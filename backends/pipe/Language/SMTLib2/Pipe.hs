module Language.SMTLib2.Pipe where

import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type hiding (Constr,Field,Datatype)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Type.Nat as Type
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Expression hiding (Fun,Field,Var,QVar,LVar)
import qualified Language.SMTLib2.Internals.Expression as Expr
import Language.SMTLib2.Strategy as Strat

import qualified Data.Text as T
import qualified Data.Text.Read as T
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Proxy
import Data.Constraint
import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show

import System.Process
import System.IO
import qualified Data.ByteString as BS hiding (reverse)
import qualified Data.ByteString.Char8 as BS8
import Blaze.ByteString.Builder
import Data.Attoparsec

import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Ratio

import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Identity
import Control.Monad.Trans.Except

data PipeDatatype = forall a. IsDatatype a => PipeDatatype (Proxy a)

data SMTPipe = SMTPipe { channelIn :: Handle
                       , channelOut :: Handle
                       , processHandle :: ProcessHandle
                       , names :: Map String Int
                       , vars :: Map T.Text RevVar
                       , datatypes :: Map T.Text PipeDatatype
                       , interpolationMode :: InterpolationMode }
             deriving Typeable

data RevVar = forall (t::Type). Var !(Repr t)
            | forall (t::Type). QVar !(Repr t)
            | forall (arg::[Type]) (t::Type). Fun !(List Repr arg) !(Repr t)
            | forall (arg::[Type]) (dt :: *). (IsDatatype dt) => Constr !(List Repr arg) !(Proxy dt)
            | forall (dt :: *) (res :: Type). (IsDatatype dt) => Field !(Proxy dt) !(Repr res)
            | forall (t::Type). FunArg !(Repr t)
            | forall (t::Type). LVar !(Repr t)
            | forall (dt :: *). IsDatatype dt => Datatype !(Proxy dt)

data InterpolationMode = Z3Interpolation [T.Text] [T.Text]
                       | MathSATInterpolation

newtype PipeExpr (t :: Type) = PipeExpr (Expression PipeVar PipeVar PipeFun PipeConstr PipeField PipeVar PipeVar PipeExpr t) deriving Show
type PipeVar = UntypedVar T.Text
type PipeFun = UntypedFun T.Text
type PipeConstr = UntypedCon T.Text
type PipeField = UntypedField T.Text

newtype PipeClauseId = PipeClauseId T.Text deriving (Show,Eq,Ord)

instance GEq PipeExpr where
  geq (PipeExpr e1) (PipeExpr e2) = geq e1 e2

instance GCompare PipeExpr where
  gcompare (PipeExpr e1) (PipeExpr e2) = gcompare e1 e2

instance GShow PipeExpr where
  gshowsPrec = showsPrec

instance GetType PipeExpr where
  getType (PipeExpr e) = getType e

instance Backend SMTPipe where
  type SMTMonad SMTPipe = IO
  type Expr SMTPipe = PipeExpr
  type Var SMTPipe = PipeVar
  type QVar SMTPipe = PipeVar
  type Fun SMTPipe = PipeFun
  type Constr SMTPipe = PipeConstr
  type Field SMTPipe = PipeField
  type FunArg SMTPipe = PipeVar
  type LVar SMTPipe = PipeVar
  type ClauseId SMTPipe = PipeClauseId
  type Model SMTPipe = AssignmentModel SMTPipe
  setOption opt b = do
    putRequest b $ renderSetOption opt
    return ((),b)
  getInfo info b = do
    putRequest b (renderGetInfo info)
    resp <- parseResponse b
    case info of
      SMTSolverName -> case resp of
        L.List [L.Symbol ":name",L.String name] -> return (T.unpack name,b)
        _ -> error $ "Invalid response to 'get-info' query: "++show resp
      SMTSolverVersion -> case resp of
        L.List [L.Symbol ":version",L.String name] -> return (T.unpack name,b)
        _ -> error $ "Invalid response to 'get-info' query: "++show resp
  declareVar tp name b = do
    let (sym,req,nnames) = renderDeclareVar (names b) tp name
        nb = b { names = nnames
               , vars = Map.insert sym (Var tp) (vars b) }
    putRequest nb req
    return (UntypedVar sym tp,nb)
  createQVar tp name b = do
    let name' = case name of
          Just n -> n
          Nothing -> "qv"
        (name'',nb) = genName b name'
    return (UntypedVar name'' tp,nb { vars = Map.insert name'' (QVar tp) (vars nb) })
  createFunArg tp name b = do
    let name' = case name of
          Just n -> n
          Nothing -> "fv"
        (name'',nb) = genName b name'
    return (UntypedVar name'' tp,nb { vars = Map.insert name'' (FunArg tp) (vars nb) })
  defineVar name (PipeExpr expr) b = do
    let tp = getType expr
        (sym,req,nnames) = renderDefineVar (names b) tp name (exprToLisp expr)
        nb = b { names = nnames
               , vars = Map.insert sym (Var tp) (vars b) }
    putRequest nb req
    return (UntypedVar sym tp,nb)
  declareFun arg res name b = do
    let (sym,req,nnames) = renderDeclareFun (names b) arg res name
        nb = b { names = nnames
               , vars = Map.insert sym (Fun arg res) (vars b) }
    putRequest nb req
    return (UntypedFun sym arg res,nb)
  defineFun name arg body b = do
    let argTp = runIdentity $ List.mapM (return . getType) arg
        bodyTp = getType body
        (name',req,nnames) = renderDefineFun (\(UntypedVar n _) -> L.Symbol n)
                             (\(PipeExpr e) -> exprToLisp e) (names b) name arg body
        nb = b { names = nnames }
    putRequest nb req
    return (UntypedFun name' argTp bodyTp,nb)
  assert (PipeExpr expr) b = do
    putRequest b (L.List [L.Symbol "assert"
                         ,exprToLisp expr])
    return ((),b)
  assertId (PipeExpr expr) b = do
    let (name,b1) = genName b "cl"
    putRequest b1 (L.List [L.Symbol "assert"
                          ,L.List [L.Symbol "!"
                                  ,exprToLisp expr
                                  ,L.Symbol ":named"
                                  ,L.Symbol name]])
    return (PipeClauseId name,b1)
  assertPartition (PipeExpr expr) part b = case interpolationMode b of
    Z3Interpolation grpA grpB -> do
      let (name,b1) = genName b "grp"
      putRequest b1 (L.List [L.Symbol "assert"
                          ,L.List [L.Symbol "!"
                                  ,exprToLisp expr
                                  ,L.Symbol ":named"
                                  ,L.Symbol name]])
      return ((),b1 { interpolationMode = case part of
                      PartitionA -> Z3Interpolation (name:grpA) grpB
                      PartitionB -> Z3Interpolation grpA (name:grpB) })
    MathSATInterpolation -> do
      putRequest b (L.List [L.Symbol "assert"
                           ,L.List [L.Symbol "!"
                                  ,exprToLisp expr
                                  ,L.Symbol ":interpolation-group"
                                  ,L.Symbol (case part of
                                               PartitionA -> "partA"
                                               PartitionB -> "partB")]])
      return ((),b)
  getUnsatCore b = do
    putRequest b (L.List [L.Symbol "get-unsat-core"])
    resp <- parseResponse b
    case resp of
      L.List names -> do
        cids <- mapM (\name -> case name of
                        L.Symbol name' -> return $ PipeClauseId name'
                        _ -> error $ "smtlib2: Invalid clause when getting unsatisfiable core: "++show name
                     ) names
        return (cids,b)
      _ -> error $ "smtlib2: Invalid response to query for unsatisfiable core: "++show resp
  checkSat tactic limits b = do
    putRequest b $ renderCheckSat tactic limits
    res <- BS.hGetLine (channelOut b)
    return (case res of
              "sat" -> Sat
              "sat\r" -> Sat
              "unsat" -> Unsat
              "unsat\r" -> Unsat
              "unknown" -> Unknown
              "unknown\r" -> Unknown
              _ -> error $ "smtlib2: unknown check-sat response: "++show res,b)
  getValue expr b = do
    putRequest b (renderGetValue b expr)
    l <- parseResponse b
    return (parseGetValue b (getType expr) l,b)
  getProof b = do
    putRequest b renderGetProof
    l <- parseResponse b
    return (parseGetProof b l,b)
  push b = do
    putRequest b (L.List [L.Symbol "push",L.Number $ L.I 1])
    return ((),b)
  pop b = do
    putRequest b (L.List [L.Symbol "pop",L.Number $ L.I 1])
    return ((),b)
  getModel b = do
    putRequest b (L.List [L.Symbol "get-model"])
    mdl <- parseResponse b
    case runExcept $ parseGetModel b mdl of
      Right mdl' -> return (mdl',b)
      Left err -> error $ "smtlib2: Unknown get-model response: "++err
  simplify (PipeExpr expr) b = do
    putRequest b (L.List [L.Symbol "simplify"
                         ,exprToLisp expr])
    resp <- parseResponse b
    case runExcept $ lispToExprTyped b (getType expr) resp of
      Right res -> return (res,b)
      Left err -> error $ "smtlib2: Unknown simplify response: "++show resp++" ["++err++"]"
  toBackend expr b = return (PipeExpr expr,b)
  fromBackend b (PipeExpr expr) = expr
  interpolate b = do
    case interpolationMode b of
      Z3Interpolation grpA grpB -> do
        putRequest b (L.List [L.Symbol "get-interpolant",getAnd grpA,getAnd grpB])
      MathSATInterpolation -> do
        putRequest b (L.List [L.Symbol "get-interpolant",L.List [L.Symbol "partA"]])
    resp <- parseResponse b
    case runExcept $ lispToExprTyped b BoolRepr resp of
      Right res -> return (res,b)
      Left err -> error $ "smtlib2: Unknown get-interpolant response: "++show resp++" ["++err++"]"
    where
      getAnd [] = L.Symbol "true"
      getAnd [x] = L.Symbol x
      getAnd xs = L.List $ (L.Symbol "and"):fmap L.Symbol xs
  declareDatatypes coll b = do
    putRequest b (renderDeclareDatatype coll)
    return (mkTypes b coll)
    where
      mkTypes :: SMTPipe -> TypeCollection sigs
              -> (BackendTypeCollection PipeConstr PipeField sigs,SMTPipe)
      mkTypes b NoDts = (NoDts,b)
      mkTypes b (ConsDts (dt::Type.Datatype '(DatatypeSig dt,dt)) dts)
        = let (dt',b1) = mkCons b (constructors dt)
              b2 = b1 { vars = Map.insert (T.pack $ datatypeName dt)
                                          (Datatype (Proxy::Proxy dt))
                                          (vars b1) }
              (dts',b3) = mkTypes b2 dts
          in (ConsDts (BackendDatatype dt') dts',b3)

      mkCons :: IsDatatype dt => SMTPipe -> Constrs Type.Constr sig dt
             -> (Constrs (BackendConstr PipeConstr PipeField) sig dt,SMTPipe)
      mkCons b NoCon = (NoCon,b)
      mkCons b (ConsCon (con :: Type.Constr '(arg,tp)) cons)
        = let arg = runIdentity $ List.mapM (return . fieldType) (conFields con)
              (fields,b1) = mkFields b (conFields con)
              b2 = b1 { vars = Map.insert (T.pack $ conName con)
                                          (Constr arg (Proxy::Proxy tp))
                                          (vars b1) }
              (cons',b3) = mkCons b2 cons
          in (ConsCon (BackendConstr (conName con)
                                     (UntypedCon (T.pack $ conName con)
                                      (runIdentity $ List.mapM (return . fieldType) (conFields con))
                                      Proxy)
                                     fields
                                     (construct con)
                                     (conTest con))
                      cons',b3)

      mkFields :: IsDatatype dt => SMTPipe -> List (Type.Field dt) arg
               -> (List (BackendField PipeField dt) arg,SMTPipe)
      mkFields b Nil = (Nil,b)
      mkFields b (Cons (f::Type.Field dt t) fs)
        = let b1 = b { vars = Map.insert (T.pack $ fieldName f)
                                         (Field (Proxy::Proxy dt) (fieldType f))
                                         (vars b) }
              (fs',b2) = mkFields b1 fs
          in (Cons (BackendField (fieldName f)
                                (UntypedField (T.pack $ fieldName f) Proxy (fieldType f))
                                (fieldType f)
                                (fieldGet f))
                  fs',b2)
  exit b = do
    putRequest b (L.List [L.Symbol "exit"])
    hClose (channelIn b)
    hClose (channelOut b)
    terminateProcess (processHandle b)
    _ <- waitForProcess (processHandle b)
    return ((),b)

renderDeclareFun :: Map String Int -> List Repr arg -> Repr ret -> Maybe String
                 -> (T.Text,L.Lisp,Map String Int)
renderDeclareFun names args ret name
  = (name'',L.List [L.Symbol "declare-fun"
                   ,L.Symbol name''
                   ,typeList args
                   ,typeSymbol ret],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "fun"
    (name'',nnames) = genName' names name'

renderDefineFun :: (GetType e,GetType fv)
                => (forall t. fv t -> L.Lisp)
                -> (forall t. e t -> L.Lisp)
                -> Map String Int -> Maybe String
                -> List fv arg
                -> e ret
                -> (T.Text,L.Lisp,Map String Int)
renderDefineFun renderFV renderE names name args body
  = (name'',L.List [L.Symbol "define-fun"
                   ,L.Symbol name''
                   ,L.List $ mkList renderFV args
                   ,typeSymbol (getType body)
                   ,renderE body],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "fun"
    (name'',nnames) = genName' names name'
    mkList :: GetType fv => (forall t. fv t -> L.Lisp) -> List fv ts -> [L.Lisp]
    mkList _ Nil = []
    mkList renderFV (Cons v xs)
      = (L.List [renderFV v,typeSymbol (getType v)]):
        mkList renderFV xs

renderCheckSat :: Maybe Tactic -> CheckSatLimits -> L.Lisp
renderCheckSat tactic limits
  = L.List (if extendedCheckSat
            then [L.Symbol "check-sat-using"
                 ,case tactic of
                    Just t -> tacticToLisp t
                    Nothing -> L.Symbol "smt"]++
                      (case limitTime limits of
                         Just t -> [L.Symbol ":timeout"
                                   ,L.Number (L.I t)]
                         Nothing -> [])++
                      (case limitMemory limits of
                         Just m -> [L.Symbol ":max-memory"
                                   ,L.Number (L.I m)]
                         Nothing -> [])
            else [L.Symbol "check-sat"])
  where
    extendedCheckSat = case tactic of
      Just _ -> True
      _ -> case limitTime limits of
        Just _ -> True
        _ -> case limitMemory limits of
          Just _ -> True
          _ -> False

renderDeclareDatatype :: TypeCollection sigs -> L.Lisp
renderDeclareDatatype coll
  = L.List [L.Symbol "declare-datatypes"
           ,L.Symbol "()"
           ,L.List (mkTypes coll)]
  where
    mkTypes :: TypeCollection sigs -> [L.Lisp]
    mkTypes NoDts = []
    mkTypes (ConsDts dt dts) = mkType dt : mkTypes dts

    mkType :: Type.Datatype '(cons,dt) -> L.Lisp
    mkType dt = L.List $ (L.Symbol $ T.pack $ datatypeName dt) :
                         mkCons (constructors dt)

    mkCons :: Constrs Type.Constr sig dt -> [L.Lisp]
    mkCons NoCon = []
    mkCons (ConsCon con cons) = mkCon con : mkCons cons

    mkCon :: Type.Constr '(arg,dt) -> L.Lisp
    mkCon con = L.List $ (L.Symbol $ T.pack $ conName con) :
                         mkFields (conFields con)

    mkFields :: List (Type.Field dt) arg -> [L.Lisp]
    mkFields Nil = []
    mkFields (Cons f fs) = mkField f : mkFields fs

    mkField :: Type.Field dt t -> L.Lisp
    mkField f = L.List [L.Symbol $ T.pack $ fieldName f
                       ,typeSymbol (fieldType f)]
      
renderSetOption :: SMTOption -> L.Lisp
renderSetOption (SMTLogic name) = L.List [L.Symbol "set-logic",L.Symbol $ T.pack name]
renderSetOption opt
  = L.List $ [L.Symbol "set-option"]++
    (case opt of
        PrintSuccess v -> [L.Symbol ":print-success"
                          ,L.Symbol $ if v then "true" else "false"]
        ProduceModels v -> [L.Symbol ":produce-models"
                           ,L.Symbol $ if v then "true" else "false"]
        B.ProduceProofs v -> [L.Symbol ":produce-proofs"
                             ,L.Symbol $ if v then "true" else "false"]
        B.ProduceUnsatCores v -> [L.Symbol ":produce-unsat-cores"
                                 ,L.Symbol $ if v then "true" else "false"]
        ProduceInterpolants v -> [L.Symbol ":produce-interpolants"
                                 ,L.Symbol $ if v then "true" else "false"])

renderGetInfo :: SMTInfo i -> L.Lisp
renderGetInfo SMTSolverName
  = L.List [L.Symbol "get-info"
           ,L.Symbol ":name"]
renderGetInfo SMTSolverVersion
  = L.List [L.Symbol "get-info"
           ,L.Symbol ":version"]

renderDeclareVar :: Map String Int -> Repr tp -> Maybe String
                 -> (T.Text,L.Lisp,Map String Int)
renderDeclareVar names tp name
  = (name'',L.List [L.Symbol "declare-fun"
                   ,L.Symbol name''
                   ,L.Symbol "()"
                   ,typeSymbol tp
                   ],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "var"
    (name'',nnames) = genName' names name'

renderDefineVar :: Map String Int -> Repr t -> Maybe String -> L.Lisp
                -> (T.Text,L.Lisp,Map String Int)
renderDefineVar names tp name lexpr
  = (name'',
     L.List [L.Symbol "define-fun"
            ,L.Symbol name''
            ,L.Symbol "()"
            ,typeSymbol tp
            ,lexpr],
     nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "var"
    (name'',nnames) = genName' names name'

renderGetValue :: SMTPipe -> PipeExpr t -> L.Lisp
renderGetValue b (PipeExpr e) = L.List [L.Symbol "get-value"
                                       ,L.List [exprToLisp e]]

parseGetValue :: SMTPipe -> Repr t -> L.Lisp -> Value PipeConstr t
parseGetValue b repr (L.List [L.List [_,val]]) = case runExcept $ lispToValue b val of
  Right (AnyValue v) -> case geq repr (valueType v) of
    Just Refl -> v
    Nothing -> error $ "smtlib2: Wrong type of returned value."
  Left err -> error $ "smtlib2: Failed to parse get-value entry: "++show val++" ["++err++"]"
parseGetValue _ _ expr = error $ "smtlib2: Failed to parse get-value result: "++show expr

renderGetProof :: L.Lisp
renderGetProof = L.List [L.Symbol "get-proof"]

parseGetProof :: SMTPipe -> L.Lisp -> PipeExpr BoolType
parseGetProof b resp = case runExcept $ lispToExprTyped b BoolRepr proof of
  Right res -> res
  Left err -> error $ "smtlib2: Failed to parse proof: "++show resp++" ["++err++"]"
  where
    proof = case resp of
      L.List items -> case findProof items of
        Nothing -> resp
        Just p -> p
      _ -> resp
    findProof [] = Nothing
    findProof ((L.List [L.Symbol "proof",p]):_) = Just p
    findProof (x:xs) = findProof xs

parseGetModel :: SMTPipe -> L.Lisp -> LispParse (Model SMTPipe)
parseGetModel b (L.List ((L.Symbol "model"):mdl)) = do
  assign <- mapM parseAssignment mdl
  return $ AssignmentModel assign
  where
    parser = pipeParser b
    parseAssignment (L.List [L.Symbol "define-fun",L.Symbol fname,L.List args,rtp,body])
      = case args of
        [] -> do
          srt@(Sort tp) <- lispToSort parser rtp
          expr <- lispToExprTyped b tp body
          return $ VarAssignment (UntypedVar fname tp) expr
        _ -> do
          srt@(Sort tp) <- lispToSort parser rtp
          withFunList b args $
            \b' tps args' -> do
              body' <- lispToExprTyped b' tp body
              return $ FunAssignment (UntypedFun fname tps tp) args' body'
    parseAssignment lsp = throwE $ "Invalid model entry: "++show lsp
    withFunList :: SMTPipe -> [L.Lisp]
                -> (forall arg. SMTPipe -> List Repr arg -> List PipeVar arg -> LispParse a) -> LispParse a
    withFunList b [] f = f b Nil Nil
    withFunList b ((L.List [L.Symbol v,tp]):ls) f = do
      Sort tp <- lispToSort parser tp
      withFunList (b { vars = Map.insert v (FunArg tp) (vars b) }) ls $
        \b' tps args -> f b' (Cons tp tps) (Cons (UntypedVar v tp) args)
    withFunList _ lsp _ = throwE $ "Invalid fun args: "++show lsp
parseGetModel _ lsp = throwE $ "Invalid model: "++show lsp

data Sort = forall (t :: Type). Sort (Repr t)
data Sorts = forall (t :: [Type]). Sorts (List Repr t)

data ParsedFunction fun con field
  = ParsedFunction { argumentTypeRequired :: Integer -> Bool
                   , getParsedFunction :: [Maybe Sort] -> LispParse (AnyFunction fun con field)
                   }

data AnyExpr e = forall (t :: Type). AnyExpr (e t)

instance GShow e => Show (AnyExpr e) where
  showsPrec p (AnyExpr x) = gshowsPrec p x

data LispParser (v :: Type -> *) (qv :: Type -> *) (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) (fv :: Type -> *) (lv :: Type -> *) (e :: Type -> *)
  = LispParser { parseFunction :: forall a. Maybe Sort -> T.Text
                               -> (forall args res. fun '(args,res) -> a)
                               -> (forall args res. (IsDatatype res) => con '(args,res) -> a) -- constructor
                               -> (forall args res. (IsDatatype res) => con '(args,res) -> a) -- constructor test
                               -> (forall t res. (IsDatatype t) => field '(t,res) -> a)
                               -> LispParse a
               , parseDatatype :: forall a. T.Text
                               -> (forall t. IsDatatype t => Proxy t -> a)
                               -> LispParse a
               , parseVar :: forall a. Maybe Sort -> T.Text
                          -> (forall t. v t -> LispParse a)
                          -> (forall t. qv t -> LispParse a)
                          -> (forall t. fv t -> LispParse a)
                          -> (forall t. lv t -> LispParse a)
                          -> LispParse a
               , parseRecursive :: forall a. Maybe Sort -> L.Lisp
                                -> (forall t. e t -> LispParse a)
                                -> LispParse a
               , registerQVar :: forall (t :: Type). T.Text -> Repr t
                              -> (qv t,LispParser v qv fun con field fv lv e)
               , registerLetVar :: forall (t :: Type). T.Text -> Repr t
                                -> (lv t,LispParser v qv fun con field fv lv e)
               }

type LispParse = Except String

-- | Spawn a new SMT solver process and create a pipe to communicate with it.
createPipe :: String -- ^ Path to the binary of the SMT solver
         -> [String] -- ^ Command line arguments to be passed to the SMT solver
         -> IO SMTPipe
createPipe solver args = do
  let cmd = CreateProcess { cmdspec = RawCommand solver args
                          , cwd = Nothing
                          , env = Nothing
                          , std_in = CreatePipe
                          , std_out = CreatePipe
                          , std_err = Inherit
                          , close_fds = False
                          , create_group = True
#if MIN_VERSION_process(1,2,0)
                          , delegate_ctlc = False
#endif
                          }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  let p0 = SMTPipe { channelIn = hin
                   , channelOut = hout
                   , processHandle = handle
                   , names = Map.empty
                   , vars = Map.empty
                   , datatypes = Map.empty
                   , interpolationMode = MathSATInterpolation }
  putRequest p0 (L.List [L.Symbol "get-info"
                        ,L.Symbol ":name"])
  resp <- parseResponse p0
  case resp of
    L.List [L.Symbol ":name",L.String name] -> case name of
      "Z3" -> return $ p0 { interpolationMode = Z3Interpolation [] [] }
      _ -> return p0
    _ -> return p0

lispToExprUntyped :: SMTPipe -> L.Lisp
                  -> (forall (t::Type). PipeExpr t -> LispParse a)
                  -> LispParse a
lispToExprUntyped st l res = lispToExprWith (pipeParser st) Nothing l $
                             \e -> res (PipeExpr e)

lispToExprTyped :: SMTPipe -> Repr t -> L.Lisp -> LispParse (PipeExpr t)
lispToExprTyped st tp l = lispToExprWith (pipeParser st) (Just (Sort tp)) l $
                          \e -> case geq tp (getType e) of
                          Just Refl -> return (PipeExpr e)
                          Nothing -> throwE $ show l++" has type "++show (getType e)++", but "++show tp++" was expected."

pipeParser :: SMTPipe
           -> LispParser PipeVar PipeVar PipeFun PipeConstr PipeField PipeVar PipeVar PipeExpr
pipeParser st = parse
  where
  parse = LispParser { parseFunction = \srt name fun con test field
                                       -> case T.stripPrefix "is-" name of
                                       Just con -> case Map.lookup name (vars st) of
                                         Just (Constr arg dt)
                                           -> return $ test (UntypedCon name arg dt)
                                         _ -> throwE $ "Unknown constructor: "++show name
                                       Nothing -> case Map.lookup name (vars st) of
                                         Just (Fun arg tp)
                                           -> return $ fun (UntypedFun name arg tp)
                                         Just (Constr arg dt)
                                           -> return $ con (UntypedCon name arg dt)
                                         Just (Field dt tp)
                                           -> return $ field (UntypedField name dt tp)
                                         _ -> throwE $ "Unknown symbol "++show name
                     , parseDatatype = \name res -> case Map.lookup name (datatypes st) of
                                         Just (PipeDatatype p) -> return $ res p
                                         _ -> throwE $ "Unknown datatype "++show name
                     , parseVar = \srt name v qv fv lv -> case Map.lookup name (vars st) of
                                    Just (Var tp)
                                      -> v (UntypedVar name tp)
                                    Just (QVar tp)
                                      -> qv (UntypedVar name tp)
                                    Just (FunArg tp)
                                      -> fv (UntypedVar name tp)
                                    Just (LVar tp)
                                      -> lv (UntypedVar name tp)
                                    _ -> throwE $ "Unknown variable "++show name
                     , parseRecursive = \srt l res -> lispToExprWith parse srt l $
                                                      \e -> res (PipeExpr e)
                     , registerQVar = \name tp
                                      -> (UntypedVar name tp,
                                          pipeParser (st { vars = Map.insert name (QVar tp)
                                                                  (vars st) }))
                     , registerLetVar = \name tp
                                        -> (UntypedVar name tp,
                                            pipeParser (st { vars = Map.insert name (LVar tp)
                                                                    (vars st) }))
                     }

lispToExprWith :: (GShow fun,GShow con,GShow field,GShow e,
                   GetFunType fun,GetConType con,GetFieldType field,GetType e)
               => LispParser v qv fun con field fv lv e
               -> Maybe Sort
               -> L.Lisp
               -> (forall (t :: Type).
                   Expression v qv fun con field fv lv e t
                   -> LispParse a)
               -> LispParse a
lispToExprWith p hint (runExcept . lispToConstant -> Right (AnyValue val)) res
  = res (Const val)
lispToExprWith p hint (L.Symbol sym) res
  = parseVar p hint sym (res . Expr.Var) (res . Expr.QVar) (res . Expr.FVar) (res . Expr.LVar)
lispToExprWith p hint (L.List [L.Symbol "_",L.Symbol "as-array",fsym]) res = do
  parsed <- lispToFunction p el_hint fsym
  AnyFunction fun <- getParsedFunction parsed idx_hint
  res (AsArray fun)
  where
    (idx_hint,el_hint) = case hint of
      Nothing -> ([],Nothing)
      Just (Sort tp) -> case tp of
        ArrayRepr args el
          -> (runIdentity $ List.toList (\t -> return (Just $ Sort t)) args,
              Just $ Sort el)
lispToExprWith p hint (L.List [L.Symbol "forall",L.List args,body]) res
  = mkQuant p args $
    \np args' -> parseRecursive np (Just (Sort BoolRepr)) body $
                 \body' -> case getType body' of
                 BoolRepr -> res (Quantification Forall args' body')
lispToExprWith p hint (L.List [L.Symbol "exists",L.List args,body]) res
  = mkQuant p args $
    \np args' -> parseRecursive np (Just (Sort BoolRepr)) body $
                 \body' -> case getType body' of
                 BoolRepr -> res (Quantification Exists args' body')
lispToExprWith p hint (L.List [L.Symbol "let",L.List args,body]) res
  = mkLet p args $
    \np args' -> parseRecursive np hint body $
                 \body' -> res (Let args' body')
lispToExprWith p hint (L.List (fun:args)) res = do
  parsed <- lispToFunction p hint fun
  args' <- matchList (argumentTypeRequired parsed) 0 args
  let hints = fmap (\arg -> case arg of
                      Left _ -> Nothing
                      Right (AnyExpr e) -> Just $ Sort (getType e)
                   ) args'
  AnyFunction fun' <- getParsedFunction parsed hints
  let (argTps,ret) = getFunType fun'
  args'' <- catchE (makeList p argTps args') $
            \err -> throwE $ "While parsing arguments of function: "++
                    show fun'++": "++err
  res $ App fun' args''
  where
    matchList _ _ [] = return []
    matchList f i (e:es) = if f i
                           then parseRecursive p Nothing e
                                (\e' -> do
                                     rest <- matchList f (i+1) es
                                     return $ (Right (AnyExpr e')):rest)
                           else do
                             rest <- matchList f (i+1) es
                             return $ (Left e):rest
    makeList :: (GShow e,GetType e) => LispParser v qv fun con field fv lv e
             -> List Repr arg -> [Either L.Lisp (AnyExpr e)] -> LispParse (List e arg)
    makeList _ Nil [] = return Nil
    makeList _ Nil _  = throwE $ "Too many arguments to function."
    makeList p (Cons tp args) (e:es) = case e of
      Right (AnyExpr e') -> do
        r <- case geq tp (getType e') of
           Just Refl -> return e'
           Nothing -> throwE $ "Argument "++gshowsPrec 11 e' ""++" has wrong type."
        rs <- makeList p args es
        return (Cons r rs)
      Left l -> parseRecursive p (Just $ Sort tp) l $
                \e' -> do
                  r <- case geq tp (getType e') of
                     Just Refl -> return e'
                     Nothing -> throwE $ "Argument "++gshowsPrec 11 e' ""++" has wrong type."
                  rs <- makeList p args es
                  return (Cons r rs)
    makeList _ (Cons _ _) [] = throwE $ "Not enough arguments to function."
lispToExprWith _ _ lsp _ = throwE $ "Invalid SMT expression: "++show lsp

mkQuant :: LispParser v qv fun con field fv lv e -> [L.Lisp]
        -> (forall arg. LispParser v qv fun con field fv lv e -> List qv arg -> LispParse a)
        -> LispParse a
mkQuant p [] f = f p Nil
mkQuant p ((L.List [L.Symbol name,sort]):args) f = do
  Sort srt <- lispToSort p sort
  let (qvar,np) = registerQVar p name srt
  mkQuant np args $ \p args -> f p (Cons qvar args)
mkQuant _ lsp _ = throwE $ "Invalid forall/exists parameter: "++show lsp

mkLet :: GetType e
      => LispParser v qv fun con field fv lv e -> [L.Lisp]
         -> (forall arg. LispParser v qv fun con field fv lv e
             -> List (LetBinding lv e) arg -> LispParse a)
         -> LispParse a
mkLet p [] f = f p Nil
mkLet p ((L.List [L.Symbol name,expr]):args) f
  = parseRecursive p Nothing expr $
    \expr' -> do
      let (lvar,np) = registerLetVar p name (getType expr')
      mkLet np args $ \p args -> f p (Cons (LetBinding lvar expr') args)
mkLet _ lsp _ = throwE $ "Invalid let parameter: "++show lsp

withEq :: Repr t -> [b]
       -> (forall n. Natural n -> List Repr (AllEq t n) -> a)
       -> a
withEq tp [] f = f Zero Nil
withEq tp (_:xs) f = withEq tp xs $
                     \n args -> f (Succ n) (Cons tp args)
                                             
lispToFunction :: LispParser v qv fun con field fv lv e
               -> Maybe Sort -> L.Lisp -> LispParse (ParsedFunction fun con field)
lispToFunction _ _ (L.Symbol "=")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort tp):_ -> withEq tp args $
                           \n args
                           -> return $ AnyFunction (Eq tp n)
       _ -> throwE $ "Cannot derive type of = parameters.")
lispToFunction _ _ (L.Symbol "distinct")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort tp):_ -> withEq tp args $
                           \n args' -> return $ AnyFunction (Distinct tp n)
       _ -> throwE $ "Cannot derive type of \"distinct\" parameters.")
lispToFunction rf sort (L.List [L.Symbol "_",L.Symbol "map",sym]) = do
  f <- lispToFunction rf sort' sym
  let reqList 0 = case idx' of
        Nothing -> True
        Just _ -> argumentTypeRequired f 0
      reqList n = argumentTypeRequired f n
      fun args = do
        Sorts pidx <- case idx' of
          Just srts -> return srts
          Nothing -> case args of
            Just srt:_ -> case asArraySort srt of
              Just (idx,_) -> return idx
              Nothing -> throwE $ "Could not derive type of the array index in map function."
            _ -> throwE $ "Could not derive type of the array index in map function."
        argSorts <- mapM (\prx -> case prx of
                            Nothing -> return Nothing
                            Just srt -> do
                              (_,elsrt) <- case asArraySort srt of
                                Just srt' -> return srt'
                                Nothing -> throwE $ "Argument to map function isn't an array."
                              return (Just elsrt)
                         ) args
        fun' <- getParsedFunction f argSorts
        return $ mkMap pidx fun'
  return (ParsedFunction reqList fun)
  where
    (sort',idx') = case sort of
      Just (Sort tp) -> case tp of
        ArrayRepr idx el
          -> (Just (Sort el),
              Just (Sorts idx))
        _ -> (Nothing,Nothing)
      _ -> (Nothing,Nothing)
lispToFunction _ _ (L.Symbol ">=") = lispToOrdFunction Ge
lispToFunction _ _ (L.Symbol ">") = lispToOrdFunction Gt
lispToFunction _ _ (L.Symbol "<=") = lispToOrdFunction Le
lispToFunction _ _ (L.Symbol "<") = lispToOrdFunction Lt
lispToFunction _ sort (L.Symbol "+") = lispToArithFunction sort Plus
lispToFunction _ sort (L.Symbol "*") = lispToArithFunction sort Mult
lispToFunction _ sort (L.Symbol "-") = lispToArithFunction sort Minus
lispToFunction _ _ (L.Symbol "div") = return $ ParsedFunction (const False)
                                      (\_ -> return $ AnyFunction (ArithIntBin Div))
lispToFunction _ _ (L.Symbol "mod") = return $ ParsedFunction (const False)
                                      (\_ -> return $ AnyFunction (ArithIntBin Mod))
lispToFunction _ _ (L.Symbol "rem") = return $ ParsedFunction (const False)
                                      (\_ -> return $ AnyFunction (ArithIntBin Rem))
lispToFunction _ _ (L.Symbol "/") = return $ ParsedFunction (const False)
                                    (\_ -> return $ AnyFunction Divide)
lispToFunction _ sort (L.Symbol "abs") = case sort of
  Just (Sort tp) -> case tp of
    IntRepr -> return $ ParsedFunction (const False) (\_ -> return $ AnyFunction (Abs NumInt))
    RealRepr -> return $ ParsedFunction (const False) (\_ -> return $ AnyFunction (Abs NumReal))
    exp -> throwE $ "abs function can't have type "++show exp
  Nothing -> return $ ParsedFunction (==0) $
             \args -> case args of
                [Just (Sort tp)] -> case tp of
                  IntRepr -> return $ AnyFunction (Abs NumInt)
                  RealRepr -> return $ AnyFunction (Abs NumReal)
                  srt -> throwE $ "abs can't take argument of type "++show srt
                _ -> throwE $ "abs function takes exactly one argument."
lispToFunction _ _ (L.Symbol "not")
  = return $ ParsedFunction (const False) (\_ -> return $ AnyFunction Not)
lispToFunction _ _ (L.Symbol "and") = return $ lispToLogicFunction And
lispToFunction _ _ (L.Symbol "or") = return $ lispToLogicFunction Or
lispToFunction _ _ (L.Symbol "xor") = return $ lispToLogicFunction XOr
lispToFunction _ _ (L.Symbol "=>") = return $ lispToLogicFunction Implies
lispToFunction _ _ (L.Symbol "to-real")
  = return $ ParsedFunction (const False) (\_ -> return $ AnyFunction ToReal)
lispToFunction _ _ (L.Symbol "to-int")
  = return$ ParsedFunction (const False) (\_ -> return $ AnyFunction ToInt)
lispToFunction _ sort (L.Symbol "ite") = case sort of
  Just (Sort tp)
    -> return $ ParsedFunction (const False)
       (\_ -> return $ AnyFunction (ITE tp))
  Nothing -> return $ ParsedFunction (==1) $
             \args -> case args of
               [_,Just (Sort tp),_]
                 -> return $ AnyFunction (ITE tp)
               _ -> throwE $ "Invalid arguments to ite function."
lispToFunction _ _ (L.Symbol "bvule") = return $ lispToBVCompFunction BVULE
lispToFunction _ _ (L.Symbol "bvult") = return $ lispToBVCompFunction BVULT
lispToFunction _ _ (L.Symbol "bvuge") = return $ lispToBVCompFunction BVUGE
lispToFunction _ _ (L.Symbol "bvugt") = return $ lispToBVCompFunction BVUGT
lispToFunction _ _ (L.Symbol "bvsle") = return $ lispToBVCompFunction BVSLE
lispToFunction _ _ (L.Symbol "bvslt") = return $ lispToBVCompFunction BVSLT
lispToFunction _ _ (L.Symbol "bvsge") = return $ lispToBVCompFunction BVSGE
lispToFunction _ _ (L.Symbol "bvsgt") = return $ lispToBVCompFunction BVSGT
lispToFunction _ sort (L.Symbol "bvadd") = lispToBVBinFunction sort BVAdd
lispToFunction _ sort (L.Symbol "bvsub") = lispToBVBinFunction sort BVSub
lispToFunction _ sort (L.Symbol "bvmul") = lispToBVBinFunction sort BVMul
lispToFunction _ sort (L.Symbol "bvurem") = lispToBVBinFunction sort BVURem
lispToFunction _ sort (L.Symbol "bvsrem") = lispToBVBinFunction sort BVSRem
lispToFunction _ sort (L.Symbol "bvudiv") = lispToBVBinFunction sort BVUDiv
lispToFunction _ sort (L.Symbol "bvsdiv") = lispToBVBinFunction sort BVSDiv
lispToFunction _ sort (L.Symbol "bvshl") = lispToBVBinFunction sort BVSHL
lispToFunction _ sort (L.Symbol "bvlshr") = lispToBVBinFunction sort BVLSHR
lispToFunction _ sort (L.Symbol "bvashr") = lispToBVBinFunction sort BVASHR
lispToFunction _ sort (L.Symbol "bvxor") = lispToBVBinFunction sort BVXor
lispToFunction _ sort (L.Symbol "bvand") = lispToBVBinFunction sort BVAnd
lispToFunction _ sort (L.Symbol "bvor") = lispToBVBinFunction sort BVOr
lispToFunction _ sort (L.Symbol "bvnot") = lispToBVUnFunction sort BVNot
lispToFunction _ sort (L.Symbol "bvneg") = lispToBVUnFunction sort BVNeg
lispToFunction _ _ (L.Symbol "select")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort arr):_ -> case arr of
         ArrayRepr idx el
           -> return $ AnyFunction (Select idx el)
         srt -> throwE $ "Invalid argument type to select function: "++show srt
       _ -> throwE $ "Invalid arguments to select function.")
lispToFunction _ sort (L.Symbol "store") = case sort of
  Just (Sort srt) -> case srt of
    ArrayRepr idx el
      -> return (ParsedFunction (const False)
                 (\_ -> return $ AnyFunction
                        (Store idx el)))
    srt' -> throwE $ "Invalid argument types to store function: "++show srt'
  Nothing -> return $ ParsedFunction (==0)
             (\args -> case args of
                Just (Sort arr):_ -> case arr of
                  ArrayRepr idx el
                    -> return $ AnyFunction
                       (Store idx el)
                  srt -> throwE $ "Invalid first argument type to store function: "++show srt
                _ -> throwE $ "Invalid arguments to store function.")
lispToFunction r sort (L.List [L.Symbol "as",L.Symbol "const",sig]) = do
  Sort rsig <- case sort of
    Just srt -> return srt
    Nothing -> lispToSort r sig
  case rsig of
    ArrayRepr idx el
      -> return $ ParsedFunction (const False)
         (\_ -> return $ AnyFunction (ConstArray idx el))
    _ -> throwE $ "Invalid signature for (as const ...) function."
lispToFunction _ sort (L.Symbol "concat")
  = return $ ParsedFunction (const True)
    (\args -> case args of
       [Just (Sort tp1),Just (Sort tp2)]
         -> case (tp1,tp2) of
         (BitVecRepr sz1,BitVecRepr sz2)
           -> return $ AnyFunction (Concat sz1 sz2)
         _ -> throwE $ "Invalid argument types to concat function."
       _ -> throwE $ "Wrong number of arguments to concat function.")
lispToFunction _ sort (L.List [L.Symbol "_",L.Symbol "extract",L.Number (L.I end),L.Number (L.I start)])
  = return $ ParsedFunction (==0)
    (\args -> case args of
       [Just (Sort srt)] -> case srt of
         BitVecRepr size
           -> reifyNatural start $
              \start' -> reifyNatural (end-start+1) $
                         \len' -> case naturalLEQ (naturalAdd start' len') size of
                         Just Dict -> return $ AnyFunction (Extract size start' len')
                         Nothing -> throwE $ "Invalid extract parameters."
         srt -> throwE $ "Invalid type of extract argument: "++show srt
       _ -> throwE $ "Wrong number of arguments to extract function.")
lispToFunction _ sort (L.List [L.Symbol "_",L.Symbol "divisible",L.Number (L.I div)])
  = return $ ParsedFunction (const False)
    (\_ -> return $ AnyFunction (Divisible div))
lispToFunction rf sort (L.List [sym,lispToList -> Just sig,tp]) = do
  nsort <- lispToSort rf tp
  fun <- lispToFunction rf (Just nsort) sym
  rsig <- lispToSorts rf sig $
          \sig' -> runIdentity $ List.toList (\tp -> return $ Just (Sort tp)) sig'
  return $ ParsedFunction (const False) (\_ -> getParsedFunction fun rsig)
lispToFunction rf sort (L.Symbol name)
  = parseFunction rf sort name
    (p . Expr.Fun)
    (p . Expr.Constructor)
    (p . Expr.Test)
    (p . Expr.Field)
  where
    p f = ParsedFunction (const False) (const (return $ AnyFunction f))
lispToFunction _ _ lsp = throwE $ "Unknown function: "++show lsp

lispToOrdFunction :: OrdOp -> LispParse (ParsedFunction fun con field)
lispToOrdFunction op
  = return (ParsedFunction (==0)
            (\argSrt -> case argSrt of
               (Just (Sort srt)):_ -> case srt of
                 IntRepr -> return $ AnyFunction (Ord NumInt op)
                 RealRepr -> return $ AnyFunction (Ord NumReal op)
                 srt' -> throwE $ "Invalid argument to "++show op++" function: "++show srt'
               _ -> throwE $ "Wrong number of arguments to "++show op++" function."))

lispToArithFunction :: Maybe Sort -> ArithOp -> LispParse (ParsedFunction fun con field)
lispToArithFunction sort op = case sort of
  Just (Sort tp) -> case tp of
    IntRepr -> return (ParsedFunction (const False)
                       (\args -> withEq IntRepr args $
                                 \n _ -> return $ AnyFunction (Arith NumInt op n)))
    RealRepr -> return (ParsedFunction (const False)
                        (\args -> withEq RealRepr args $
                                 \n _ -> return $ AnyFunction (Arith NumReal op n)))
    srt -> throwE $ "Invalid type of "++show op++" function: "++show srt
  Nothing -> return (ParsedFunction (==0)
                     (\argSrt -> case argSrt of
                        (Just (Sort srt)):_ -> case srt of
                           IntRepr -> withEq IntRepr argSrt $
                                      \n args
                                      -> return $ AnyFunction (Arith NumInt op n)
                           RealRepr -> withEq RealRepr argSrt $
                                       \n args
                                       -> return $ AnyFunction (Arith NumReal op n)
                           srt' -> throwE $ "Wrong argument type to "++show op++" function: "++show srt'
                        _ -> throwE $ "Wrong number of arguments to "++show op++" function."))

lispToLogicFunction :: LogicOp -> ParsedFunction fun con field
lispToLogicFunction op
  = ParsedFunction (const False)
    (\args -> withEq BoolRepr args $
       \n args
       -> return $ AnyFunction (Logic op n))

lispToBVCompFunction :: BVCompOp -> ParsedFunction fun con field
lispToBVCompFunction op
  = ParsedFunction (==0)
    (\args -> case args of
       [Just (Sort srt),_] -> case srt of
         BitVecRepr bw -> return $ AnyFunction (BVComp op bw)
         srt -> throwE $ "Invalid argument type to "++show op++" function: "++show srt
       _ -> throwE $ "Wrong number of arguments to "++show op++" function.")

lispToBVBinFunction :: Maybe Sort -> BVBinOp -> LispParse (ParsedFunction fun con field)
lispToBVBinFunction (Just (Sort srt)) op = case srt of
  BitVecRepr bw -> return $ ParsedFunction (const False) $
                   \_ -> return $ AnyFunction (BVBin op bw)
  srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
lispToBVBinFunction Nothing op
  = return $ ParsedFunction (==0) $
    \args -> case args of
      [Just (Sort srt),_] -> case srt of
        BitVecRepr bw -> return $ AnyFunction (BVBin op bw)
        srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
      _ -> throwE $ "Wrong number of arguments to "++show op++" function."

lispToBVUnFunction :: Maybe Sort -> BVUnOp -> LispParse (ParsedFunction fun con field)
lispToBVUnFunction (Just (Sort srt)) op = case srt of
  BitVecRepr bw -> return $ ParsedFunction (const False) $
                   \_ -> return $ AnyFunction (BVUn op bw)
  srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
lispToBVUnFunction Nothing op
  = return $ ParsedFunction (==0) $
    \args -> case args of
      [Just (Sort srt)] -> case srt of
        BitVecRepr bw -> return $ AnyFunction (BVUn op bw)
        srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
      _ -> throwE $ "Wrong number of arguments to "++show op++" function."

mkMap :: List Repr idx -> AnyFunction fun con field -> AnyFunction fun con field
mkMap idx (AnyFunction f) = AnyFunction (Map idx f)

asArraySort :: Sort -> Maybe (Sorts,Sort)
asArraySort (Sort tp) = case tp of
  ArrayRepr idx el
    -> return (Sorts idx,Sort el)
  _ -> Nothing

lispToList :: L.Lisp -> Maybe [L.Lisp]
lispToList (L.Symbol "()") = Just []
lispToList (L.List lst) = Just lst
lispToList _ = Nothing

lispToSort :: LispParser v qv fun con field fv lv e -> L.Lisp -> LispParse Sort
lispToSort _ (L.Symbol "Bool") = return (Sort BoolRepr)
lispToSort _ (L.Symbol "Int") = return (Sort IntRepr)
lispToSort _ (L.Symbol "Real") = return (Sort RealRepr)
lispToSort r (L.List ((L.Symbol "Array"):tps)) = do
  Sort rtp' <- lispToSort r rtp
  lispToSorts r idx (\idx' -> Sort (ArrayRepr idx' rtp'))
  where
    (idx,rtp) = splitLast tps
    splitLast [x] = ([],x)
    splitLast (x:xs) = let (xs',y') = splitLast xs
                       in (x:xs',y')
lispToSort _ (L.List [L.Symbol "_",L.Symbol "BitVec",L.Number (L.I n)])
  = reifyNatural n $ \bw -> return (Sort (BitVecRepr bw))
lispToSort r (L.Symbol name) = parseDatatype r name $
                               \pr -> Sort (DataRepr (getDatatype pr))
lispToSort _ lsp = throwE $ "Invalid SMT type: "++show lsp

lispToSorts :: LispParser v qv fun con field fv lv e -> [L.Lisp]
            -> (forall (arg :: [Type]). List Repr arg -> a)
            -> LispParse a
lispToSorts _ [] f = return (f Nil)
lispToSorts r (x:xs) f = do
  Sort tp <- lispToSort r x
  lispToSorts r xs $
    \tps -> f (Cons tp tps)

lispToValue :: SMTPipe -> L.Lisp -> LispParse (AnyValue PipeConstr)
lispToValue b l = case runExcept $ lispToConstant l of
  Right r -> return r
  Left e -> lispToConstrConstant b l

lispToConstant :: L.Lisp -> LispParse (AnyValue con)
lispToConstant (L.Symbol "true") = return (AnyValue (BoolValue True))
lispToConstant (L.Symbol "false") = return (AnyValue (BoolValue False))
lispToConstant (lispToNumber -> Just n) = return (AnyValue (IntValue n))
lispToConstant (lispToReal -> Just n) = return (AnyValue (RealValue n))
lispToConstant (lispToBitVec -> Just (val,sz))
  = reifyNatural sz $ \bw -> return (AnyValue (BitVecValue val bw))
lispToConstant l = throwE $ "Invalid constant "++show l

lispToConstrConstant :: SMTPipe -> L.Lisp -> LispParse (AnyValue PipeConstr)
lispToConstrConstant b sym = do
  (constr,args) <- case sym of
    L.Symbol s -> return (s,[])
    L.List ((L.Symbol s):args) -> return (s,args)
    _ -> throwE $ "Invalid constant: "++show sym
  rev <- case Map.lookup constr (vars b) of
    Just r -> return r
    Nothing -> throwE $ "Invalid constructor "++show constr
  case rev of
    Constr parg dt -> do
      args' <- makeList parg args
      return (AnyValue (ConstrValue (UntypedCon constr parg dt) args'))
    _ -> throwE $ "Invalid constant: "++show sym
  where
    makeList :: List Repr arg -> [L.Lisp] -> LispParse (List (Value PipeConstr) arg)
    makeList Nil [] = return Nil
    makeList Nil _  = throwE $ "Too many arguments to constructor."
    makeList (Cons p args) (l:ls) = do
      AnyValue v <- lispToValue b l
      v' <- case geq p (valueType v) of
        Just Refl -> return v
        Nothing -> throwE $ "Type error in constructor arguments."
      vs <- makeList args ls
      return (Cons v' vs)
    makeList (Cons _ _) [] = throwE $ "Not enough arguments to constructor."

lispToNumber :: L.Lisp -> Maybe Integer
lispToNumber (L.Number (L.I n)) = Just n
lispToNumber (L.List [L.Symbol "-",n]) = do
  n' <- lispToNumber n
  return (negate n')
lispToNumber _ = Nothing

lispToReal :: L.Lisp -> Maybe Rational
lispToReal (L.Number (L.D n)) = Just $ toRational n
lispToReal (L.Number (L.I n)) = Just $ fromInteger n
lispToReal (L.List [L.Symbol "/",v1,v2]) = do
  r1 <- lispToReal v1
  r2 <- lispToReal v2
  return $ r1 / r2
lispToReal _ = Nothing

lispToBitVec :: L.Lisp -> Maybe (Integer,Integer)
lispToBitVec (L.List [L.Symbol "_",L.Symbol (T.stripPrefix "bv" -> Just val),L.Number (L.I sz)])
  = case T.decimal val of
  Right (rval,"") -> Just (rval,sz)
  _ -> Nothing
lispToBitVec (L.Symbol (T.stripPrefix "#x" -> Just bv)) = case T.hexadecimal bv of
  Right (rbv,"") -> Just (rbv,(fromIntegral $ T.length bv)*4)
  _ -> Nothing
lispToBitVec (L.Symbol (T.stripPrefix "#b" -> Just bv))
  | T.all (\c -> c=='0' || c=='1') bv = Just (T.foldl (\v c -> case c of
                                                         '0' -> v*2
                                                         '1' -> v*2+1) 0 bv,
                                              fromIntegral $ T.length bv)
  | otherwise = Nothing
lispToBitVec _ = Nothing

exprToLisp :: Expression PipeVar PipeVar PipeFun PipeConstr PipeField PipeVar PipeVar PipeExpr t
           -> L.Lisp
exprToLisp = runIdentity . exprToLispWith
             (\(UntypedVar v _) -> return $ L.Symbol v)
             (\(UntypedVar v _) -> return $ L.Symbol v)
             (\(UntypedFun v _ _) -> return $ L.Symbol v)
             (\(UntypedCon v _ _) -> return $ L.Symbol v)
             (\(UntypedCon v _ _) -> return $ L.Symbol $ T.append "is-" v)
             (\(UntypedField v _ _) -> return $ L.Symbol v)
             (\(UntypedVar v _) -> return $ L.Symbol v)
             (\(UntypedVar v _) -> return $ L.Symbol v)
             (\(PipeExpr v) -> return $ exprToLisp v)

exprToLispWith :: (Monad m,GetType v,GetType qv,GetFunType fun,GetConType con,GetFieldType field,GetType fv,GetType lv,GetType e)
               => (forall (t' :: Type).
                   v t' -> m L.Lisp)                         -- ^ variables
               -> (forall (t' :: Type).
                   qv t' -> m L.Lisp)                        -- ^ quantified variables
               -> (forall (arg :: [Type]) (res :: Type).
                   fun '(arg,res) -> m L.Lisp) -- ^ functions
               -> (forall (arg :: [Type]) (res :: *).
                   con '(arg,res) -> m L.Lisp)    -- ^ constructor
               -> (forall (arg :: [Type]) (res :: *).
                   con '(arg,res) -> m L.Lisp)    -- ^ constructor tests
               -> (forall (t' :: *) (res :: Type).
                   field '(t',res) -> m L.Lisp)      -- ^ field accesses
               -> (forall t.
                   fv t -> m L.Lisp)                                              -- ^ function variables
               -> (forall t.
                   lv t -> m L.Lisp)                                              -- ^ let variables
               -> (forall (t' :: Type).
                   e t' -> m L.Lisp)                         -- ^ sub expressions
               -> Expression v qv fun con field fv lv e t
               -> m L.Lisp
exprToLispWith f _ _ _ _ _ _ _ _ (Expr.Var v) = f v
exprToLispWith _ f _ _ _ _ _ _ _ (Expr.QVar v) = f v
exprToLispWith _ _ _ _ _ _ f _ _ (Expr.FVar v) = f v
exprToLispWith _ _ _ _ _ _ _ f _ (Expr.LVar v) = f v
-- This is a special case because the argument order is different
exprToLispWith _ _ f g h i _ _ j (Expr.App (Store _ _) (Cons arr (Cons val idx))) = do
  arr' <- j arr
  idx' <- List.toList j idx
  val' <- j val
  return $ L.List ((L.Symbol "store"):arr':idx'++[val'])
exprToLispWith _ _ f g h i _ _ j (Expr.App fun args) = do
  args' <- List.toList j args
  sym <- functionSymbol f g h i fun
  case args' of
    [] -> return sym
    _ -> return $ L.List $ sym:args'
exprToLispWith _ _ _ f _ _ _ _ _ (Expr.Const val) = valueToLisp f val
exprToLispWith _ _ f g h i _ _ _ (Expr.AsArray fun) = do
  sym <- functionSymbolWithSig f g h i fun
  return $  L.List [L.Symbol "_"
                   ,L.Symbol "as-array"
                   ,sym]
exprToLispWith _ f _ _ _ _ _ _ g (Expr.Quantification q args body) = do
  bind <- List.toList (\arg -> do
                          sym <- f arg
                          return $ L.List [sym,typeSymbol $ getType arg]
                      ) args
  body' <- g body
  return $ L.List [L.Symbol (case q of
                               Expr.Forall -> "forall"
                               Expr.Exists -> "exists")
                  ,L.List bind
                  ,body']
exprToLispWith _ _ _ _ _ _ _ f g (Expr.Let args body) = do
  binds <- List.toList (\bind -> do
                          sym <- f (letVar bind)
                          expr <- g (letExpr bind)
                          return $ L.List [sym,expr]
                       ) args
  body' <- g body
  return $ L.List [L.Symbol "let"
                  ,L.List binds
                  ,body']

valueToLisp :: Monad m
            => (forall arg tp. (IsDatatype tp)
                => con '(arg,tp) -> m L.Lisp)
            -> Value con t -> m L.Lisp
valueToLisp _ (BoolValue True) = return $ L.Symbol "true"
valueToLisp _ (BoolValue False) = return $ L.Symbol "false"
valueToLisp _ (IntValue n) = return $ numToLisp n
valueToLisp _ (RealValue n)
  = return $ L.List [L.Symbol "/"
                    ,numToLisp $ numerator n
                    ,numToLisp $ denominator n]
valueToLisp _ (BitVecValue n bw) = return $ L.List [L.Symbol "_"
                                                   ,L.Symbol (T.pack $ "bv"++show n)
                                                   ,L.Number $ L.I $ naturalToInteger bw]
valueToLisp f (ConstrValue con args) = do
  con' <- f con
  args' <- List.toList (valueToLisp f) args
  case args' of
    [] -> return con'
    xs -> return $ L.List (con' : xs)

isOverloaded :: Function fun con field sig -> Bool
isOverloaded (Expr.Eq _ _) = True
isOverloaded (Expr.Distinct _ _) = True
isOverloaded (Expr.Map _ _) = True
isOverloaded (Expr.Ord _ _) = True
isOverloaded (Expr.Arith _ _ _) = True
isOverloaded (Expr.Abs _) = True
isOverloaded (Expr.ITE _) = True
isOverloaded (Expr.BVComp _ _) = True
isOverloaded (Expr.BVBin _ _) = True
isOverloaded (Expr.BVUn _ _) = True
isOverloaded (Expr.Select _ _) = True
isOverloaded (Expr.Store _ _) = True
isOverloaded (Expr.ConstArray _ _) = True
isOverloaded (Expr.Concat _ _) = True
isOverloaded (Expr.Extract _ _ _) = True
isOverloaded _ = False

functionSymbol :: (Monad m,GetFunType fun,GetConType con,GetFieldType field)
                  => (forall (arg' :: [Type]) (res' :: Type).
                      fun '(arg',res') -> m L.Lisp) -- ^ How to render user functions
                  -> (forall (arg' :: [Type]) (res' :: *).
                      con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor applications
                  -> (forall (arg' :: [Type]) (res' :: *).
                      con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor tests
                  -> (forall (t :: *) (res' :: Type).
                      field '(t,res') -> m L.Lisp)          -- ^ How to render field acceses
                  -> Function fun con field '(arg,res) -> m L.Lisp
functionSymbol f _ _ _ (Expr.Fun g) = f g
functionSymbol _ _ _ _ (Expr.Eq _ _) = return $ L.Symbol "="
functionSymbol _ _ _ _ (Expr.Distinct _ _) = return $ L.Symbol "distinct"
functionSymbol f g h i (Expr.Map _ j) = do
  sym <- functionSymbolWithSig f g h i j
  return $  L.List [L.Symbol "_"
                   ,L.Symbol "map"
                   ,sym]
functionSymbol _ _ _ _ (Ord _ op) = return $ ordSymbol op
functionSymbol _ _ _ _ (Arith _ op _) = return $ arithSymbol op
functionSymbol _ _ _ _ (ArithIntBin Div) = return $ L.Symbol "div"
functionSymbol _ _ _ _ (ArithIntBin Mod) = return $ L.Symbol "mod"
functionSymbol _ _ _ _ (ArithIntBin Rem) = return $ L.Symbol "rem"
functionSymbol _ _ _ _ Divide = return $ L.Symbol "/"
functionSymbol _ _ _ _ (Abs _) = return $ L.Symbol "abs"
functionSymbol _ _ _ _ Not = return $ L.Symbol "not"
functionSymbol _ _ _ _ (Logic And _) = return $ L.Symbol "and"
functionSymbol _ _ _ _ (Logic Or _) = return $ L.Symbol "or"
functionSymbol _ _ _ _ (Logic XOr _) = return $ L.Symbol "xor"
functionSymbol _ _ _ _ (Logic Implies _) = return $ L.Symbol "=>"
functionSymbol _ _ _ _ ToReal = return $ L.Symbol "to_real"
functionSymbol _ _ _ _ ToInt = return $ L.Symbol "to_int"
functionSymbol _ _ _ _ (ITE _) = return $ L.Symbol "ite"
functionSymbol _ _ _ _ (BVComp op _) = return $ L.Symbol $ case op of
  BVULE -> "bvule"
  BVULT -> "bvult"
  BVUGE -> "bvuge"
  BVUGT -> "bvugt"
  BVSLE -> "bvsle"
  BVSLT -> "bvslt"
  BVSGE -> "bvsge"
  BVSGT -> "bvsgt"
functionSymbol _ _ _ _ (BVBin op _) = return $ L.Symbol $ case op of
  BVAdd -> "bvadd"
  BVSub -> "bvsub"
  BVMul -> "bvmul"
  BVURem -> "bvurem"
  BVSRem -> "bvsrem"
  BVUDiv -> "bvudiv"
  BVSDiv -> "bvsdiv"
  BVSHL -> "bvshl"
  BVLSHR -> "bvlshr"
  BVASHR -> "bvashr"
  BVXor -> "bvxor"
  BVAnd -> "bvand"
  BVOr -> "bvor"
functionSymbol _ _ _ _ (BVUn op _) = return $ L.Symbol $ case op of
  BVNot -> "bvnot"
  BVNeg -> "bvneg"
functionSymbol _ _ _ _ (Select _ _) = return $ L.Symbol "select"
functionSymbol _ _ _ _ (Store _ _) = return $ L.Symbol "store"
functionSymbol _ _ _ _ (ConstArray idx el)
  = return $ L.List [L.Symbol "as"
                    ,L.Symbol "const"
                    ,typeSymbol (ArrayRepr idx el)]
functionSymbol _ _ _ _ (Concat _ _) = return $ L.Symbol "concat"
functionSymbol _ _ _ _ (Extract bw start len)
  = return $ L.List [L.Symbol "_"
                    ,L.Symbol "extract"
                    ,L.Number $ L.I $ start'+len'-1
                    ,L.Number $ L.I start']
  where
    start' = naturalToInteger start
    len' = naturalToInteger len
functionSymbol _ g _ _ (Constructor con) = g con
functionSymbol _ _ h _ (Test con) = h con
functionSymbol _ _ _ i (Expr.Field f) = i f
functionSymbol _ _ _ _ (Divisible n) = return $ L.List [L.Symbol "_"
                                                       ,L.Symbol "divisible"
                                                       ,L.Number $ L.I n]

functionSymbolWithSig :: (Monad m,GetFunType fun,GetConType con,GetFieldType field)
                      => (forall (arg' :: [Type]) (res' :: Type).
                          fun '(arg',res') -> m L.Lisp) -- ^ How to render user functions
                      -> (forall (arg' :: [Type]) (res' :: *).
                          con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor applications
                      -> (forall (arg' :: [Type]) (res' :: *).
                          con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor tests
                      -> (forall (t :: *) (res' :: Type).
                          field '(t,res') -> m L.Lisp)          -- ^ How to render field acceses
                      -> Function fun con field '(arg,res) -> m L.Lisp
functionSymbolWithSig f g h i j = do
  sym <- functionSymbol f g h i j
  if isOverloaded j
    then return $ L.List [sym
                         ,typeList arg
                         ,typeSymbol res]
    else return sym
  where
    (arg,res) = getFunType j

typeSymbol :: Repr t -> L.Lisp
typeSymbol BoolRepr = L.Symbol "Bool"
typeSymbol IntRepr = L.Symbol "Int"
typeSymbol RealRepr = L.Symbol "Real"
typeSymbol (BitVecRepr n) = L.List [L.Symbol "_"
                                   ,L.Symbol "BitVec"
                                   ,L.Number (L.I $ naturalToInteger n)]
typeSymbol (ArrayRepr idx el) = L.List ((L.Symbol "Array"):
                                        runIdentity (List.toList (return.typeSymbol) idx) ++
                                        [typeSymbol el])
typeSymbol (DataRepr dt) = L.Symbol (T.pack $ datatypeName dt)

typeList :: List Repr t -> L.Lisp
typeList Nil = L.Symbol "()"
typeList args = L.List (runIdentity $ List.toList (return.typeSymbol) args)

ordSymbol :: OrdOp -> L.Lisp
ordSymbol Ge = L.Symbol ">="
ordSymbol Gt = L.Symbol ">"
ordSymbol Le = L.Symbol "<="
ordSymbol Lt = L.Symbol "<"

arithSymbol :: ArithOp -> L.Lisp
arithSymbol Plus = L.Symbol "+"
arithSymbol Mult = L.Symbol "*"
arithSymbol Minus = L.Symbol "-"

numToLisp :: Integer -> L.Lisp
numToLisp n = if n>=0
              then L.Number $ L.I n
              else L.List [L.Symbol "-"
                          ,L.Number $ L.I $ abs n]

clearInput :: SMTPipe -> IO ()
clearInput pipe = do
  r <- hReady (channelOut pipe)
  if r
    then (do
             _ <- BS.hGetSome (channelOut pipe) 1024
             clearInput pipe)
    else return ()

putRequest :: SMTPipe -> L.Lisp -> IO ()
putRequest pipe expr = do
  clearInput pipe
  toByteStringIO (BS.hPutStr $ channelIn pipe) (mappend (L.fromLispExpr expr) flush)
  BS8.hPutStrLn (channelIn pipe) ""
  hFlush (channelIn pipe)

parseResponse :: SMTPipe -> IO L.Lisp
parseResponse pipe = do
  str <- BS.hGetLine (channelOut pipe)
  let continue (Done _ r) = return r
      continue res@(Partial _) = do
        line <- BS.hGetLine (channelOut pipe)
        continue (feed (feed res line) (BS8.singleton '\n'))
      continue (Fail str' ctx msg) = error $ "Error parsing "++show str'++" response in "++show ctx++": "++msg
  continue $ parse L.lisp (BS8.snoc str '\n')

genName :: SMTPipe -> String -> (T.Text,SMTPipe)
genName pipe name = (sym,pipe { names = nnames })
  where
    (sym,nnames) = genName' (names pipe) name

genName' :: Map String Int -> String -> (T.Text,Map String Int)
genName' names name = case Map.lookup name names of
  Nothing -> (T.pack name',Map.insert name 0 names)
  Just n -> (T.pack $ name' ++ "_" ++ show (n+1),
             Map.insert name (n+1) names)
  where
    name' = escapeName name
    escapeName :: String -> String
    escapeName [] = []
    escapeName ('_':xs) = '_':'_':escapeName xs
    escapeName (x:xs) = x:escapeName xs

tacticToLisp :: Tactic -> L.Lisp
tacticToLisp Skip = L.Symbol "skip"
tacticToLisp (AndThen ts) = L.List ((L.Symbol "and-then"):fmap tacticToLisp ts)
tacticToLisp (OrElse ts) = L.List ((L.Symbol "or-else"):fmap tacticToLisp ts)
tacticToLisp (ParOr ts) = L.List ((L.Symbol "par-or"):fmap tacticToLisp ts)
tacticToLisp (ParThen t1 t2) = L.List [L.Symbol "par-then"
                                      ,tacticToLisp t1
                                      ,tacticToLisp t2]
tacticToLisp (TryFor t n) = L.List [L.Symbol "try-for"
                                   ,tacticToLisp t
                                   ,L.Number $ L.I n]
tacticToLisp (If c t1 t2) = L.List [L.Symbol "if"
                                   ,probeToLisp c
                                   ,tacticToLisp t1
                                   ,tacticToLisp t2]
tacticToLisp (FailIf c) = L.List [L.Symbol "fail-if"
                                 ,probeToLisp c]
tacticToLisp (UsingParams (CustomTactic name) []) = L.Symbol (T.pack name)
tacticToLisp (UsingParams (CustomTactic name) pars)
  = L.List ([L.Symbol "using-params"
            ,L.Symbol $ T.pack name]++
            concat [ [L.Symbol (T.pack $ ':':pname)
                     ,case par of
                         ParBool True -> L.Symbol "true"
                         ParBool False -> L.Symbol "false"
                         ParInt i -> L.Number $ L.I i
                         ParDouble i -> L.Number $ L.D i]
                     | (pname,par) <- pars ])

probeToLisp :: Probe a -> L.Lisp
probeToLisp (ProbeBoolConst b)
  = L.Symbol $ if b then "true" else "false"
probeToLisp (ProbeIntConst i)
  = L.Number $ L.I i
probeToLisp (ProbeAnd ps)
  = L.List ((L.Symbol "and"):
            fmap probeToLisp ps)
probeToLisp (ProbeOr ps)
  = L.List ((L.Symbol "or"):
            fmap probeToLisp ps)
probeToLisp (ProbeNot p)
  = L.List [L.Symbol "not"
           ,probeToLisp p]
probeToLisp (ProbeEq p1 p2)
  = L.List [L.Symbol "="
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp (ProbeGt p1 p2)
  = L.List [L.Symbol ">"
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp (ProbeGe p1 p2)
  = L.List [L.Symbol ">="
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp (ProbeLt p1 p2)
  = L.List [L.Symbol "<"
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp (ProbeGe p1 p2)
  = L.List [L.Symbol "<="
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp IsPB = L.Symbol "is-pb"
probeToLisp ArithMaxDeg = L.Symbol "arith-max-deg"
probeToLisp ArithAvgDeg = L.Symbol "arith-avg-deg"
probeToLisp ArithMaxBW = L.Symbol "arith-max-bw"
probeToLisp ArithAvgBW = L.Symbol "arith-avg-bw"
probeToLisp IsQFLIA = L.Symbol "is-qflia"
probeToLisp IsQFLRA = L.Symbol "is-qflra"
probeToLisp IsQFLIRA = L.Symbol "is-qflira"
probeToLisp IsILP = L.Symbol "is-ilp"
probeToLisp IsQFNIA = L.Symbol "is-qfnia"
probeToLisp IsQFNRA = L.Symbol "is-qfnra"
probeToLisp IsNIA = L.Symbol "is-nia"
probeToLisp IsNRA = L.Symbol "is-nra"
probeToLisp IsUnbounded = L.Symbol "is-unbounded"
probeToLisp Memory = L.Symbol "memory"
probeToLisp Depth = L.Symbol "depth"
probeToLisp Size = L.Symbol "size"
probeToLisp NumExprs = L.Symbol "num-exprs"
probeToLisp NumConsts = L.Symbol "num-consts"
probeToLisp NumBoolConsts = L.Symbol "num-bool-consts"
probeToLisp NumArithConsts = L.Symbol "num-arith-consts"
probeToLisp NumBVConsts = L.Symbol "num-bv-consts"
probeToLisp Strat.ProduceProofs = L.Symbol "produce-proofs"
probeToLisp ProduceModel = L.Symbol "produce-model"
probeToLisp Strat.ProduceUnsatCores = L.Symbol "produce-unsat-cores"
probeToLisp HasPatterns = L.Symbol "has-patterns"
probeToLisp IsPropositional = L.Symbol "is-propositional"
probeToLisp IsQFBV = L.Symbol "is-qfbv"
probeToLisp IsQFBVEQ = L.Symbol "is-qfbv-eq"
