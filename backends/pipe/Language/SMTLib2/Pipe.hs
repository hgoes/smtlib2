module Language.SMTLib2.Pipe where

import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type hiding (Constr,Field,Datatype)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Type.Nat as Type
import Language.SMTLib2.Internals.Expression hiding (Fun,Field,Var,QVar)
import qualified Language.SMTLib2.Internals.Expression as Expr
import Language.SMTLib2.Strategy as Strat

import qualified Data.Text as T
import qualified Data.Text.Read as T
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IMap
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

data RevVar = forall (t::Type). GetType t => Var !(Proxy t)
            | forall (t::Type). GetType t => QVar !(Proxy t)
            | forall (arg::[Type]) (t::Type). (GetTypes arg,GetType t) => Fun !(Proxy arg) !(Proxy t)
            | forall (arg::[Type]) (t :: *). (GetTypes arg,IsDatatype t) => Constr !(Proxy arg) !(Proxy t)
            | forall (t :: *) (res :: Type). (IsDatatype t,GetType res) => Field !(Proxy t) !(Proxy res)
            | forall (t::Type). GetType t => FunArg !(Proxy t)
            | forall (t :: *). IsDatatype t => Datatype !(Proxy t)

data InterpolationMode = Z3Interpolation [T.Text] [T.Text]
                       | MathSATInterpolation

newtype PipeExpr (t :: Type) = PipeExpr (Expression PipeVar PipeVar PipeFun PipeConstr PipeField PipeVar PipeExpr t) deriving Show
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

instance Backend SMTPipe where
  type SMTMonad SMTPipe = IO
  type Expr SMTPipe = PipeExpr
  type Var SMTPipe = PipeVar
  type QVar SMTPipe = PipeVar
  type Fun SMTPipe = PipeFun
  type Constr SMTPipe = PipeConstr
  type Field SMTPipe = PipeField
  type FunArg SMTPipe = PipeVar
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
  declareVar name b = with $ \pr -> do
    let (sym,req,nnames) = renderDeclareVar (names b) pr name
        nb = b { names = nnames
               , vars = Map.insert sym (Var pr) (vars b) }
    putRequest nb req
    return (UntypedVar sym,nb)
    where
      with :: (Proxy t -> IO (PipeVar t,SMTPipe)) -> IO (PipeVar t,SMTPipe)
      with f = f Proxy
  createQVar name b = with $ \pr -> do
    let name' = case name of
          Just n -> n
          Nothing -> "qv"
        (name'',nb) = genName b name'
    return (UntypedVar name'',nb { vars = Map.insert name'' (QVar pr) (vars nb) })
    where
      with :: (Proxy t -> IO (PipeVar t,SMTPipe)) -> IO (PipeVar t,SMTPipe)
      with f = f Proxy
  createFunArg name b = with $ \pr -> do
    let name' = case name of
          Just n -> n
          Nothing -> "fv"
        (name'',nb) = genName b name'
    return (UntypedVar name'',nb { vars = Map.insert name'' (FunArg pr) (vars nb) })
    where
      with :: (Proxy t -> IO (PipeVar t,SMTPipe)) -> IO (PipeVar t,SMTPipe)
      with f = f Proxy
  defineVar name (PipeExpr expr::PipeExpr t) b = do
    let pr = Proxy::Proxy t
        (sym,req,nnames) = renderDefineVar (names b) pr name (exprToLisp expr)
        nb = b { names = nnames
               , vars = Map.insert sym (Var pr) (vars b) }
    putRequest nb req
    return (UntypedVar sym,nb)
  declareFun name b = withProxy $ \parg pr -> do
    let (sym,req,nnames) = renderDeclareFun (names b) parg pr name
        nb = b { names = nnames
               , vars = Map.insert sym (Fun parg pr) (vars b) }
    putRequest nb req
    return (UntypedFun sym,nb)    
    where
      withProxy :: (Proxy arg -> Proxy t -> IO (PipeFun '(arg,t),SMTPipe)) -> IO (PipeFun '(arg,t),SMTPipe)
      withProxy f = f Proxy Proxy
  defineFun name arg body b = do
    let (name',req,nnames) = renderDefineFun (\(UntypedVar n) -> L.Symbol n)
                             (\(PipeExpr e) -> exprToLisp e) (names b) name arg body
        nb = b { names = nnames }
    putRequest nb req
    return (UntypedFun name',nb)
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
    return (parseGetValue b l,b)
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
    case runExcept $ lispToExprTyped b resp of
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
    case runExcept $ lispToExprTyped b resp of
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
      mkCons b (ConsCon (con::Type.Constr '(arg,dt)) cons)
        = let (fields,b1) = mkFields b (conFields con)
              b2 = b1 { vars = Map.insert (T.pack $ conName con)
                                          (Constr (Proxy::Proxy arg) (Proxy::Proxy dt))
                                          (vars b1) }
              (cons',b3) = mkCons b2 cons
          in (ConsCon (BackendConstr (conName con)
                                     (UntypedCon $ T.pack $ conName con)
                                     fields
                                     (construct con)
                                     (conTest con))
                      cons',b3)

      mkFields :: IsDatatype dt => SMTPipe -> Args (Type.Field dt) arg
               -> (Args (BackendField PipeField dt) arg,SMTPipe)
      mkFields b NoArg = (NoArg,b)
      mkFields b (Arg (f::Type.Field dt t) fs)
        = let b1 = b { vars = Map.insert (T.pack $ fieldName f)
                                         (Field (Proxy::Proxy dt) (Proxy::Proxy t))
                                         (vars b) }
              (fs',b2) = mkFields b1 fs
          in (Arg (BackendField (fieldName f)
                                (UntypedField $ T.pack $ fieldName f)
                                (fieldGet f))
                  fs',b2)
  exit b = do
    putRequest b (L.List [L.Symbol "exit"])
    hClose (channelIn b)
    hClose (channelOut b)
    terminateProcess (processHandle b)
    _ <- waitForProcess (processHandle b)
    return ((),b)

renderDeclareFun :: (GetTypes arg,GetType ret)
                 => Map String Int -> Proxy arg -> Proxy ret -> Maybe String
                 -> (T.Text,L.Lisp,Map String Int)
renderDeclareFun names (_::Proxy arg) (_::Proxy ret) name
  = (name'',L.List [L.Symbol "declare-fun"
                   ,L.Symbol name''
                   ,typeList (getTypes::Args Repr arg)
                   ,typeSymbol (getType::Repr ret)],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "fun"
    (name'',nnames) = genName' names name'

renderDefineFun :: (GetTypes arg,GetType ret)
                => (forall t. GetType t => fv t -> L.Lisp)
                -> (forall t. GetType t => e t -> L.Lisp)
                -> Map String Int -> Maybe String
                -> Args fv arg
                -> e ret
                -> (T.Text,L.Lisp,Map String Int)
renderDefineFun renderFV renderE names name args (body :: e r)
  = (name'',L.List [L.Symbol "define-fun"
                   ,L.Symbol name''
                   ,L.List $ mkArgs renderFV args
                   ,typeSymbol (getType::Repr r)
                   ,renderE body],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "fun"
    (name'',nnames) = genName' names name'
    mkArgs :: (forall t. GetType t => fv t -> L.Lisp) -> Args fv ts -> [L.Lisp]
    mkArgs _ NoArg = []
    mkArgs renderFV (Arg (v::fv t) xs)
      = (L.List [renderFV v,typeSymbol (getType::Repr t)]):
        mkArgs renderFV xs

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

    mkFields :: Args (Type.Field dt) arg -> [L.Lisp]
    mkFields NoArg = []
    mkFields (Arg f fs) = mkField f : mkFields fs

    mkField :: GetType t => Type.Field dt t -> L.Lisp
    mkField (f::Type.Field dt t) = L.List [L.Symbol $ T.pack $ fieldName f
                                          ,typeSymbol (getType::Repr t)]
      
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

renderDeclareVar :: GetType tp => Map String Int -> Proxy tp -> Maybe String
                 -> (T.Text,L.Lisp,Map String Int)
renderDeclareVar names (_::Proxy tp) name
  = (name'',L.List [L.Symbol "declare-fun"
                   ,L.Symbol name''
                   ,L.Symbol "()"
                   ,typeSymbol (getType::Repr tp)
                   ],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "var"
    (name'',nnames) = genName' names name'

renderDefineVar :: GetType t => Map String Int -> Proxy t -> Maybe String -> L.Lisp
                -> (T.Text,L.Lisp,Map String Int)
renderDefineVar names (_::Proxy t) name lexpr
  = (name'',
     L.List [L.Symbol "define-fun"
            ,L.Symbol name''
            ,L.Symbol "()"
            ,typeSymbol (getType::Repr t)
            ,lexpr],
     nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "var"
    (name'',nnames) = genName' names name'

renderGetValue :: GetType t => SMTPipe -> PipeExpr t -> L.Lisp
renderGetValue b (PipeExpr e) = L.List [L.Symbol "get-value"
                                       ,L.List [exprToLisp e]]

parseGetValue :: GetType t => SMTPipe -> L.Lisp -> Value PipeConstr t
parseGetValue b (L.List [L.List [_,val]]) = case runExcept $ lispToValue b val of
  Right (AnyValue v) -> case cast v of
    Just v' -> v'
    Nothing -> error $ "smtlib2: Wrong type of returned value."
  Left err -> error $ "smtlib2: Failed to parse get-value entry: "++show val++" ["++err++"]"
parseGetValue _ expr = error $ "smtlib2: Failed to parse get-value result: "++show expr

renderGetProof :: L.Lisp
renderGetProof = L.List [L.Symbol "get-proof"]

parseGetProof :: SMTPipe -> L.Lisp -> PipeExpr BoolType
parseGetProof b resp = case runExcept $ lispToExprTyped b proof of
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
          srt <- lispToSort parser rtp
          lispToExprWith parser (Just srt) body $
            \expr -> return $ VarAssignment (UntypedVar fname) (PipeExpr expr)
        _ -> do
          srt <- lispToSort parser rtp
          withFunArgs b args $
            \b' args' -> lispToExprWith (pipeParser b') (Just srt) body $
                           \body' -> return $ FunAssignment (UntypedFun fname) args' (PipeExpr body')
    parseAssignment lsp = throwE $ "Invalid model entry: "++show lsp
    withFunArgs :: SMTPipe -> [L.Lisp] -> (forall arg. GetTypes arg => SMTPipe -> Args PipeVar arg -> LispParse a) -> LispParse a
    withFunArgs b [] f = f b NoArg
    withFunArgs b ((L.List [L.Symbol v,tp]):ls) f = do
      Sort (_::Proxy t) <- lispToSort parser tp
      withFunArgs (b { vars = Map.insert v (FunArg (Proxy::Proxy t)) (vars b) }) ls $
        \b' args -> f b' (Arg (UntypedVar v :: PipeVar t) args)
    withFunArgs _ lsp _ = throwE $ "Invalid fun args: "++show lsp
parseGetModel _ lsp = throwE $ "Invalid model: "++show lsp

data Sort = forall (t :: Type). GetType t => Sort (Proxy t)
data Sorts = forall (t :: [Type]). GetTypes t => Sorts (Proxy t)

data ParsedFunction fun con field
  = ParsedFunction { argumentTypeRequired :: Integer -> Bool
                   , getParsedFunction :: [Maybe Sort] -> LispParse (AnyFunction fun con field)
                   }

data AnyExpr e = forall (t :: Type). GetType t => AnyExpr (e t)

instance GShow e => Show (AnyExpr e) where
  showsPrec p (AnyExpr x) = gshowsPrec p x

data LispParser (v :: Type -> *) (qv :: Type -> *) (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) (fv :: Type -> *) (e :: Type -> *)
  = LispParser { parseFunction :: forall a. Maybe Sort -> T.Text
                               -> (forall args res. (GetTypes args,GetType res) => fun '(args,res) -> a)
                               -> (forall args res. (GetTypes args,IsDatatype res) => con '(args,res) -> a) -- constructor
                               -> (forall args res. (GetTypes args,IsDatatype res) => con '(args,res) -> a) -- constructor test
                               -> (forall t res. (IsDatatype t,GetType res) => field '(t,res) -> a)
                               -> LispParse a
               , parseDatatype :: forall a. T.Text
                               -> (forall t. IsDatatype t => Proxy t -> a)
                               -> LispParse a
               , parseVar :: forall a. Maybe Sort -> T.Text
                          -> (forall t. GetType t => v t -> LispParse a)
                          -> (forall t. GetType t => qv t -> LispParse a)
                          -> (forall t. GetType t => fv t -> LispParse a)
                          -> LispParse a
               , parseRecursive :: forall a. Maybe Sort -> L.Lisp
                                -> (forall t. GetType t => e t -> LispParse a)
                                -> LispParse a
               , registerQVar :: forall (t :: Type). GetType t => T.Text -> Proxy t
                              -> (qv t,LispParser v qv fun con field fv e)
               , registerLetVar :: forall (t :: Type). GetType t => T.Text -> Proxy t
                                -> (v t,LispParser v qv fun con field fv e)
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
                  -> (forall (t::Type). GetType t => PipeExpr t -> LispParse a)
                  -> LispParse a
lispToExprUntyped st l res = lispToExprWith (pipeParser st) Nothing l $
                             \e -> res (PipeExpr e)

lispToExprTyped :: GetType t => SMTPipe -> L.Lisp -> LispParse (PipeExpr t)
lispToExprTyped st l = withProxy $
                       \p -> lispToExprWith (pipeParser st) (Just (Sort p)) l $
                             \e -> case gcast e of
                               Nothing -> throwE $ show l++" has type "++show (getTypeOf e)++", but "++show (getTypeOf p)++" was expected."
                               Just r -> return (PipeExpr r)
  where
    withProxy :: (Proxy t -> LispParse (PipeExpr t)) -> LispParse (PipeExpr t)
    withProxy f = f Proxy

pipeParser :: SMTPipe -> LispParser PipeVar PipeVar PipeFun PipeConstr PipeField PipeVar PipeExpr
pipeParser st = parse
  where
  parse = LispParser { parseFunction = \srt name fun con test field
                                       -> case T.stripPrefix "is-" name of
                                       Just con -> case Map.lookup name (vars st) of
                                         Just (Constr (_::Proxy arg) (_::Proxy t))
                                           -> return $ test (UntypedCon name :: PipeConstr '(arg,t))
                                         _ -> throwE $ "Unknown constructor: "++show name
                                       Nothing -> case Map.lookup name (vars st) of
                                         Just (Fun (_::Proxy arg) (_::Proxy t))
                                           -> return $ fun (UntypedFun name :: PipeFun '(arg,t))
                                         Just (Constr (_::Proxy arg) (_::Proxy t))
                                           -> return $ con (UntypedCon name :: PipeConstr '(arg,t))
                                         Just (Field (_::Proxy t) (_::Proxy res))
                                           -> return $ field (UntypedField name :: PipeField '(t,res))
                                         _ -> throwE $ "Unknown symbol "++show name
                     , parseDatatype = \name res -> case Map.lookup name (datatypes st) of
                                         Just (PipeDatatype p) -> return $ res p
                                         _ -> throwE $ "Unknown datatype "++show name
                     , parseVar = \srt name v qv fv -> case Map.lookup name (vars st) of
                                    Just (Var (_::Proxy t))
                                      -> v (UntypedVar name :: PipeVar t)
                                    Just (QVar (_::Proxy t))
                                      -> qv (UntypedVar name :: PipeVar t)
                                    Just (FunArg (_::Proxy t))
                                      -> fv (UntypedVar name :: PipeVar t)
                                    _ -> throwE $ "Unknown variable "++show name
                     , parseRecursive = \srt l res -> lispToExprWith parse srt l $
                                                      \e -> res (PipeExpr e)
                     , registerQVar = \name pr
                                      -> (UntypedVar name,
                                          pipeParser (st { vars = Map.insert name (QVar pr)
                                                                  (vars st) }))
                     , registerLetVar = \name pr
                                        -> (UntypedVar name,
                                            pipeParser (st { vars = Map.insert name (Var pr)
                                                                    (vars st) }))
                     }

lispToExprWith :: (GShow fun,GShow con,GShow field,GShow e)
               => LispParser v qv fun con field fv e
               -> Maybe Sort
               -> L.Lisp
               -> (forall (t :: Type). GetType t
                   => Expression v qv fun con field fv e t
                   -> LispParse a)
               -> LispParse a
lispToExprWith p hint (runExcept . lispToConstant -> Right (AnyValue val)) res
  = res (Const val)
lispToExprWith p hint (L.Symbol sym) res
  = parseVar p hint sym (res . Expr.Var) (res . Expr.QVar) (res . Expr.FVar)
lispToExprWith p hint (L.List [L.Symbol "_",L.Symbol "as-array",fsym]) res = do
  parsed <- lispToFunction p el_hint fsym
  AnyFunction fun <- getParsedFunction parsed idx_hint
  res (AsArray fun)
  where
    (idx_hint,el_hint) = case hint of
      Nothing -> ([],Nothing)
      Just (Sort (_::Proxy srt)) -> case getType::Repr srt of
        ArrayRepr args (_::Repr el)
          -> (argsToList (\(_::Repr t) -> Just $ Sort (Proxy::Proxy t)) args,
              Just $ Sort (Proxy::Proxy el))
lispToExprWith p hint (L.List [L.Symbol "forall",L.List args,body]) res
  = mkQuant p args $
    \np args' -> parseRecursive np (Just (Sort (Proxy::Proxy BoolType))) body $
                 \body' -> case gcast body' of
                 Just body'' -> res (Quantification Forall args' body'')
lispToExprWith p hint (L.List [L.Symbol "exists",L.List args,body]) res
  = mkQuant p args $
    \np args' -> parseRecursive np (Just (Sort (Proxy::Proxy BoolType))) body $
                 \body' -> case gcast body' of
                 Just body'' -> res (Quantification Exists args' body'')
lispToExprWith p hint (L.List [L.Symbol "let",L.List args,body]) res
  = mkLet p args $
    \np args' -> parseRecursive np hint body $
                 \body' -> res (Let args' body')
lispToExprWith p hint (L.List (fun:args)) res = do
  parsed <- lispToFunction p hint fun
  args' <- matchArgs (argumentTypeRequired parsed) 0 args
  let hints = fmap (\arg -> case arg of
                      Left _ -> Nothing
                      Right (AnyExpr (_::e t)) -> Just $ Sort (Proxy::Proxy t)
                   ) args'
  AnyFunction fun' <- getParsedFunction parsed hints
  let (argTps,ret) = functionType fun'
  args'' <- catchE (makeArgs p argTps args') $
            \err -> throwE $ "While parsing arguments of function: "++
                    show fun'++": "++err
  res $ App fun' args''
  where
    matchArgs _ _ [] = return []
    matchArgs f i (e:es) = if f i
                           then parseRecursive p Nothing e
                                (\e' -> do
                                     rest <- matchArgs f (i+1) es
                                     return $ (Right (AnyExpr e')):rest)
                           else do
                             rest <- matchArgs f (i+1) es
                             return $ (Left e):rest
    makeArgs :: GShow e => LispParser v qv fun con field fv e
             -> Args Repr arg -> [Either L.Lisp (AnyExpr e)] -> LispParse (Args e arg)
    makeArgs _ NoArg [] = return NoArg
    makeArgs _ NoArg _  = throwE $ "Too many arguments to function."
    makeArgs p (Arg (_::Repr t) args) (e:es) = case e of
      Right (AnyExpr e') -> do
        r <- case gcast e' of
           Just e'' -> return e''
           Nothing -> throwE $ "Argument "++gshowsPrec 11 e' ""++" has wrong type."
        rs <- makeArgs p args es
        return (Arg r rs)
      Left l -> parseRecursive p (Just $ Sort (Proxy::Proxy t)) l $
                \e' -> do
                  r <- case gcast e' of
                     Just e'' -> return e''
                     Nothing -> throwE $ "Argument "++gshowsPrec 11 e' ""++" has wrong type."
                  rs <- makeArgs p args es
                  return (Arg r rs)
    makeArgs _ (Arg _ _) [] = throwE $ "Not enough arguments to function."
lispToExprWith _ _ lsp _ = throwE $ "Invalid SMT expression: "++show lsp

mkQuant :: LispParser v qv fun con field fv e -> [L.Lisp]
        -> (forall arg. GetTypes arg => LispParser v qv fun con field fv e -> Args qv arg -> LispParse a)
        -> LispParse a
mkQuant p [] f = f p NoArg
mkQuant p ((L.List [L.Symbol name,sort]):args) f = do
  Sort srt <- lispToSort p sort
  let (qvar,np) = registerQVar p name srt
  mkQuant np args $ \p args -> f p (Arg qvar args)
mkQuant _ lsp _ = throwE $ "Invalid forall/exists parameter: "++show lsp

mkLet :: LispParser v qv fun con field fv e -> [L.Lisp]
         -> (forall arg. GetTypes arg => LispParser v qv fun con field fv e
             -> Args (LetBinding v e) arg -> LispParse a)
         -> LispParse a
mkLet p [] f = f p NoArg
mkLet p ((L.List [L.Symbol name,expr]):args) f
  = parseRecursive p Nothing expr $
    \(expr' :: e t) -> do
      let (lvar,np) = registerLetVar p name (Proxy::Proxy t)
      mkLet np args $ \p args -> f p (Arg (LetBinding lvar expr') args)
mkLet _ lsp _ = throwE $ "Invalid let parameter: "++show lsp

withEq :: GetType t => Proxy (t :: Type) -> [b]
       -> (forall (arg::[Type]). (AllEq (t ': arg),GetTypes arg,SameType (t ': arg) ~ t)
           => Proxy (t ': arg) -> a)
       -> a
withEq (_::Proxy t) [_] f = f (Proxy::Proxy '[t])
withEq p@(_::Proxy t) (_:xs) f = withEq p xs $
                                 \(_::Proxy (t ': arg)) -> f (Proxy :: Proxy (t ': t ': arg))
                                             
lispToFunction :: LispParser v qv fun con field fv e
               -> Maybe Sort -> L.Lisp -> LispParse (ParsedFunction fun con field)
lispToFunction _ _ (L.Symbol "=")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort p):_ -> withEq p args $
                          \(_::Proxy (t ': arg))
                          -> return $ AnyFunction (Eq::Function fun con field '(t ': arg,BoolType))
       _ -> throwE $ "Cannot derive type of = parameters.")
lispToFunction _ _ (L.Symbol "distinct")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort p):_ -> withEq p args $
                          \(_::Proxy (t ': arg))
                          -> return $ AnyFunction (Distinct::Function fun con field '(t ': arg,BoolType))
       _ -> throwE $ "Cannot derive type of \"distinct\" parameters.")
lispToFunction rf sort (L.List [L.Symbol "_",L.Symbol "map",sym]) = do
  f <- lispToFunction rf sort' sym
  let reqArgs 0 = case idx' of
        Nothing -> True
        Just _ -> argumentTypeRequired f 0
      reqArgs n = argumentTypeRequired f n
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
  return (ParsedFunction reqArgs fun)
  where
    (sort',idx') = case sort of
      Just (Sort (_::Proxy p)) -> case getType::Repr p of
        ArrayRepr (_::Args Repr args) (_::Repr t)
          -> (Just (Sort (Proxy::Proxy t)),
              Just (Sorts (Proxy::Proxy args)))
        _ -> (Nothing,Nothing)
      _ -> (Nothing,Nothing)
lispToFunction _ _ (L.Symbol ">=") = lispToOrdFunction Ge
lispToFunction _ _ (L.Symbol ">") = lispToOrdFunction Gt
lispToFunction _ _ (L.Symbol "<=") = lispToOrdFunction Le
lispToFunction _ _ (L.Symbol "<") = lispToOrdFunction Lt
lispToFunction _ sort (L.Symbol "+") = lispToArithFunction sort Plus
lispToFunction _ sort (L.Symbol "*") = lispToArithFunction sort Mult
lispToFunction _ sort (L.Symbol "-") = lispToArithFunction sort Minus
lispToFunction _ sort (L.Symbol "abs") = case sort of
  Just (Sort (_::Proxy srt)) -> case getType::Repr srt of
    IntRepr -> return $ ParsedFunction (const False) (\_ -> return $ AnyFunction AbsInt)
    RealRepr -> return $ ParsedFunction (const False) (\_ -> return $ AnyFunction AbsReal)
    exp -> throwE $ "abs function can't have type "++show exp
  Nothing -> return $ ParsedFunction (==0) $
             \args -> case args of
                [Just (Sort (_::Proxy srt))] -> case getType::Repr srt of
                  IntRepr -> return $ AnyFunction AbsInt
                  RealRepr -> return $ AnyFunction AbsReal
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
  Just (Sort (_::Proxy srt))
    -> return $ ParsedFunction (const False)
       (\_ -> return $ AnyFunction
              (ITE :: Function fun con field '( '[BoolType,srt,srt],srt)))
  Nothing -> return $ ParsedFunction (==1) $
             \args -> case args of
               [_,Just (Sort (_::Proxy srt)),_]
                 -> return $ AnyFunction
                      (ITE :: Function fun con field '( '[BoolType,srt,srt],srt))
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
       Just (Sort (_::Proxy arr)):_ -> case getType::Repr arr of
         ArrayRepr (_::Args Repr idx) (_::Repr val)
           -> return $ AnyFunction (Select :: Function fun con field
                                              '(ArrayType idx val ': idx,val))
         srt -> throwE $ "Invalid argument type to select function: "++show srt
       _ -> throwE $ "Invalid arguments to select function.")
lispToFunction _ sort (L.Symbol "store") = case sort of
  Just (Sort (_::Proxy srt)) -> case getType::Repr srt of
    ArrayRepr (_::Args Repr idx) (_::Repr val)
      -> return (ParsedFunction (const False)
                 (\_ -> return $ AnyFunction
                        (Store :: Function fun con field
                                  '(ArrayType idx val ': val ': idx,ArrayType idx val))))
    srt' -> throwE $ "Invalid argument types to store function: "++show srt'
  Nothing -> return $ ParsedFunction (==0)
             (\args -> case args of
                Just (Sort (_::Proxy arr)):_ -> case getType::Repr arr of
                  ArrayRepr (_::Args Repr idx) (_::Repr val)
                    -> return $ AnyFunction
                       (Store :: Function fun con field
                                 '(ArrayType idx val ': val ': idx,ArrayType idx val))
                  srt -> throwE $ "Invalid first argument type to store function: "++show srt
                _ -> throwE $ "Invalid arguments to store function.")
lispToFunction r sort (L.List [L.Symbol "as",L.Symbol "const",sig]) = do
  Sort (_::Proxy rsig) <- case sort of
    Just srt -> return srt
    Nothing -> lispToSort r sig
  case getType::Repr rsig of
    ArrayRepr (_::Args Repr idx) (_::Repr val)
      -> return $ ParsedFunction (const False)
         (\_ -> return $ AnyFunction (ConstArray :: Function fun con field '( '[val],ArrayType idx val)))
    _ -> throwE $ "Invalid signature for (as const ...) function."
lispToFunction _ sort (L.Symbol "concat")
  = return $ ParsedFunction (const True)
    (\args -> case args of
       [Just (Sort (_::Proxy s1)),Just (Sort (_::Proxy s2))]
         -> case (getType::Repr s1,getType::Repr s2) of
         (BitVecRepr sz1,BitVecRepr sz2)
           -> reifyAdd sz1 sz2 $
              \(_::Proxy p1) (_::Proxy p2)
              -> return $ AnyFunction (Concat :: Function fun con field
                                                 '( '[BitVecType p1,BitVecType p2],
                                                    BitVecType (p1 + p2)))
         _ -> throwE $ "Invalid argument types to concat function."
       _ -> throwE $ "Wrong number of arguments to concat function.")
lispToFunction _ sort (L.List [L.Symbol "_",L.Symbol "extract",L.Number (L.I end),L.Number (L.I start)])
  = return $ ParsedFunction (==0)
    (\args -> case args of
       [Just (Sort (_::Proxy srt))] -> case getType::Repr srt of
         BitVecRepr size -> case reifyExtract start (end-start+1) size $
                                 \pstart (_::Proxy len) (_::Proxy size)
                                   -> AnyFunction
                                      (Extract pstart :: Function fun con field
                                                         '( '[BitVecType size],BitVecType len)) of
                              Just r -> return r
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
            \(_::Proxy sig') -> argsToList (\(_::Repr t) -> Just $ Sort (Proxy::Proxy t)
                                           ) (getTypes::Args Repr sig')
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
               (Just (Sort (_::Proxy srt))):_ -> case getType::Repr srt of
                 IntRepr -> return $ AnyFunction (OrdInt op)
                 RealRepr -> return $ AnyFunction (OrdReal op)
                 srt' -> throwE $ "Invalid argument to "++show op++" function: "++show srt'
               _ -> throwE $ "Wrong number of arguments to "++show op++" function."))

lispToArithFunction :: Maybe Sort -> ArithOp -> LispParse (ParsedFunction fun con field)
lispToArithFunction sort op = case sort of
  Just (Sort (_::Proxy pel)) -> case getType::Repr pel of
    IntRepr -> return (ParsedFunction (const False)
                       (\args -> withEq (Proxy::Proxy IntType) args $
                                 \(_::Proxy ('IntType ': arg))
                                 -> return $ AnyFunction (ArithInt op :: Function fun con field '( 'IntType ': arg,IntType))))
    RealRepr -> return (ParsedFunction (const False)
                        (\args -> withEq (Proxy::Proxy RealType) args $
                                 \(_::Proxy ('RealType ': arg))
                                 -> return $ AnyFunction (ArithReal op :: Function fun con field '( 'RealType ': arg,RealType))))
    srt -> throwE $ "Invalid type of "++show op++" function: "++show srt
  Nothing -> return (ParsedFunction (==0)
                     (\argSrt -> case argSrt of
                        (Just (Sort (_::Proxy srt))):_ -> case getType::Repr srt of
                           IntRepr -> withEq (Proxy::Proxy IntType) argSrt $
                                      \(_::Proxy ('IntType ': arg))
                                      -> return $ AnyFunction (ArithInt op :: Function fun con field '( 'IntType ': arg,IntType))
                           RealRepr -> withEq (Proxy::Proxy RealType) argSrt $
                                       \(_::Proxy ('RealType ': arg))
                                       -> return $ AnyFunction (ArithReal op :: Function fun con field '( 'RealType ': arg,RealType))
                           srt' -> throwE $ "Wrong argument type to "++show op++" function: "++show srt'
                        _ -> throwE $ "Wrong number of arguments to "++show op++" function."))

lispToLogicFunction :: LogicOp -> ParsedFunction fun con field
lispToLogicFunction op
  = ParsedFunction (const False)
    (\args -> withEq (Proxy::Proxy BoolType) args $
       \(_::Proxy (BoolType ': args))
          -> return $ AnyFunction
             (Logic op :: Function fun con field '(BoolType ': args,BoolType)))

lispToBVCompFunction :: BVCompOp -> ParsedFunction fun con field
lispToBVCompFunction op
  = ParsedFunction (==0)
    (\args -> case args of
       [Just (Sort (_::Proxy srt)),_] -> case getType::Repr srt of
         BitVecRepr sz -> reifyNat sz $
           \(_::Proxy sz)
           -> return $ AnyFunction (BVComp op :: Function fun con field
                                                 '( '[BitVecType sz,BitVecType sz],BoolType))
         srt -> throwE $ "Invalid argument type to "++show op++" function: "++show srt
       _ -> throwE $ "Wrong number of arguments to "++show op++" function.")

lispToBVBinFunction :: Maybe Sort -> BVBinOp -> LispParse (ParsedFunction fun con field)
lispToBVBinFunction (Just (Sort (_::Proxy srt))) op = case getType::Repr srt of
  BitVecRepr sz -> reifyNat sz $
    \(_::Proxy sz)
    -> return $ ParsedFunction (const False) $
       \_ -> return $ AnyFunction
             (BVBin op :: Function fun con field '( '[BitVecType sz,BitVecType sz],BitVecType sz))
  srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
lispToBVBinFunction Nothing op
  = return $ ParsedFunction (==0) $
    \args -> case args of
      [Just (Sort (_::Proxy srt)),_] -> case getType::Repr srt of
        BitVecRepr sz -> reifyNat sz $
          \(_::Proxy sz)
          -> return $ AnyFunction
             (BVBin op :: Function fun con field '( '[BitVecType sz,BitVecType sz],BitVecType sz))
        srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
      _ -> throwE $ "Wrong number of arguments to "++show op++" function."

lispToBVUnFunction :: Maybe Sort -> BVUnOp -> LispParse (ParsedFunction fun con field)
lispToBVUnFunction (Just (Sort (_::Proxy srt))) op = case getType::Repr srt of
  BitVecRepr sz -> reifyNat sz $
    \(_::Proxy sz) 
    -> return $ ParsedFunction (const False) $
       \_ -> return $ AnyFunction
             (BVUn op :: Function fun con field '( '[BitVecType sz],BitVecType sz))
  srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
lispToBVUnFunction Nothing op
  = return $ ParsedFunction (==0) $
    \args -> case args of
      [Just (Sort (_::Proxy srt))] -> case getType::Repr srt of
        BitVecRepr sz -> reifyNat sz $
          \(_::Proxy sz)
          -> return $ AnyFunction
             (BVUn op :: Function fun con field '( '[BitVecType sz],BitVecType sz))
        srt' -> throwE $ "Invalid argument type to "++show op++" function: "++show srt'
      _ -> throwE $ "Wrong number of arguments to "++show op++" function."

mkMap :: GetTypes idx => p idx -> AnyFunction fun con field -> AnyFunction fun con field
mkMap (pidx::p idx) (AnyFunction (f :: Function fun con field '(arg,res))) = case getTypeConstr (Proxy::Proxy arg) pidx of
  Dict -> AnyFunction (Map f :: Function fun con field '(Lifted arg idx,ArrayType idx res))

asArraySort :: Sort -> Maybe (Sorts,Sort)
asArraySort (Sort (_::Proxy p)) = case getType::Repr p of
  ArrayRepr (_::Args Repr idx) (_::Repr el)
    -> return (Sorts (Proxy::Proxy idx),Sort (Proxy::Proxy el))
  _ -> Nothing

lispToList :: L.Lisp -> Maybe [L.Lisp]
lispToList (L.Symbol "()") = Just []
lispToList (L.List lst) = Just lst
lispToList _ = Nothing

lispToSort :: LispParser v qv fun con field fv e -> L.Lisp -> LispParse Sort
lispToSort _ (L.Symbol "Bool") = return (Sort (Proxy::Proxy BoolType))
lispToSort _ (L.Symbol "Int") = return (Sort (Proxy::Proxy IntType))
lispToSort _ (L.Symbol "Real") = return (Sort (Proxy::Proxy RealType))
lispToSort r (L.List ((L.Symbol "Array"):tps)) = do
  Sort (_::Proxy rtp') <- lispToSort r rtp
  lispToSorts r idx (\(_::Proxy idx') -> Sort (Proxy::Proxy (ArrayType idx' rtp')))
  where
    (idx,rtp) = splitLast tps
    splitLast [x] = ([],x)
    splitLast (x:xs) = let (xs',y') = splitLast xs
                       in (x:xs',y')
lispToSort _ (L.List [L.Symbol "_",L.Symbol "BitVec",L.Number (L.I n)])
  = reifyNat n $ \(_::Proxy sz) -> return (Sort (Proxy::Proxy (BitVecType sz)))
lispToSort r (L.Symbol name) = parseDatatype r name $
                               \(_::Proxy t) -> Sort (Proxy::Proxy (DataType t))
lispToSort _ lsp = throwE $ "Invalid SMT type: "++show lsp

lispToSorts :: LispParser v qv fun con field fv e -> [L.Lisp]
            -> (forall (arg :: [Type]). GetTypes arg => Proxy arg -> a)
            -> LispParse a
lispToSorts _ [] f = return (f (Proxy::Proxy ('[]::[Type])))
lispToSorts r (x:xs) f = do
  Sort (_::Proxy t) <- lispToSort r x
  lispToSorts r xs $
    \(_::Proxy ts) -> f (Proxy::Proxy (t ': ts))

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
  = reifyNat sz $ \(_::Proxy tsz) -> return (AnyValue (BitVecValue val::Value con (BitVecType tsz)))
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
    Constr parg (_::Proxy res) -> do
      args' <- makeArgs (getTypesOf parg) args
      return (AnyValue (ConstrValue (UntypedCon constr) args'
                         :: Value PipeConstr (DataType res)))
    _ -> throwE $ "Invalid constant: "++show sym
  where
    makeArgs :: Args Repr arg -> [L.Lisp] -> LispParse (Args (Value PipeConstr) arg)
    makeArgs NoArg [] = return NoArg
    makeArgs NoArg _  = throwE $ "Too many arguments to constructor."
    makeArgs (Arg p args) (l:ls) = do
      AnyValue v <-  lispToValue b l
      v' <- case gcast v of
        Just r -> return r
        Nothing -> throwE $ "Type error in constructor arguments."
      vs <- makeArgs args ls
      return (Arg v' vs)
    makeArgs (Arg _ _) [] = throwE $ "Not enough arguments to constructor."

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

exprToLisp :: GetType t
           => Expression PipeVar PipeVar PipeFun PipeConstr PipeField PipeVar PipeExpr t
           -> L.Lisp
exprToLisp = runIdentity . exprToLispWith
             (\(UntypedVar v) -> return $ L.Symbol v)
             (\(UntypedVar v) -> return $ L.Symbol v)
             (\(UntypedFun v) -> return $ L.Symbol v)
             (\(UntypedCon v) -> return $ L.Symbol v)
             (\(UntypedCon v) -> return $ L.Symbol $ T.append "is-" v)
             (\(UntypedField v) -> return $ L.Symbol v)
             (\(UntypedVar v) -> return $ L.Symbol v)
             (\(PipeExpr v) -> return $ exprToLisp v)

exprToLispWith :: (Monad m,GetType t)
               => (forall (t' :: Type).
                   GetType t' => v t' -> m L.Lisp)                         -- ^ variables
               -> (forall (t' :: Type).
                   GetType t' => qv t' -> m L.Lisp)                        -- ^ quantified variables
               -> (forall (arg :: [Type]) (res :: Type).
                   (GetTypes arg,GetType res) => fun '(arg,res) -> m L.Lisp) -- ^ functions
               -> (forall (arg :: [Type]) (res :: *).
                   GetTypes arg => con '(arg,res) -> m L.Lisp)    -- ^ constructor
               -> (forall (arg :: [Type]) (res :: *).
                   GetTypes arg => con '(arg,res) -> m L.Lisp)    -- ^ constructor tests
               -> (forall (t' :: *) (res :: Type).
                   GetType res => field '(t',res) -> m L.Lisp)      -- ^ field accesses
               -> (fv t -> m L.Lisp)                                              -- ^ function variables
               -> (forall (t' :: Type).
                   GetType t' => e t' -> m L.Lisp)                         -- ^ sub expressions
               -> Expression v qv fun con field fv e t
               -> m L.Lisp
exprToLispWith f _ _ _ _ _ _ _ (Expr.Var v) = f v
exprToLispWith _ f _ _ _ _ _ _ (Expr.QVar v) = f v
exprToLispWith _ _ _ _ _ _ f _ (Expr.FVar v) = f v
-- This is a special case because the argument order is different
exprToLispWith _ _ f g h i _ j (Expr.App Store (Arg arr (Arg val idx))) = do
  arr' <- j arr
  idx' <- argsToListM j idx
  val' <- j val
  return $ L.List ((L.Symbol "store"):arr':idx'++[val'])
exprToLispWith _ _ f g h i _ j (Expr.App fun args) = do
  args' <- argsToListM j args
  sym <- functionSymbol f g h i fun
  case args' of
    [] -> return sym
    _ -> return $ L.List $ sym:args'
exprToLispWith _ _ _ f _ _ _ _ (Expr.Const val) = valueToLisp f val
exprToLispWith _ _ f g h i _ _ (Expr.AsArray fun) = do
  sym <- functionSymbolWithSig f g h i fun
  return $  L.List [L.Symbol "_"
                   ,L.Symbol "as-array"
                   ,sym]
exprToLispWith _ f _ _ _ _ _ g (Expr.Quantification q args body) = do
  bind <- argsToListM (\arg -> do
                          sym <- f arg
                          return $ L.List [sym,typeSymbol $ getTypeOf arg]
                      ) args
  body' <- g body
  return $ L.List [L.Symbol (case q of
                               Expr.Forall -> "forall"
                               Expr.Exists -> "exists")
                  ,L.List bind
                  ,body']
exprToLispWith f _ _ _ _ _ _ g (Expr.Let args body) = do
  binds <- argsToListM (\bind -> do
                          sym <- f (letVar bind)
                          expr <- g (letExpr bind)
                          return $ L.List [sym,expr]
                       ) args
  body' <- g body
  return $ L.List [L.Symbol "let"
                  ,L.List binds
                  ,body']

valueToLisp :: Monad m
            => (forall arg tp. (GetTypes arg,IsDatatype tp)
                => con '(arg,tp) -> m L.Lisp)
            -> Value con t -> m L.Lisp
valueToLisp _ (BoolValue True) = return $ L.Symbol "true"
valueToLisp _ (BoolValue False) = return $ L.Symbol "false"
valueToLisp _ (IntValue n) = return $ numToLisp n
valueToLisp _ (RealValue n)
  = return $ L.List [L.Symbol "/"
                    ,numToLisp $ numerator n
                    ,numToLisp $ denominator n]
valueToLisp _ (BitVecValue n::Value con tp) = return $ case getType::Repr tp of
  BitVecRepr sz -> L.List [L.Symbol "_"
                          ,L.Symbol (T.pack $ "bv"++show n)
                          ,L.Number $ L.I sz]
valueToLisp f (ConstrValue con args) = do
  con' <- f con
  args' <- argsToListM (valueToLisp f) args
  case args' of
    [] -> return con'
    xs -> return $ L.List (con' : xs)

isOverloaded :: Function fun con field sig -> Bool
isOverloaded Expr.Eq = True
isOverloaded Expr.Distinct = True
isOverloaded (Expr.Map _) = True
isOverloaded (Expr.OrdInt _) = True
isOverloaded (Expr.OrdReal _) = True
isOverloaded (Expr.ArithInt _) = True
isOverloaded (Expr.ArithReal _) = True
isOverloaded Expr.AbsInt = True
isOverloaded Expr.AbsReal = True
isOverloaded Expr.ITE = True
isOverloaded (Expr.BVComp _) = True
isOverloaded (Expr.BVBin _) = True
isOverloaded (Expr.BVUn _) = True
isOverloaded Expr.Select = True
isOverloaded Expr.Store = True
isOverloaded Expr.ConstArray = True
isOverloaded Expr.Concat = True
isOverloaded (Expr.Extract _) = True
isOverloaded _ = False

functionSymbol :: (Monad m,GetTypes arg,GetType res)
                  => (forall (arg' :: [Type]) (res' :: Type).
                      (GetTypes arg',GetType res') => fun '(arg',res') -> m L.Lisp) -- ^ How to render user functions
                  -> (forall (arg' :: [Type]) (res' :: *).
                      GetTypes arg' => con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor applications
                  -> (forall (arg' :: [Type]) (res' :: *).
                      GetTypes arg' => con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor tests
                  -> (forall (t :: *) (res' :: Type).
                      GetType res' => field '(t,res') -> m L.Lisp)          -- ^ How to render field acceses
                  -> Function fun con field '(arg,res) -> m L.Lisp
functionSymbol f _ _ _ (Expr.Fun g) = f g
functionSymbol _ _ _ _ Expr.Eq = return $ L.Symbol "="
functionSymbol _ _ _ _ Expr.Distinct = return $ L.Symbol "distinct"
functionSymbol f g h i (Expr.Map j) = do
  sym <- functionSymbolWithSig f g h i j
  return $  L.List [L.Symbol "_"
                   ,L.Symbol "map"
                   ,sym]
functionSymbol _ _ _ _ (OrdInt op) = return $ ordSymbol op
functionSymbol _ _ _ _ (OrdReal op) = return $ ordSymbol op
functionSymbol _ _ _ _ (ArithInt op) = return $ arithSymbol op
functionSymbol _ _ _ _ (ArithReal op) = return $ arithSymbol op
functionSymbol _ _ _ _ (ArithIntBin Div) = return $ L.Symbol "div"
functionSymbol _ _ _ _ (ArithIntBin Mod) = return $ L.Symbol "mod"
functionSymbol _ _ _ _ (ArithIntBin Rem) = return $ L.Symbol "rem"
functionSymbol _ _ _ _ Divide = return $ L.Symbol "/"
functionSymbol _ _ _ _ AbsInt = return $ L.Symbol "abs"
functionSymbol _ _ _ _ AbsReal = return $ L.Symbol "abs"
functionSymbol _ _ _ _ Not = return $ L.Symbol "not"
functionSymbol _ _ _ _ (Logic And) = return $ L.Symbol "and"
functionSymbol _ _ _ _ (Logic Or) = return $ L.Symbol "or"
functionSymbol _ _ _ _ (Logic XOr) = return $ L.Symbol "xor"
functionSymbol _ _ _ _ (Logic Implies) = return $ L.Symbol "=>"
functionSymbol _ _ _ _ ToReal = return $ L.Symbol "to_real"
functionSymbol _ _ _ _ ToInt = return $ L.Symbol "to_int"
functionSymbol _ _ _ _ ITE = return $ L.Symbol "ite"
functionSymbol _ _ _ _ (BVComp op) = return $ L.Symbol $ case op of
  BVULE -> "bvule"
  BVULT -> "bvult"
  BVUGE -> "bvuge"
  BVUGT -> "bvugt"
  BVSLE -> "bvsle"
  BVSLT -> "bvslt"
  BVSGE -> "bvsge"
  BVSGT -> "bvsgt"
functionSymbol _ _ _ _ (BVBin op) = return $ L.Symbol $ case op of
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
functionSymbol _ _ _ _ (BVUn op) = return $ L.Symbol $ case op of
  BVNot -> "bvnot"
  BVNeg -> "bvneg"
functionSymbol _ _ _ _ Select = return $ L.Symbol "select"
functionSymbol _ _ _ _ Store = return $ L.Symbol "store"
functionSymbol _ _ _ _ (ConstArray::Function fun con field '(arg,res))
  = return $ L.List [L.Symbol "as"
                    ,L.Symbol "const"
                    ,typeSymbol (getType::Repr res)]
functionSymbol _ _ _ _ Concat = return $ L.Symbol "concat"
functionSymbol _ _ _ _ f@(Extract start)
  = return $ case f of
  (_::Function fun con field '( '[BitVecType size],BitVecType len))
      -> L.List [L.Symbol "_"
                ,L.Symbol "extract"
                ,L.Number $ L.I $ start'+len'-1
                ,L.Number $ L.I start']
         where
           start' = natVal start
           len' = natVal (Proxy::Proxy len)
functionSymbol _ g _ _ (Constructor con) = g con
functionSymbol _ _ h _ (Test con) = h con
functionSymbol _ _ _ i (Expr.Field f) = i f
functionSymbol _ _ _ _ (Divisible n) = return $ L.List [L.Symbol "_"
                                                       ,L.Symbol "divisible"
                                                       ,L.Number $ L.I n]

functionSymbolWithSig :: (Monad m,GetTypes arg,GetType res)
                      => (forall (arg' :: [Type]) (res' :: Type).
                          (GetTypes arg',GetType res')
                          => fun '(arg',res') -> m L.Lisp) -- ^ How to render user functions
                      -> (forall (arg' :: [Type]) (res' :: *).
                          GetTypes arg' => con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor applications
                      -> (forall (arg' :: [Type]) (res' :: *).
                          GetTypes arg' => con '(arg',res') -> m L.Lisp)    -- ^ How to render constructor tests
                      -> (forall (t :: *) (res' :: Type).
                          GetType res' => field '(t,res') -> m L.Lisp)          -- ^ How to render field acceses
                      -> Function fun con field '(arg,res) -> m L.Lisp
functionSymbolWithSig f g h i (j::Function fun con field '(arg,res)) = do
  sym <- functionSymbol f g h i j
  if isOverloaded j
    then return $ L.List [sym
                         ,typeList (getTypes::Args Repr arg)
                         ,typeSymbol (getType::Repr res)]
    else return sym

typeSymbol :: Repr t -> L.Lisp
typeSymbol BoolRepr = L.Symbol "Bool"
typeSymbol IntRepr = L.Symbol "Int"
typeSymbol RealRepr = L.Symbol "Real"
typeSymbol (BitVecRepr n) = L.List [L.Symbol "_"
                                   ,L.Symbol "BitVec"
                                   ,L.Number (L.I n)]
typeSymbol (ArrayRepr idx el) = L.List ((L.Symbol "Array"):
                                        argsToList typeSymbol idx ++
                                        [typeSymbol el])
typeSymbol (DataRepr dt) = L.Symbol (T.pack $ datatypeName dt)

typeList :: Args Repr t -> L.Lisp
typeList NoArg = L.Symbol "()"
typeList args = L.List (argsToList typeSymbol args)

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
