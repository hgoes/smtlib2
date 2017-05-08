module Language.SMTLib2.Pipe.Internals where

import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type --hiding (Constr,Field,Datatype)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Type.Nat as Type
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Expression hiding (Fun,Field,Var,QVar,LVar)
import qualified Language.SMTLib2.Internals.Expression as Expr
import qualified Language.SMTLib2.Internals.Proof as P
import Language.SMTLib2.Strategy as Strat

import qualified Data.Text as T
import qualified Data.Text.Read as T
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
import Data.Proxy
import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show
#if !MIN_VERSION_base(4,8,0)
import Data.Monoid
#endif
import Data.Foldable (foldlM)
import Control.Monad.Except
import Data.Traversable
import qualified GHC.TypeLits as TL

import System.Process
import System.IO
import qualified Data.ByteString as BS hiding (reverse)
import qualified Data.ByteString.Char8 as BS8
import Blaze.ByteString.Builder
import Data.Attoparsec.ByteString

import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Ratio

import Control.Monad.Identity
import Control.Monad.State

data PipeDatatype = forall a. IsDatatype a => PipeDatatype (Proxy a)

data SMTPipe = SMTPipe { channelIn :: Handle
                       , channelOut :: Handle
                       , processHandle :: Maybe ProcessHandle
                       , names :: Map String Int
                       , vars :: Map T.Text RevVar
                       , datatypes :: TypeRegistry T.Text T.Text T.Text
                       , interpolationMode :: InterpolationMode }
             deriving Typeable

data RevVar = forall (t::Type). Var !(Repr t)
            | forall (t::Type). QVar !(Repr t)
            | forall (arg::[Type]) (t::Type). Fun !(List Repr arg) !(Repr t)
            | forall (t::Type). FunArg !(Repr t)
            | forall (t::Type). LVar !(Repr t)

data InterpolationMode = Z3Interpolation [T.Text] [T.Text]
                       | MathSATInterpolation

type PipeVar = UntypedVar T.Text
type PipeFun = UntypedFun T.Text

newtype PipeClauseId = PipeClauseId T.Text deriving (Show,Eq,Ord,Typeable)

type PipeProofNode = P.Proof L.Lisp (Expr SMTPipe) Int

data PipeProof = PipeProof { proofNodes :: Map Int PipeProofNode
                           , proofNode :: Int }

instance Eq PipeProof where
  (==) (PipeProof _ x) (PipeProof _ y) = x == y

instance Ord PipeProof where
  compare (PipeProof _ x) (PipeProof _ y) = compare x y

instance Show PipeProof where
  showsPrec p pr = showParen (p>10) $ showsPrec 0 (proofNode pr)

instance GEq (Expr SMTPipe) where
  geq (PipeExpr e1) (PipeExpr e2) = geq e1 e2

instance GCompare (Expr SMTPipe) where
  gcompare (PipeExpr e1) (PipeExpr e2) = gcompare e1 e2

instance GShow (Expr SMTPipe) where
  gshowsPrec = showsPrec

instance GetType (Expr SMTPipe) where
  getType (PipeExpr e) = getType e

instance Backend SMTPipe where
  type SMTMonad SMTPipe = IO
  newtype Expr SMTPipe t = PipeExpr (Expression PipeVar PipeVar PipeFun PipeVar PipeVar (Expr SMTPipe) t) deriving (Show,Typeable)
  type Var SMTPipe = PipeVar
  type QVar SMTPipe = PipeVar
  type Fun SMTPipe = PipeFun
  type FunArg SMTPipe = PipeVar
  type LVar SMTPipe = PipeVar
  type ClauseId SMTPipe = PipeClauseId
  type Model SMTPipe = AssignmentModel SMTPipe
  type Proof SMTPipe = PipeProof
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
        (sym,req,nnames) = renderDefineVar (names b) tp name (exprToLisp (datatypes b) expr)
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
                             (\(PipeExpr e) -> exprToLisp (datatypes b) e) (names b) name arg body
        nb = b { names = nnames }
    putRequest nb req
    return (UntypedFun name' argTp bodyTp,nb)
  assert (PipeExpr expr) b = do
    putRequest b (L.List [L.Symbol "assert"
                         ,exprToLisp (datatypes b) expr])
    return ((),b)
  assertId (PipeExpr expr) b = do
    let (name,b1) = genName b "cl"
    putRequest b1 (L.List [L.Symbol "assert"
                          ,L.List [L.Symbol "!"
                                  ,exprToLisp (datatypes b) expr
                                  ,L.Symbol ":named"
                                  ,L.Symbol name]])
    return (PipeClauseId name,b1)
  assertPartition (PipeExpr expr) part b = case interpolationMode b of
    Z3Interpolation grpA grpB -> do
      let (name,b1) = genName b "grp"
      putRequest b1 (L.List [L.Symbol "assert"
                          ,L.List [L.Symbol "!"
                                  ,exprToLisp (datatypes b) expr
                                  ,L.Symbol ":named"
                                  ,L.Symbol name]])
      return ((),b1 { interpolationMode = case part of
                      PartitionA -> Z3Interpolation (name:grpA) grpB
                      PartitionB -> Z3Interpolation grpA (name:grpB) })
    MathSATInterpolation -> do
      putRequest b (L.List [L.Symbol "assert"
                           ,L.List [L.Symbol "!"
                                  ,exprToLisp (datatypes b) expr
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
  analyzeProof b pr = case Map.lookup (proofNode pr) (proofNodes pr) of
    Just nd -> case nd of
      P.Rule r args res -> P.Rule (show r) (fmap (\arg -> PipeProof (proofNodes pr) arg) args) res
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
                         ,exprToLisp (datatypes b) expr])
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
    let (req,nnames,nreg) = renderDeclareDatatype (names b) (datatypes b) coll
        nb = b { names = nnames
               , datatypes = nreg }
    putRequest nb req
    return ((),nb)
  exit b = do
    putRequest b (L.List [L.Symbol "exit"])
    hClose (channelIn b)
    hClose (channelOut b)
    case processHandle b of
      Nothing -> return ()
      Just ph -> do
        terminateProcess ph
        _ <- waitForProcess ph
        return ()
    return ((),b)
  comment msg b = do
    hPutStrLn (channelIn b) ("; "++msg)
    return ((),b)
  builtIn name arg ret b = return (UntypedFun (T.pack name) arg ret,b)

renderDeclareFun :: Map String Int -> List Repr arg -> Repr ret -> Maybe String
                 -> (T.Text,L.Lisp,Map String Int)
renderDeclareFun names args ret name
  = (name'',L.List [L.Symbol "declare-fun"
                   ,L.Symbol name''
                   ,typeList args
                   ,typeSymbol Set.empty ret],nnames)
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
                   ,typeSymbol Set.empty (getType body)
                   ,renderE body],nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "fun"
    (name'',nnames) = genName' names name'
    mkList :: GetType fv => (forall t. fv t -> L.Lisp) -> List fv ts -> [L.Lisp]
    mkList _ Nil = []
    mkList renderFV (v ::: xs)
      = (L.List [renderFV v,typeSymbol Set.empty (getType v)]):
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

renderDeclareDatatype' :: Integer
                       -> [(T.Text,[(T.Text,[(T.Text,L.Lisp)])])]
                       -> L.Lisp
renderDeclareDatatype' npar coll
  = L.List [L.Symbol "declare-datatypes"
           ,case npar of
              0 -> L.Symbol "()"
              _ -> L.List [L.Symbol $ T.pack $ "a"++show i
                          | i <- [0..npar-1]]
           ,L.List [ L.List ((L.Symbol name):
                             [L.List ((L.Symbol con):
                                      [ L.List [L.Symbol field
                                               ,tp]
                                      | (field,tp) <- fields ])
                             | (con,fields) <- cons ])
                   | (name,cons) <- coll]]

renderDeclareDatatype :: Map String Int -> TypeRegistry T.Text T.Text T.Text -> [AnyDatatype]
                      -> (L.Lisp,Map String Int,TypeRegistry T.Text T.Text T.Text)
renderDeclareDatatype names reg dts
  = (renderDeclareDatatype' (case dts of
                               AnyDatatype dt : _ -> naturalToInteger (parameters dt)
                               [] -> 0)
      str,nnames,nreg)
  where
    ((nnames,nreg),str) = mapAccumL mkDt (names,reg) dts
    mkDt (names,reg) dt'@(AnyDatatype dt)
      = let (name,names1) = genName' names (datatypeName dt)
            reg1 = reg { allDatatypes = Map.insert name dt' (allDatatypes reg)
                       , revDatatypes = Map.insert dt' name (revDatatypes reg) }
            (cons,(names2,reg2)) = runState (List.toList (mkCon dt)
                                             (constructors dt)) (names1,reg1)
        in ((names2,reg2),(name,cons))
    mkCon dt con = do
      (names,reg) <- get
      let (name,names1) = genName' names (constrName con)
          reg1 = reg { allConstructors = Map.insert name (AnyConstr dt con) (allConstructors reg)
                     , revConstructors = Map.insert (AnyConstr dt con) name (revConstructors reg) }
      put (names1,reg1)
      fs <- List.toList (mkField dt) (fields con)
      return (name,fs)
    mkField dt field = do
      (names,reg) <- get
      let (name,names1) = genName' names (fieldName field)
          reg1 = reg { allFields = Map.insert name (AnyField dt field) (allFields reg)
                     , revFields = Map.insert (AnyField dt field) name (revFields reg) }
      put (names1,reg1)
      return (name,typeSymbol allTypes (fieldType field))

    allParameters :: (forall n. Natural n -> a) -> a
    allParameters f = case dts of
      AnyDatatype dt : dts'
        | all (\(AnyDatatype dt') -> case geq (parameters dt') (parameters dt) of
                  Just Refl -> True
                  Nothing -> False) dts' -> f (parameters dt)
      _ -> error "Not all datatypes in a cycle share the same parameters."

    isRecType :: IsDatatype dt => Datatype dt -> Bool
    isRecType dt = Set.member (datatypeName dt) allTypes
    
    allTypes :: Set String
    allTypes = Set.fromList [ datatypeName dt
                            | AnyDatatype dt <- dts ]
    
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
                   ,typeSymbol Set.empty tp
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
            ,typeSymbol Set.empty tp
            ,lexpr],
     nnames)
  where
    name' = case name of
              Just n -> n
              Nothing -> "var"
    (name'',nnames) = genName' names name'

renderGetValue :: SMTPipe -> Expr SMTPipe t -> L.Lisp
renderGetValue b (PipeExpr e) = L.List [L.Symbol "get-value"
                                       ,L.List [exprToLisp (datatypes b) e]]

parseGetValue :: SMTPipe -> Repr t -> L.Lisp -> Value t
parseGetValue b repr (L.List [L.List [_,val]])
  = case runExcept $ lispToValue b (Just $ Sort repr) val of
  Right (AnyValue v) -> case geq repr (valueType v) of
    Just Refl -> v
    Nothing -> error $ "smtlib2: Wrong type of returned value."
  Left err -> error $ "smtlib2: Failed to parse get-value entry: "++show val++" ["++err++"]"
parseGetValue _ _ expr = error $ "smtlib2: Failed to parse get-value result: "++show expr

renderGetProof :: L.Lisp
renderGetProof = L.List [L.Symbol "get-proof"]

parseGetProof :: SMTPipe -> L.Lisp -> PipeProof
parseGetProof b resp = case runExcept $ parseProof b Map.empty Map.empty Map.empty proof of
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

parseProof :: SMTPipe
           -> Map T.Text (Expr SMTPipe BoolType)
           -> Map T.Text Int
           -> Map Int PipeProofNode
           -> L.Lisp
           -> LispParse PipeProof
parseProof pipe exprs proofs nodes l = case l of
  L.List [L.Symbol "let",L.List defs,body] -> do
    (nexprs,nproofs,nnodes)
      <- foldlM (\(exprs,proofs,nodes) def
                 -> case def of
                    L.List [L.Symbol name,def'] -> do
                      res <- parseDef exprs proofs nodes def'
                      case res of
                        Left expr -> return (Map.insert name expr exprs,proofs,nodes)
                        Right (proof,nnodes)
                          -> return (exprs,Map.insert name proof proofs,nnodes)
                ) (exprs,proofs,nodes) defs
    parseProof pipe nexprs nproofs nnodes body
  _ -> do
    (res,nnodes) <- parseDefProof exprs proofs nodes l
    return (PipeProof nnodes res)
  where
    exprParser = pipeParser pipe
    exprParser' exprs = exprParser { parseRecursive = \_ -> parseDefExpr' exprs
                                   }
    parseDefExpr' :: Map T.Text (Expr SMTPipe BoolType) -> Maybe Sort -> L.Lisp
                  -> (forall tp. Expr SMTPipe tp -> LispParse a)
                  -> LispParse a
    parseDefExpr' exprs srt l@(L.Symbol name) res = case Map.lookup name exprs of
      Just def -> res def
      Nothing -> lispToExprWith (exprParser' exprs) srt l $
                 \e -> res (PipeExpr e)
    parseDefExpr' exprs srt l res = lispToExprWith (exprParser' exprs) srt l
                                    (res.PipeExpr)
    parseDefExpr :: Map T.Text (Expr SMTPipe BoolType) -> L.Lisp
                 -> LispParse (Expr SMTPipe BoolType)
    parseDefExpr exprs l = parseDefExpr' exprs (Just $ Sort BoolRepr) l $
                           \e -> case getType e of
                             BoolRepr -> return e
                             _ -> throwError "let expression in proof is not bool"
    parseDefProof exprs proofs nodes (L.List (rule:args)) = do
      (args',res,nnodes) <- parseArgs nodes args
      let sz = Map.size nnodes
      return (sz,Map.insert sz (P.Rule rule args' res) nnodes)
      where
        parseArgs nodes [x] = case x of
          L.List [L.Symbol "~",lhs,rhs] -> do
            lhs' <- parseDefExpr exprs lhs
            rhs' <- parseDefExpr exprs rhs
            return ([],P.EquivSat lhs' rhs',nodes)
          _ -> do
            e <- parseDefExpr exprs x
            return ([],P.ProofExpr e,nodes)
        parseArgs nodes (x:xs) = do
          (nd,nodes1) <- parseDefProof exprs proofs nodes x
          (nds,res,nodes2) <- parseArgs nodes1 xs
          return (nd:nds,res,nodes2)
    parseDefProof exprs proofs nodes (L.Symbol sym) = case Map.lookup sym proofs of
      Just pr -> return (pr,nodes)
    parseDef exprs proofs nodes l
      = (fmap Left $ parseDefExpr exprs l) `catchError`
        (\_ -> fmap Right $ parseDefProof exprs proofs nodes l)

parseGetModel :: SMTPipe -> L.Lisp -> LispParse (Model SMTPipe)
parseGetModel b (L.List ((L.Symbol "model"):mdl)) = do
  nb <- foldlM adapt b mdl
  assign <- mapM (parseAssignment nb) mdl
  return $ AssignmentModel assign
  where
    adapt b (L.List [L.Symbol "define-fun",L.Symbol fname,L.List args,rtp,body])
      = case args of
      [] -> do
        srt@(Sort tp) <- lispToSort (pipeParser b) rtp
        return $ b { vars = Map.insert fname (Var tp) (vars b) }
      _ -> do
        srt@(Sort tp) <- lispToSort (pipeParser b) rtp
        withFunList b args $
          \b' tps args'
           -> return $ b { vars = Map.insert fname (Fun tps tp) (vars b) }
    parseAssignment b (L.List [L.Symbol "define-fun",L.Symbol fname,L.List args,rtp,body])
      = case args of
        [] -> do
          srt@(Sort tp) <- lispToSort (pipeParser b) rtp
          expr <- lispToExprTyped b tp body
          return $ VarAssignment (UntypedVar fname tp) expr
        _ -> do
          srt@(Sort tp) <- lispToSort (pipeParser b) rtp
          withFunList b args $
            \b' tps args' -> do
              body' <- lispToExprTyped b' tp body
              return $ FunAssignment (UntypedFun fname tps tp) args' body'
    parseAssignment _ lsp = throwError $ "Invalid model entry: "++show lsp
    withFunList :: SMTPipe -> [L.Lisp]
                -> (forall arg. SMTPipe -> List Repr arg -> List PipeVar arg -> LispParse a) -> LispParse a
    withFunList b [] f = f b Nil Nil
    withFunList b ((L.List [L.Symbol v,tp]):ls) f = do
      Sort tp <- lispToSort (pipeParser b) tp
      withFunList (b { vars = Map.insert v (FunArg tp) (vars b) }) ls $
        \b' tps args -> f b' (tp ::: tps) ((UntypedVar v tp) ::: args)
    withFunList _ lsp _ = throwError $ "Invalid fun args: "++show lsp
parseGetModel _ lsp = throwError $ "Invalid model: "++show lsp

data Sort = forall (t :: Type). Sort (Repr t)
data Sorts = forall (t :: [Type]). Sorts (List Repr t)

data ParsedFunction fun
  = ParsedFunction { argumentTypeRequired :: Integer -> Bool
                   , getParsedFunction :: [Maybe Sort] -> LispParse (AnyFunction fun)
                   }

data AnyExpr e = forall (t :: Type). AnyExpr (e t)

instance GShow e => Show (AnyExpr e) where
  showsPrec p (AnyExpr x) = gshowsPrec p x

data LispParser (v :: Type -> *) (qv :: Type -> *) (fun :: ([Type],Type) -> *) (fv :: Type -> *) (lv :: Type -> *) (e :: Type -> *)
  = LispParser { parseFunction :: forall a. Maybe Sort -> T.Text
                               -> (forall args res. fun '(args,res) -> LispParse a)
                               -> (forall args res. (IsDatatype res) => Type.Datatype res -> Type.Constr res args -> LispParse a) -- constructor
                               -> (forall args res. (IsDatatype res) => Type.Datatype res -> Type.Constr res args -> LispParse a) -- constructor test
                               -> (forall t args res. (IsDatatype t) => Type.Datatype t -> Type.Field t res -> LispParse a)
                               -> LispParse a
               , parseDatatype :: forall a. T.Text
                               -> (forall dt. IsDatatype dt
                                   => Type.Datatype dt -> LispParse a)
                               -> LispParse a
               , parseVar :: forall a. Maybe Sort -> T.Text
                          -> (forall t. v t -> LispParse a)
                          -> (forall t. qv t -> LispParse a)
                          -> (forall t. fv t -> LispParse a)
                          -> (forall t. lv t -> LispParse a)
                          -> LispParse a
               , parseRecursive :: forall a. LispParser v qv fun fv lv e
                                -> Maybe Sort -> L.Lisp
                                -> (forall t. e t -> LispParse a)
                                -> LispParse a
               , registerQVar :: forall (t :: Type). T.Text -> Repr t
                              -> (qv t,LispParser v qv fun fv lv e)
               , registerLetVar :: forall (t :: Type). T.Text -> Repr t
                                -> (lv t,LispParser v qv fun fv lv e)
               }

type LispParse = Except String

-- | Spawn a new SMT solver process and create a pipe to communicate with it.
createPipe :: String -- ^ Path to the binary of the SMT solver
         -> [String] -- ^ Command line arguments to be passed to the SMT solver
         -> IO SMTPipe
createPipe solver args = do
  let cmd = (proc solver args) { std_in = CreatePipe
                               , std_out = CreatePipe
                               , std_err = Inherit
                               , close_fds = False }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  let p0 = SMTPipe { channelIn = hin
                   , channelOut = hout
                   , processHandle = Just handle
                   , names = Map.empty
                   , vars = Map.empty
                   , datatypes = emptyTypeRegistry
                   , interpolationMode = MathSATInterpolation }
  putRequest p0 (L.List [L.Symbol "get-info"
                        ,L.Symbol ":name"])
  resp <- parseResponse p0
  case resp of
    L.List [L.Symbol ":name",L.String name] -> case name of
      "Z3" -> return $ p0 { interpolationMode = Z3Interpolation [] [] }
      _ -> return p0
    _ -> return p0

-- | Create a SMT pipe by giving the input and output handle.
createPipeFromHandle :: Handle -- ^ Input handle
                     -> Handle -- ^ Output handle
                     -> IO SMTPipe
createPipeFromHandle hin hout = do
  return SMTPipe { channelIn = hin
                 , channelOut = hout
                 , processHandle = Nothing
                 , names = Map.empty
                 , vars = Map.empty
                 , datatypes = emptyTypeRegistry
                 , interpolationMode = MathSATInterpolation }

lispToExprUntyped :: SMTPipe -> L.Lisp
                  -> (forall (t::Type). Expr SMTPipe t -> LispParse a)
                  -> LispParse a
lispToExprUntyped st l res = lispToExprWith (pipeParser st) Nothing l $
                             \e -> res (PipeExpr e)

lispToExprTyped :: SMTPipe -> Repr t -> L.Lisp -> LispParse (Expr SMTPipe t)
lispToExprTyped st tp l = lispToExprWith (pipeParser st) (Just (Sort tp)) l $
                          \e -> case geq tp (getType e) of
                          Just Refl -> return (PipeExpr e)
                          Nothing -> throwError $ show l++" has type "++show (getType e)++", but "++show tp++" was expected."

pipeParser :: SMTPipe
           -> LispParser PipeVar PipeVar PipeFun PipeVar PipeVar (Expr SMTPipe)
pipeParser st = parse
  where
  parse = LispParser { parseFunction = \srt name fun con test field
                                       -> case T.stripPrefix "is-" name of
                                       Just con -> case Map.lookup name (allConstructors $ datatypes st) of
                                         Just (AnyConstr dt con) -> test dt con
                                         _ -> throwError $ "Unknown constructor: "++show name
                                       Nothing -> case Map.lookup name (allConstructors $ datatypes st) of
                                         Just (AnyConstr dt c) -> con dt c
                                         Nothing -> case Map.lookup name (allFields $ datatypes st) of
                                           Just (AnyField dt f) -> field dt f
                                           Nothing -> case Map.lookup name (vars st) of
                                             Just (Fun arg tp)
                                               -> fun (UntypedFun name arg tp)
                                             _ -> throwError $ "Unknown symbol "++show name
                     , parseDatatype = \name res -> case Map.lookup name (allDatatypes $ datatypes st) of
                                         Just (AnyDatatype p) -> res p
                                         _ -> throwError $ "Unknown datatype "++show name
                     , parseVar = \srt name v qv fv lv -> case Map.lookup name (vars st) of
                                    Just (Var tp)
                                      -> v (UntypedVar name tp)
                                    Just (QVar tp)
                                      -> qv (UntypedVar name tp)
                                    Just (FunArg tp)
                                      -> fv (UntypedVar name tp)
                                    Just (LVar tp)
                                      -> lv (UntypedVar name tp)
                                    _ -> throwError $ "Unknown variable "++show name
                     , parseRecursive = \parse srt l res -> lispToExprWith parse srt l $
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

lispToExprWith :: (GShow fun,GShow e,GetFunType fun,GetType e)
               => LispParser v qv fun fv lv e
               -> Maybe Sort
               -> L.Lisp
               -> (forall (t :: Type).
                   Expression v qv fun fv lv e t
                   -> LispParse a)
               -> LispParse a
lispToExprWith p hint (runExcept . lispToConstant -> Right (AnyValue val)) res
  = res (Const val)
lispToExprWith p hint (L.Symbol sym) res
  = parseVar p hint sym (res . Expr.Var) (res . Expr.QVar) (res . Expr.FVar) (res . Expr.LVar) `catchError`
    (\_ -> do
        parsed <- lispToFunction p hint (L.Symbol sym)
        AnyFunction f <- getParsedFunction parsed []
        case getFunType f of
          (Nil,_) -> res $ App f Nil
          _ -> throwError $ "Arguments expected for function "++show sym)
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
    \np args' -> parseRecursive np np (Just (Sort BoolRepr)) body $
                 \body' -> case getType body' of
                 BoolRepr -> res (Quantification Forall args' body')
lispToExprWith p hint (L.List [L.Symbol "exists",L.List args,body]) res
  = mkQuant p args $
    \np args' -> parseRecursive np np (Just (Sort BoolRepr)) body $
                 \body' -> case getType body' of
                 BoolRepr -> res (Quantification Exists args' body')
lispToExprWith p hint (L.List [L.Symbol "let",L.List args,body]) res
  = mkLet p args $
    \np args' -> parseRecursive np np hint body $
                 \body' -> res (Let args' body')
lispToExprWith p hint (L.List [L.Symbol "as",expr,tp]) res = do
  srt <- lispToSort p tp
  lispToExprWith p (Just srt) expr res
lispToExprWith p hint (L.List (fun:args)) res = do
  parsed <- lispToFunction p hint fun
  args' <- matchList (argumentTypeRequired parsed) 0 args
  let hints = fmap (\arg -> case arg of
                      Left _ -> Nothing
                      Right (AnyExpr e) -> Just $ Sort (getType e)
                   ) args'
  AnyFunction fun' <- getParsedFunction parsed hints
  let (argTps,ret) = getFunType fun'
  args'' <- catchError (makeList p argTps args') $
            \err -> throwError $ "While parsing arguments of function: "++
                    show fun'++": "++err
  res $ App fun' args''
  where
    matchList _ _ [] = return []
    matchList f i (e:es) = if f i
                           then parseRecursive p p Nothing e
                                (\e' -> do
                                     rest <- matchList f (i+1) es
                                     return $ (Right (AnyExpr e')):rest)
                           else do
                             rest <- matchList f (i+1) es
                             return $ (Left e):rest
    makeList :: (GShow e,GetType e) => LispParser v qv fun fv lv e
             -> List Repr arg -> [Either L.Lisp (AnyExpr e)] -> LispParse (List e arg)
    makeList _ Nil [] = return Nil
    makeList _ Nil _  = throwError $ "Too many arguments to function."
    makeList p (tp ::: args) (e:es) = case e of
      Right (AnyExpr e') -> do
        r <- case geq tp (getType e') of
           Just Refl -> return e'
           Nothing -> throwError $ "Argument "++gshowsPrec 11 e' ""++" has wrong type."
        rs <- makeList p args es
        return (r ::: rs)
      Left l -> parseRecursive p p (Just $ Sort tp) l $
                \e' -> do
                  r <- case geq tp (getType e') of
                     Just Refl -> return e'
                     Nothing -> throwError $ "Argument "++gshowsPrec 11 e' ""++" has wrong type."
                  rs <- makeList p args es
                  return (r ::: rs)
    makeList _ (_ ::: _) [] = throwError $ "Not enough arguments to function."
lispToExprWith _ _ lsp _ = throwError $ "Invalid SMT expression: "++show lsp

mkQuant :: LispParser v qv fun fv lv e -> [L.Lisp]
        -> (forall arg. LispParser v qv fun fv lv e -> List qv arg -> LispParse a)
        -> LispParse a
mkQuant p [] f = f p Nil
mkQuant p ((L.List [L.Symbol name,sort]):args) f = do
  Sort srt <- lispToSort p sort
  let (qvar,np) = registerQVar p name srt
  mkQuant np args $ \p args -> f p (qvar ::: args)
mkQuant _ lsp _ = throwError $ "Invalid forall/exists parameter: "++show lsp

mkLet :: GetType e
      => LispParser v qv fun fv lv e -> [L.Lisp]
         -> (forall arg. LispParser v qv fun fv lv e
             -> List (LetBinding lv e) arg -> LispParse a)
         -> LispParse a
mkLet p [] f = f p Nil
mkLet p ((L.List [L.Symbol name,expr]):args) f
  = parseRecursive p p Nothing expr $
    \expr' -> do
      let (lvar,np) = registerLetVar p name (getType expr')
      mkLet np args $ \p args -> f p ((LetBinding lvar expr') ::: args)
mkLet _ lsp _ = throwError $ "Invalid let parameter: "++show lsp

withEq :: Repr t -> [b]
       -> (forall n. Natural n -> List Repr (AllEq t n) -> a)
       -> a
withEq tp [] f = f Zero Nil
withEq tp (_:xs) f = withEq tp xs $
                     \n args -> f (Succ n) (tp ::: args)
                                             
lispToFunction :: LispParser v qv fun fv lv e
               -> Maybe Sort -> L.Lisp -> LispParse (ParsedFunction fun)
lispToFunction _ _ (L.Symbol "=")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort tp):_ -> withEq tp args $
                           \n args
                           -> return $ AnyFunction (Eq tp n)
       _ -> throwError $ "Cannot derive type of = parameters.")
lispToFunction _ _ (L.Symbol "distinct")
  = return $ ParsedFunction (==0)
    (\args -> case args of
       Just (Sort tp):_ -> withEq tp args $
                           \n args' -> return $ AnyFunction (Distinct tp n)
       _ -> throwError $ "Cannot derive type of \"distinct\" parameters.")
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
              Nothing -> throwError $ "Could not derive type of the array index in map function."
            _ -> throwError $ "Could not derive type of the array index in map function."
        argSorts <- mapM (\prx -> case prx of
                            Nothing -> return Nothing
                            Just srt -> do
                              (_,elsrt) <- case asArraySort srt of
                                Just srt' -> return srt'
                                Nothing -> throwError $ "Argument to map function isn't an array."
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
lispToFunction _ _ (L.Symbol "^") = return $ ParsedFunction (const False)
                                    (\_ -> return $ AnyFunction (ArithIntBin Exp))
lispToFunction _ _ (L.Symbol "/") = return $ ParsedFunction (const False)
                                    (\_ -> return $ AnyFunction Divide)
lispToFunction _ sort (L.Symbol "abs") = case sort of
  Just (Sort tp) -> case tp of
    IntRepr -> return $ ParsedFunction (const False) (\_ -> return $ AnyFunction (Abs NumInt))
    RealRepr -> return $ ParsedFunction (const False) (\_ -> return $ AnyFunction (Abs NumReal))
    exp -> throwError $ "abs function can't have type "++show exp
  Nothing -> return $ ParsedFunction (==0) $
             \args -> case args of
                [Just (Sort tp)] -> case tp of
                  IntRepr -> return $ AnyFunction (Abs NumInt)
                  RealRepr -> return $ AnyFunction (Abs NumReal)
                  srt -> throwError $ "abs can't take argument of type "++show srt
                _ -> throwError $ "abs function takes exactly one argument."
lispToFunction _ _ (L.Symbol "not")
  = return $ ParsedFunction (const False) (\_ -> return $ AnyFunction Not)
lispToFunction _ _ (L.Symbol "and") = return $ lispToLogicFunction And
lispToFunction _ _ (L.Symbol "or") = return $ lispToLogicFunction Or
lispToFunction _ _ (L.Symbol "xor") = return $ lispToLogicFunction XOr
lispToFunction _ _ (L.Symbol "=>") = return $ lispToLogicFunction Implies
lispToFunction _ _ (L.List [L.Symbol "_",
                            L.Symbol "at-least",
                            L.Number (L.I n)])
  = return $ lispToLogicFunction (AtLeast n)
lispToFunction _ _ (L.List [L.Symbol "_",
                            L.Symbol "at-most",
                            L.Number (L.I n)])
  = return $ lispToLogicFunction (AtMost n)
lispToFunction _ _ (L.Symbol "to_real")
  = return $ ParsedFunction (const False) (\_ -> return $ AnyFunction ToReal)
lispToFunction _ _ (L.Symbol "to_int")
  = return$ ParsedFunction (const False) (\_ -> return $ AnyFunction ToInt)
lispToFunction _ sort (L.Symbol "ite") = case sort of
  Just (Sort tp)
    -> return $ ParsedFunction (const False)
       (\_ -> return $ AnyFunction (ITE tp))
  Nothing -> return $ ParsedFunction (==1) $
             \args -> case args of
               [_,Just (Sort tp),_]
                 -> return $ AnyFunction (ITE tp)
               _ -> throwError $ "Invalid arguments to ite function."
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
         srt -> throwError $ "Invalid argument type to select function: "++show srt
       _ -> throwError $ "Invalid arguments to select function.")
lispToFunction _ sort (L.Symbol "store") = case sort of
  Just (Sort srt) -> case srt of
    ArrayRepr idx el
      -> return (ParsedFunction (const False)
                 (\_ -> return $ AnyFunction
                        (Store idx el)))
    srt' -> throwError $ "Invalid argument types to store function: "++show srt'
  Nothing -> return $ ParsedFunction (==0)
             (\args -> case args of
                Just (Sort arr):_ -> case arr of
                  ArrayRepr idx el
                    -> return $ AnyFunction
                       (Store idx el)
                  srt -> throwError $ "Invalid first argument type to store function: "++show srt
                _ -> throwError $ "Invalid arguments to store function.")
lispToFunction r sort (L.List [L.Symbol "as",L.Symbol "const",sig]) = do
  Sort rsig <- case sort of
    Just srt -> return srt
    Nothing -> lispToSort r sig
  case rsig of
    ArrayRepr idx el
      -> return $ ParsedFunction (const False)
         (\_ -> return $ AnyFunction (ConstArray idx el))
    _ -> throwError $ "Invalid signature for (as const ...) function."
lispToFunction _ sort (L.Symbol "concat")
  = return $ ParsedFunction (const True)
    (\args -> case args of
       [Just (Sort tp1),Just (Sort tp2)]
         -> case (tp1,tp2) of
         (BitVecRepr sz1,BitVecRepr sz2)
           -> return $ AnyFunction (Concat sz1 sz2)
         _ -> throwError $ "Invalid argument types to concat function."
       _ -> throwError $ "Wrong number of arguments to concat function.")
lispToFunction _ sort (L.List [L.Symbol "_",L.Symbol "extract",L.Number (L.I end),L.Number (L.I start)])
  = return $ ParsedFunction (==0)
    (\args -> case args of
       [Just (Sort srt)] -> case srt of
         BitVecRepr size
           | start <= end &&
             end <= bwSize size
             -> case TL.someNatVal start of
               Just (TL.SomeNat start')
                 -> case TL.someNatVal (end-start+1) of
                      Just (TL.SomeNat len')
                        -> return $ AnyFunction
                            (Extract size (bw start')
                              (bw len'))
           | otherwise -> throwError $ "Invalid extract parameters."
         srt -> throwError $ "Invalid type of extract argument: "++show srt
       _ -> throwError $ "Wrong number of arguments to extract function.")
lispToFunction _ sort (L.List [L.Symbol "_",L.Symbol "divisible",L.Number (L.I div)])
  = return $ ParsedFunction (const False)
    (\_ -> return $ AnyFunction (Divisible div))
lispToFunction _ sort (L.List (L.Symbol "_":
                               L.Symbol (T.stripPrefix "pb" -> Just op):
                               coeff)) = do
  coeffNum <- mapM (\c -> case c of
                       L.Number (L.I c') -> return c'
                       _ -> throwError $ "Invalid pseudo-boolean coefficient: "++show c
                   ) coeff
  rop <- case op of
    "eq" -> return PBEq
    "le" -> return PBLe
    "ge" -> return PBGe
    _ -> throwError $ "Invalid pseudo-boolean operator: "++show op
  case coeffNum of
    [] -> throwError $ "Invalid number of pseudo-boolean coefficients"
    res:coeff' -> List.reifyCList coeff' $
                  \rcoeff -> return $ ParsedFunction (const False)
                             (\_ -> return $ AnyFunction $
                                    PseudoBoolean rop rcoeff res)
lispToFunction rf sort (L.List [sym,lispToList -> Just sig,tp]) = do
  nsort <- lispToSort rf tp
  fun <- lispToFunction rf (Just nsort) sym
  rsig <- lispToSorts rf sig $
          \sig' -> return $ runIdentity $ List.toList (\tp -> return $ Just (Sort tp)) sig'
  return $ ParsedFunction (const False) (\_ -> getParsedFunction fun rsig)
lispToFunction rf sort (L.Symbol name)
  = parseFunction rf sort name
    (p . Expr.Fun)
    getCon
    getTest
    getField
  where
    p f = return $ ParsedFunction (const False) (const (return $ AnyFunction f))

    getCon :: IsDatatype dt
           => Datatype dt -> Constr dt csig
           -> LispParse (ParsedFunction fun)
    getCon (dt :: Datatype dt) con
      = return $
        ParsedFunction (case sort of
                           Just _ -> const False
                           Nothing -> \i -> List.indexDyn (fields con) i $
                                            \f -> not $ Set.null $
                                                  containedParameter
                                                  (fieldType f) Set.empty)
        (\argSorts -> case sort of
            Just (Sort (DataRepr (dt'::Datatype dt') par)) -> case eqT :: Maybe (dt :~: dt') of
              Nothing -> throwError "Type mismatch"
              Just Refl -> return $ AnyFunction $ Expr.Constructor dt par con
            Nothing -> case inferArgs argSorts (fields con) IMap.empty of
              Nothing -> throwError "Cannot infer parameter type"
              Just mp -> case fullArgs 0 (IMap.toList mp) (parameters dt) $
                              \par -> AnyFunction $ Expr.Constructor
                                      dt par con of
                           Nothing -> throwError "Cannot infer parameter type"
                           Just res -> return res)

    getTest :: IsDatatype dt => Datatype dt -> Constr dt csig
            -> LispParse (ParsedFunction fun)
    getTest (dt :: Datatype dt) con
      = return $
        ParsedFunction (\i -> i==0 && (case parameters dt of
                                         Zero -> False
                                         _ -> True))
        (\argSorts -> case parameters dt of
            Zero -> return $ AnyFunction $ Expr.Test dt Nil con
            _ -> case argSorts of
              [Just (Sort (DataRepr (dt'::Datatype dt') par))] -> case eqT :: Maybe (dt :~: dt') of
                Nothing -> throwError "Type mismatch"
                Just Refl -> return $ AnyFunction $ Expr.Test dt par con)

    getField :: IsDatatype dt => Datatype dt -> Field dt tp
             -> LispParse (ParsedFunction fun)
    getField (dt::Datatype dt) f
      = return $
        ParsedFunction (\i -> i==0 && (case parameters dt of
                                         Zero -> False
                                         _ -> True))
        (\argSorts -> case parameters dt of
            Zero -> return $ AnyFunction $ Expr.Field dt Nil f
            _ -> case argSorts of
              [Just (Sort (DataRepr (dt'::Datatype dt') par))] -> case eqT :: Maybe (dt :~: dt') of
                Nothing -> throwError "Type mismatch"
                Just Refl -> return $ AnyFunction $ Expr.Field dt par f
              _ -> throwError "Cannot infer field type")
                                       
    inferArgs :: IsDatatype dt => [Maybe Sort] -> List (Field dt) tps -> IntMap Sort -> Maybe (IntMap Sort)
    inferArgs [] Nil mp = Just mp
    inferArgs (Nothing : args) (_ ::: fs) mp = inferArgs args fs mp
    inferArgs (Just (Sort arg) : args) (f ::: fs) mp = do
      mp1 <- typeInference arg (fieldType f)
             (\p tp cmp -> let p' = fromInteger $ naturalToInteger p
                           in case IMap.lookup p' cmp of
                                Nothing -> Just $ IMap.insert p' (Sort tp) cmp
                                Just (Sort tp') -> do
                                  Refl <- geq tp tp'
                                  return cmp) mp
      inferArgs args fs mp1
lispToFunction _ _ lsp = throwError $ "Unknown function: "++show lsp

fullArgs :: Int -> [(Int,Sort)] -> Natural len -> (forall tps. (List.Length tps ~ len) => List Repr tps -> a) -> Maybe a
fullArgs cpos [] Zero f = Just $ f Nil
fullArgs cpos ((pos,Sort srt):srts) (Succ n) f
  = if cpos==pos
    then fullArgs (cpos+1) srts n $ \lst -> f (srt ::: lst)
    else Nothing
fullArgs _ _ _ _ = Nothing

lispToOrdFunction :: OrdOp -> LispParse (ParsedFunction fun)
lispToOrdFunction op
  = return (ParsedFunction (==0)
            (\argSrt -> case argSrt of
               (Just (Sort srt)):_ -> case srt of
                 IntRepr -> return $ AnyFunction (Ord NumInt op)
                 RealRepr -> return $ AnyFunction (Ord NumReal op)
                 srt' -> throwError $ "Invalid argument to "++show op++" function: "++show srt'
               _ -> throwError $ "Wrong number of arguments to "++show op++" function."))

lispToArithFunction :: Maybe Sort -> ArithOp -> LispParse (ParsedFunction fun)
lispToArithFunction sort op = case sort of
  Just (Sort tp) -> case tp of
    IntRepr -> return (ParsedFunction (const False)
                       (\args -> withEq IntRepr args $
                                 \n _ -> return $ AnyFunction (Arith NumInt op n)))
    RealRepr -> return (ParsedFunction (const False)
                        (\args -> withEq RealRepr args $
                                 \n _ -> return $ AnyFunction (Arith NumReal op n)))
    srt -> throwError $ "Invalid type of "++show op++" function: "++show srt
  Nothing -> return (ParsedFunction (==0)
                     (\argSrt -> case argSrt of
                        (Just (Sort srt)):_ -> case srt of
                           IntRepr -> withEq IntRepr argSrt $
                                      \n args
                                      -> return $ AnyFunction (Arith NumInt op n)
                           RealRepr -> withEq RealRepr argSrt $
                                       \n args
                                       -> return $ AnyFunction (Arith NumReal op n)
                           srt' -> throwError $ "Wrong argument type to "++show op++" function: "++show srt'
                        _ -> throwError $ "Wrong number of arguments to "++show op++" function."))

lispToLogicFunction :: LogicOp -> ParsedFunction fun
lispToLogicFunction op
  = ParsedFunction (const False)
    (\args -> withEq BoolRepr args $
       \n args
       -> return $ AnyFunction (Logic op n))

lispToBVCompFunction :: BVCompOp -> ParsedFunction fun
lispToBVCompFunction op
  = ParsedFunction (==0)
    (\args -> case args of
       [Just (Sort srt),_] -> case srt of
         BitVecRepr bw -> return $ AnyFunction (BVComp op bw)
         srt -> throwError $ "Invalid argument type to "++show op++" function: "++show srt
       _ -> throwError $ "Wrong number of arguments to "++show op++" function.")

lispToBVBinFunction :: Maybe Sort -> BVBinOp -> LispParse (ParsedFunction fun)
lispToBVBinFunction (Just (Sort srt)) op = case srt of
  BitVecRepr bw -> return $ ParsedFunction (const False) $
                   \_ -> return $ AnyFunction (BVBin op bw)
  srt' -> throwError $ "Invalid argument type to "++show op++" function: "++show srt'
lispToBVBinFunction Nothing op
  = return $ ParsedFunction (==0) $
    \args -> case args of
      [Just (Sort srt),_] -> case srt of
        BitVecRepr bw -> return $ AnyFunction (BVBin op bw)
        srt' -> throwError $ "Invalid argument type to "++show op++" function: "++show srt'
      _ -> throwError $ "Wrong number of arguments to "++show op++" function."

lispToBVUnFunction :: Maybe Sort -> BVUnOp -> LispParse (ParsedFunction fun)
lispToBVUnFunction (Just (Sort srt)) op = case srt of
  BitVecRepr bw -> return $ ParsedFunction (const False) $
                   \_ -> return $ AnyFunction (BVUn op bw)
  srt' -> throwError $ "Invalid argument type to "++show op++" function: "++show srt'
lispToBVUnFunction Nothing op
  = return $ ParsedFunction (==0) $
    \args -> case args of
      [Just (Sort srt)] -> case srt of
        BitVecRepr bw -> return $ AnyFunction (BVUn op bw)
        srt' -> throwError $ "Invalid argument type to "++show op++" function: "++show srt'
      _ -> throwError $ "Wrong number of arguments to "++show op++" function."

mkMap :: List Repr idx -> AnyFunction fun -> AnyFunction fun
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

lispToSort :: LispParser v qv fun fv lv e -> L.Lisp -> LispParse Sort
lispToSort _ (L.Symbol "Bool") = return (Sort BoolRepr)
lispToSort _ (L.Symbol "Int") = return (Sort IntRepr)
lispToSort _ (L.Symbol "Real") = return (Sort RealRepr)
lispToSort r (L.List ((L.Symbol "Array"):tps)) = do
  Sort rtp' <- lispToSort r rtp
  lispToSorts r idx (\idx' -> return $ Sort (ArrayRepr idx' rtp'))
  where
    (idx,rtp) = splitLast tps
    splitLast [x] = ([],x)
    splitLast (x:xs) = let (xs',y') = splitLast xs
                       in (x:xs',y')
lispToSort _ (L.List [L.Symbol "_",L.Symbol "BitVec",L.Number (L.I n)])
  = case TL.someNatVal n of
      Just (TL.SomeNat w) -> return (Sort (BitVecRepr (bw w)))
lispToSort r (L.Symbol name)
  = parseDatatype r name $ \dt -> case geq (parameters dt) Zero of
  Just Refl -> return $ Sort (DataRepr dt Nil)
  Nothing -> throwError $ "Wrong sort for type "++show name
lispToSort r (L.List (L.Symbol name:args))
  = parseDatatype r name $
    \dt -> lispToSorts r args $
           \args' -> case geq (List.length args') (parameters dt) of
             Just Refl -> return $ Sort (DataRepr dt args')
             Nothing -> throwError $ "Wrong number of arguments for type "++show name
lispToSort _ lsp = throwError $ "Invalid SMT type: "++show lsp

lispToSorts :: LispParser v qv fun fv lv e -> [L.Lisp]
            -> (forall (arg :: [Type]). List Repr arg -> LispParse a)
            -> LispParse a
lispToSorts _ [] f = f Nil
lispToSorts r (x:xs) f = do
  Sort tp <- lispToSort r x
  lispToSorts r xs $
    \tps -> f (tp ::: tps)

lispToValue :: SMTPipe -> Maybe Sort -> L.Lisp -> LispParse AnyValue
lispToValue b hint l = case runExcept $ lispToConstant l of
  Right r -> return r
  Left e -> lispToConstrConstant b hint l

lispToConstant :: L.Lisp -> LispParse AnyValue
lispToConstant (L.Symbol "true") = return (AnyValue (BoolValue True))
lispToConstant (L.Symbol "false") = return (AnyValue (BoolValue False))
lispToConstant (lispToNumber -> Just n) = return (AnyValue (IntValue n))
lispToConstant (lispToReal -> Just n) = return (AnyValue (RealValue n))
lispToConstant (lispToBitVec -> Just (val,sz))
  = case TL.someNatVal sz of
  Just (TL.SomeNat w) -> return (AnyValue (BitVecValue val (bw w)))
lispToConstant l = throwError $ "Invalid constant "++show l

lispToConstrConstant :: SMTPipe -> Maybe Sort -> L.Lisp
                     -> LispParse AnyValue
lispToConstrConstant b hint sym = do
  (constr,args) <- case sym of
    L.Symbol s -> return (s,[])
    L.List ((L.Symbol s):args) -> return (s,args)
    _ -> throwError $ "Invalid constant: "++show sym
  case Map.lookup constr (allConstructors $ datatypes b) of
    Just (AnyConstr (dt::Datatype dt) con)
      -> makeList (case hint of
                     Just (Sort (DataRepr dt' par))
                       -> IMap.fromList $ runIdentity $ List.toListIndex
                          (\i srt -> return (fromInteger $ naturalToInteger i,
                                             Sort srt))
                          par
                     Nothing -> IMap.empty) (fields con) args $
         \par rargs -> case fullArgs 0 (IMap.toList par) (parameters dt) $
                            \rpar -> case instantiate
                                          (runIdentity $ List.mapM
                                           (return.fieldType) (fields con))
                                          rpar of
                              (tsig,Refl) -> do
                                Refl <- geq tsig
                                        (runIdentity $ List.mapM
                                         (return.getType) rargs)
                                return $ AnyValue $ DataValue $
                                  construct rpar con rargs of
           Just (Just res) -> return res
           _ -> throwError "Type error in constructor"
    Nothing -> throwError $ "Invalid constructor "++show constr
  where
    makeList :: IsDatatype dt
             => IntMap Sort
             -> List (Type.Field dt) arg
             -> [L.Lisp]
             -> (forall narg. List.Length arg ~ List.Length narg
                 => IntMap Sort -> List Value narg -> LispParse a)
             -> LispParse a
    makeList par Nil [] res = res par Nil
    makeList _ Nil _ _ = throwError $ "Too many arguments to constructor."
    makeList par (f ::: fs) (l:ls) res
      = partialInstantiation (fieldType f)
        (\n g -> do
            Sort parTp <- IMap.lookup (fromInteger $ naturalToInteger n) par
            return $ g parTp) $
        \ftp -> do
          AnyValue v <- lispToValue b (Just $ Sort ftp) l
          case typeInference ftp (valueType v)
               (\pos ptp cpar -> let pos' = fromInteger $ naturalToInteger pos
                                 in case IMap.lookup pos' cpar of
                   Just (Sort ptp') -> case geq ptp ptp' of
                     Just Refl -> return cpar
                     Nothing -> Nothing
                   Nothing -> return $ IMap.insert pos' (Sort ptp) cpar) par of
            Nothing -> throwError "Type error in constructor arguments."
            Just npar -> makeList npar fs ls $
                         \rpar rest -> res rpar (v ::: rest)
    makeList _ (_ ::: _) [] _ = throwError $ "Not enough arguments to constructor."

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
lispToReal (L.List [L.Symbol "-",v]) = do
  r <- lispToReal v
  return $ -r
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

exprToLisp :: TypeRegistry T.Text T.Text T.Text
           -> Expression PipeVar PipeVar PipeFun PipeVar PipeVar (Expr SMTPipe) t
           -> L.Lisp
exprToLisp reg
  = runIdentity . exprToLispWith
    (\(UntypedVar v _) -> return $ L.Symbol v)
    (\(UntypedVar v _) -> return $ L.Symbol v)
    (\(UntypedFun v _ _) -> return $ L.Symbol v)
    (\dt con -> case Map.lookup (AnyConstr dt con) (revConstructors reg) of
        Just sym -> return $ L.Symbol sym)
    (\dt con -> case Map.lookup (AnyConstr dt con) (revConstructors reg) of
        Just sym -> return $ L.Symbol $ T.append "is-" sym)
    (\dt field -> case Map.lookup (AnyField dt field) (revFields reg) of
        Just sym -> return $ L.Symbol sym)
    (\(UntypedVar v _) -> return $ L.Symbol v)
    (\(UntypedVar v _) -> return $ L.Symbol v)
    (\(PipeExpr v) -> return $ exprToLisp reg v)

exprToLispWith :: (Monad m,GetType v,GetType qv,GetType fv,GetType lv,GetFunType fun,GetType e)
               => (forall (t' :: Type).
                   v t' -> m L.Lisp)                         -- ^ variables
               -> (forall (t' :: Type).
                   qv t' -> m L.Lisp)                        -- ^ quantified variables
               -> (forall (arg :: [Type]) (res :: Type).
                   fun '(arg,res) -> m L.Lisp) -- ^ functions
               -> (forall (arg :: [Type]) (dt :: [Type] -> (Type -> *) -> *).
                   IsDatatype dt =>
                   Datatype dt -> Type.Constr dt arg -> m L.Lisp)     -- ^ constructor
               -> (forall (arg :: [Type]) (dt :: [Type] -> (Type -> *) -> *).
                   IsDatatype dt =>
                   Datatype dt -> Type.Constr dt arg -> m L.Lisp)     -- ^ constructor tests
               -> (forall (dt :: [Type] -> (Type -> *) -> *) (res :: Type).
                   IsDatatype dt =>
                   Datatype dt -> Type.Field dt res -> m L.Lisp) -- ^ field accesses
               -> (forall t.
                   fv t -> m L.Lisp)                                              -- ^ function variables
               -> (forall t.
                   lv t -> m L.Lisp)                                              -- ^ let variables
               -> (forall (t' :: Type).
                   e t' -> m L.Lisp)                         -- ^ sub expressions
               -> Expression v qv fun fv lv e t
               -> m L.Lisp
exprToLispWith f _ _ _ _ _ _ _ _ (Expr.Var v) = f v
exprToLispWith _ f _ _ _ _ _ _ _ (Expr.QVar v) = f v
exprToLispWith _ _ _ _ _ _ f _ _ (Expr.FVar v) = f v
exprToLispWith _ _ _ _ _ _ _ f _ (Expr.LVar v) = f v
-- This is a special case because the argument order is different
exprToLispWith _ _ f g h i _ _ j (Expr.App (Store _ _) (arr ::: val ::: idx)) = do
  arr' <- j arr
  idx' <- List.toList j idx
  val' <- j val
  return $ L.List ((L.Symbol "store"):arr':idx'++[val'])
exprToLispWith _ _ f g h i _ _ j e@(Expr.App fun args) = do
  let needAs = case fun of
        Constructor dt par con -> not $ determines dt con
        _ -> False
  args' <- List.toList j args
  sym <- functionSymbol f g h i fun
  let c = case args' of
            [] -> sym
            _ -> L.List $ sym:args'
      rc = if needAs
           then L.List [L.Symbol "as",c,typeSymbol Set.empty (getType e)]
           else c
  return rc

exprToLispWith _ _ _ f _ _ _ _ _ (Expr.Const val) = valueToLisp f val
exprToLispWith _ _ f g h i _ _ _ (Expr.AsArray fun) = do
  sym <- functionSymbolWithSig f g h i fun
  return $  L.List [L.Symbol "_"
                   ,L.Symbol "as-array"
                   ,sym]
exprToLispWith _ f _ _ _ _ _ _ g (Expr.Quantification q args body) = do
  bind <- List.toList (\arg -> do
                          sym <- f arg
                          return $ L.List [sym,typeSymbol Set.empty $ getType arg]
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
                => Datatype tp -> Type.Constr tp arg -> m L.Lisp)
            -> Value t -> m L.Lisp
valueToLisp _ (BoolValue True) = return $ L.Symbol "true"
valueToLisp _ (BoolValue False) = return $ L.Symbol "false"
valueToLisp _ (IntValue n) = return $ numToLisp n
valueToLisp _ (RealValue n)
  = return $ L.List [L.Symbol "/"
                    ,numToLisp $ numerator n
                    ,numToLisp $ denominator n]
valueToLisp _ (BitVecValue n bw)
  = return $ L.List [L.Symbol "_"
                    ,L.Symbol (T.pack $ "bv"++show rn)
                    ,L.Number $ L.I bw']
  where
    bw' = bwSize bw
    rn = n `mod` 2^bw'
valueToLisp f v@(DataValue val) = do
  let (dt,par) = datatypeGet val
  case deconstruct val of
    ConApp { constructor = con
           , arguments = args } -> do
      let needAs = not $ determines dt con
      con' <- f dt con
      args' <- List.toList (valueToLisp f) args
      let c = case args' of
                [] -> con'
                xs -> L.List (con' : xs)
          rc = if needAs
               then L.List [L.Symbol "as",c,typeSymbol Set.empty
                                            (getType v)]
               else c
      return rc

isOverloaded :: Function fun sig -> Bool
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

functionSymbol :: (Monad m,GetFunType fun)
               => (forall (arg' :: [Type]) (res' :: Type).
                   fun '(arg',res') -> m L.Lisp) -- ^ How to render user functions
               -> (forall (arg' :: [Type]) (dt :: [Type] -> (Type -> *) -> *).
                   IsDatatype dt =>
                   Datatype dt -> Type.Constr dt arg' -> m L.Lisp)    -- ^ How to render constructor applications
               -> (forall (arg' :: [Type]) (dt :: [Type] -> (Type -> *) -> *).
                   IsDatatype dt =>
                   Datatype dt -> Type.Constr dt arg' -> m L.Lisp)    -- ^ How to render constructor tests
               -> (forall (dt :: [Type] -> (Type -> *) -> *) (res' :: Type).
                   IsDatatype dt =>
                   Datatype dt -> Type.Field dt res' -> m L.Lisp)          -- ^ How to render field acceses
               -> Function fun '(arg,res) -> m L.Lisp
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
functionSymbol _ _ _ _ (ArithIntBin Exp) = return $ L.Symbol "^"
functionSymbol _ _ _ _ Divide = return $ L.Symbol "/"
functionSymbol _ _ _ _ (Abs _) = return $ L.Symbol "abs"
functionSymbol _ _ _ _ Not = return $ L.Symbol "not"
functionSymbol _ _ _ _ (Logic And _) = return $ L.Symbol "and"
functionSymbol _ _ _ _ (Logic Or _) = return $ L.Symbol "or"
functionSymbol _ _ _ _ (Logic XOr _) = return $ L.Symbol "xor"
functionSymbol _ _ _ _ (Logic Implies _) = return $ L.Symbol "=>"
functionSymbol _ _ _ _ (Logic (AtLeast n) _)
  = return $ L.List [L.Symbol "_",L.Symbol "at-least",L.Number $ L.I n]
functionSymbol _ _ _ _ (Logic (AtMost n) _)
  = return $ L.List [L.Symbol "_",L.Symbol "at-most",L.Number $ L.I n]
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
                    ,typeSymbol Set.empty (ArrayRepr idx el)]
functionSymbol _ _ _ _ (Concat _ _) = return $ L.Symbol "concat"
functionSymbol _ _ _ _ (Extract bw start len)
  = return $ L.List [L.Symbol "_"
                    ,L.Symbol "extract"
                    ,L.Number $ L.I $ start'+len'-1
                    ,L.Number $ L.I start']
  where
    start' = bwSize start
    len' = bwSize len
functionSymbol _ g _ _ (Constructor dt par con) = g dt con
functionSymbol _ _ h _ (Test dt par con) = h dt con
functionSymbol _ _ _ i (Expr.Field dt par f) = i dt f
functionSymbol _ _ _ _ (Divisible n) = return $ L.List [L.Symbol "_"
                                                       ,L.Symbol "divisible"
                                                       ,L.Number $ L.I n]
functionSymbol _ _ _ _ (PseudoBoolean op coeff res)
  = return $ L.List (L.Symbol "_":
                     L.Symbol (case op of
                                 PBEq -> "pbeq"
                                 PBLe -> "pble"
                                 PBGe -> "pbge"):
                     (L.Number $ L.I res):
                     (fmap (L.Number . L.I) $ List.toListC coeff))

functionSymbolWithSig :: (Monad m,GetFunType fun)
                      => (forall (arg' :: [Type]) (res' :: Type).
                          fun '(arg',res') -> m L.Lisp) -- ^ How to render user functions
                      -> (forall (arg' :: [Type])
                          (dt :: [Type] -> (Type -> *) -> *).
                          IsDatatype dt =>
                          Datatype dt -> Type.Constr dt arg' -> m L.Lisp)    -- ^ How to render constructor applications
                      -> (forall (arg' :: [Type])
                          (dt :: [Type] -> (Type -> *) -> *).
                          IsDatatype dt =>
                          Datatype dt -> Type.Constr dt arg' -> m L.Lisp)    -- ^ How to render constructor tests
                      -> (forall (dt :: [Type] -> (Type -> *) -> *)
                          (res' :: Type).
                          IsDatatype dt =>
                          Datatype dt -> Type.Field dt res' -> m L.Lisp)          -- ^ How to render field acceses
                      -> Function fun '(arg,res) -> m L.Lisp
functionSymbolWithSig f g h i j = do
  sym <- functionSymbol f g h i j
  if isOverloaded j
    then return $ L.List [sym
                         ,typeList arg
                         ,typeSymbol Set.empty res]
    else return sym
  where
    (arg,res) = getFunType j

typeSymbol :: Set String -> Repr t -> L.Lisp
typeSymbol _ BoolRepr = L.Symbol "Bool"
typeSymbol _ IntRepr = L.Symbol "Int"
typeSymbol _ RealRepr = L.Symbol "Real"
typeSymbol _ (BitVecRepr n) = L.List [L.Symbol "_"
                                     ,L.Symbol "BitVec"
                                     ,L.Number (L.I $ bwSize n)]
typeSymbol recDt (ArrayRepr idx el)
  = L.List ((L.Symbol "Array"):
            runIdentity (List.toList (return.typeSymbol recDt) idx) ++
            [typeSymbol recDt el])
typeSymbol recDt (DataRepr dt par)
  | Set.member (datatypeName dt) recDt
    = L.Symbol (T.pack $ datatypeName dt)
  | otherwise = L.List $ [L.Symbol (T.pack $ datatypeName dt)]++
                (runIdentity $ List.toList (return.typeSymbol recDt) par)
typeSymbol _ (ParameterRepr n)
  = L.Symbol (T.pack $ "a"++show (naturalToInteger n))
                       

typeList :: List Repr t -> L.Lisp
typeList Nil = L.Symbol "()"
typeList args = L.List (runIdentity $ List.toList
                        (return.typeSymbol Set.empty) args)

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
