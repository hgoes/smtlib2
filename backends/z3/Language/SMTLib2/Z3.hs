module Language.SMTLib2.Z3 where

import Language.SMTLib2.Internals.Backend hiding (CheckSatResult(..))
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Interface as I

import Z3.Base as Z3
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable
import Data.Functor.Identity
import System.IO.Unsafe
import Data.GADT.Show
import Data.GADT.Compare

data Z3SolverState = Unconfigured Z3Options
                   | Configured Context Z3Options
                   | Spawned Context Solver
                   deriving Typeable

data Z3Solver = Z3Solver { solverState :: Z3SolverState
                         , solverNxtVar :: Int
                         }
              deriving Typeable

data Z3Options = Z3Options { randomSeed :: Word }

defaultZ3Options :: Z3Options
defaultZ3Options = Z3Options { randomSeed = 0 }

z3Solver :: Z3Solver
z3Solver = Z3Solver { solverState = Unconfigured defaultZ3Options
                    , solverNxtVar = 0 }

z3SolverWithOptions :: Z3Options -> Z3Solver
z3SolverWithOptions opts = Z3Solver { solverState = Unconfigured opts
                                    , solverNxtVar = 0 }

getContext :: Z3Solver -> IO (Context,Z3Solver)
getContext solv = case solverState solv of
  Unconfigured opts -> do
    ctx <- withConfig mkContext
    return (ctx,solv { solverState = Configured ctx opts })
  Configured ctx opts -> return (ctx,solv)
  Spawned ctx _ -> return (ctx,solv)

getSolver :: Z3Solver -> IO (Context,Solver,Z3Solver)
getSolver solv = case solverState solv of
  Unconfigured opts -> do
    ctx <- withConfig mkContext
    solver <- mkSolver ctx
    applyOptions ctx solver opts
    return (ctx,solver,solv { solverState = Spawned ctx solver })
  Configured ctx opts -> do
    solver <- mkSolver ctx
    applyOptions ctx solver opts
    return (ctx,solver,solv { solverState = Spawned ctx solver })
  Spawned ctx solver -> return (ctx,solver,solv)

applyOptions :: Context -> Solver -> Z3Options -> IO ()
applyOptions ctx solv opts = do
  params <- mkParams ctx
  seedSym <- mkStringSymbol ctx ":random-seed"
  paramsSetUInt ctx params seedSym (randomSeed opts)
  solverSetParams ctx solv params

nextSymbol :: Z3Solver -> IO (Symbol,Z3Solver)
nextSymbol solv = do
  (ctx,nsolv) <- getContext solv
  sym <- mkIntSymbol ctx (solverNxtVar solv)
  return (sym,nsolv { solverNxtVar = solverNxtVar solv+1 })

type Z3Expr = UntypedVar AST
type Z3Var = UntypedVar AST
type Z3Fun = UntypedFun FuncDecl

instance Show Z3.Model where
  showsPrec _ _ = showString "Z3Model"

deriving instance GShow (Expr Z3Solver)
deriving instance GEq (Expr Z3Solver)
deriving instance GCompare (Expr Z3Solver)
deriving instance GetType (Expr Z3Solver)

getAST :: Expr Z3Solver tp -> AST
getAST (Z3Expr (UntypedVar ast _)) = ast

mkExpr :: AST -> Repr tp -> Expr Z3Solver tp
mkExpr ast tp = Z3Expr (UntypedVar ast tp)

instance Backend Z3Solver where
  type SMTMonad Z3Solver = IO
  newtype Expr Z3Solver tp = Z3Expr (UntypedVar AST tp)
  type Var Z3Solver = Z3Var
  type QVar Z3Solver = Z3Var
  type Fun Z3Solver = Z3Fun
  type FunArg Z3Solver = Z3Var
  type LVar Z3Solver = Z3Var
  type ClauseId Z3Solver = AST
  type Model Z3Solver = Z3.Model
  type Proof Z3Solver = () -- TODO: Proof support not implemented yet
  setOption (SMTLogic log) solv = do
    (ctx,nsolv) <- getContext solv
    let logic = case log of
          "AUFLIA" -> AUFLIA
          "AUFLIRA" -> AUFLIRA
          "AUFNIRA" -> AUFNIRA
          "LRA" -> LRA
          "QF_ABV" -> QF_ABV
          "QF_AUFBV" -> QF_AUFBV
          "QF_AUFLIA" -> QF_AUFLIA
          "QF_AX" -> QF_AX
          "QF_BV" -> QF_BV
          "QF_IDL" -> QF_IDL
          "QF_LIA" -> QF_LIA
          "QF_LRA" -> QF_LRA
          "QF_NIA" -> QF_NIA
          "QF_NRA" -> QF_NRA
          "QF_RDL" -> QF_RDL
          "QF_UF" -> QF_UF
          "QF_UFBV" -> QF_UFBV
          "QF_UFIDL" -> QF_UFIDL
          "QF_UFLIA" -> QF_UFLIA
          "QF_UFLRA" -> QF_UFLRA
          "QF_UFNRA" -> QF_UFNRA
          "UFLRA" -> UFLRA
          "UFNIA" -> UFNIA
          _ -> error $ "smtlib2-z3: Unknown logic "++show log++"."
    rsolv <- mkSolverForLogic ctx logic
    return ((),nsolv { solverState = Spawned ctx rsolv })
  setOption _ solv = return ((),solv) -- TODO
  getInfo SMTSolverName solv = return ("Z3",solv)
  getInfo SMTSolverVersion solv = do
    vers <- getVersion
    return (show vers,solv)
  declareVar tp name solv =do
    (ctx,solv1) <- getContext solv
    rtp <- typeToZ3 ctx tp
    (sym,solv2) <- nextSymbol solv1
    decl <- mkFuncDecl ctx sym [] rtp
    var <- mkApp ctx decl []
    return (UntypedVar var tp,solv2)
  defineVar name (Z3Expr expr) solv = return (expr,solv)
  toBackend expr solv = do
    (ctx,solv1) <- getContext solv
    nd <- toZ3 ctx expr
    return (mkExpr nd (getType expr),solv1)
  fromBackend solv e = unsafePerformIO $ do
    (ctx,_) <- getContext solv
    fromZ3 ctx e
  assert e solv = do
    (ctx,solver,solv1) <- getSolver solv
    solverAssertCnstr ctx solver (getAST e)
    return ((),solv1)
  assertId e solv = do
    (ctx,solver,solv1) <- getSolver solv
    cid <- mkFreshBoolVar ctx "cid"
    solverAssertAndTrack ctx solver (getAST e) cid
    return (cid,solv1)
  checkSat _ limit solv = do
    (ctx,solver,solv1) <- getSolver solv
    params <- mkParams ctx
    timeoutSym <- mkStringSymbol ctx ":timeout"
    paramsSetUInt ctx params timeoutSym
      (case limitTime limit of
          Nothing -> maxBound
          Just lim -> fromInteger lim)
    solverSetParams ctx solver params
    res <- solverCheck ctx solver
    let res' = case res of
          Sat -> B.Sat
          Unsat -> B.Unsat
          Undef -> B.Unknown
    return (res',solv1)
  getUnsatCore solv = do
    (ctx,solver,solv1) <- getSolver solv
    core <- solverGetUnsatCore ctx solver
    return (core,solv1)
  getValue (Z3Expr (UntypedVar v tp)) solv = do
    (ctx,solver,solv1) <- getSolver solv
    mdl <- solverGetModel ctx solver
    res <- modelEval ctx mdl v True
    case res of
      Just ast -> do
        res <- fromZ3Value ctx (UntypedVar ast tp)
        return (res,solv1)
  push solv = do
    (ctx,solver,solv1) <- getSolver solv
    solverPush ctx solver
    return ((),solv1)
  pop solv = do
    (ctx,solver,solv1) <- getSolver solv
    solverPop ctx solver 1
    return ((),solv1)
  exit solv = return ((),solv)
  simplify (Z3Expr (UntypedVar e tp)) solv = do
    (ctx,solv1) <- getContext solv
    ne <- Z3.simplify ctx e
    return (mkExpr ne tp,solv1)

fromZ3Value :: Context -> Z3Expr t -> IO (Value t)
fromZ3Value ctx (UntypedVar e tp) = case tp of
  BoolRepr -> do
    v <- getBool ctx e
    return (BoolValue v)
  IntRepr -> do
    v <- getInt ctx e
    return (IntValue v)
  RealRepr -> do
    v <- getReal ctx e
    return (RealValue v)
  BitVecRepr bw -> do
    v <- getInt ctx e
    return (BitVecValue v bw)

typeToZ3 :: Context -> Repr t -> IO Sort
typeToZ3 ctx BoolRepr = mkBoolSort ctx
typeToZ3 ctx IntRepr = mkIntSort ctx
typeToZ3 ctx RealRepr = mkRealSort ctx
typeToZ3 ctx (BitVecRepr bw) = mkBvSort ctx (naturalToInteger bw)
typeToZ3 ctx (ArrayRepr (idx ::: Nil) el) = do
  idx' <- typeToZ3 ctx idx
  el' <- typeToZ3 ctx el
  mkArraySort ctx idx' el'

toZ3 :: Context
     -> Expression Z3Var Z3Var Z3Fun Z3Var Z3Var (Expr Z3Solver) t
     -> IO AST
toZ3 ctx (Var (UntypedVar var tp)) = return var
toZ3 ctx (Const val) = toZ3Const ctx val
toZ3 ctx (App fun args) = toZ3App ctx fun args
--toZ3 ctx (AsArray fun
toZ3 ctx e = error $ "toZ3: "++show e

fromZ3 :: Context
       -> Expr Z3Solver tp
       -> IO (Expression Z3Var Z3Var Z3Fun Z3Var Z3Var (Expr Z3Solver) tp)
fromZ3 ctx (Z3Expr v@(UntypedVar var tp)) = do
  kind <- getAstKind ctx var
  case kind of
    Z3_VAR_AST -> return (Var v)
    Z3_APP_AST -> do
      app <- toApp ctx var
      func <- getAppDecl ctx app
      sym <- getDeclName ctx func
      symKind <- getSymbolKind ctx sym
      case symKind of
        Z3_INT_SYMBOL -> return (Var v)
        Z3_STRING_SYMBOL -> do
          symName <- getSymbolString ctx sym
          args <- getAppArgs ctx app
          case symName of
            "true" -> case tp of
              BoolRepr -> return $ I.ConstBool True
            "false" -> case tp of
              BoolRepr -> return $ I.ConstBool False
            "and" -> case tp of
              BoolRepr -> return $ I.AndLst (fmap (\v -> mkExpr v BoolRepr) args)
            "or" -> case tp of
              BoolRepr -> return $ I.OrLst (fmap (\v -> mkExpr v BoolRepr) args)
            "not" -> case tp of
              BoolRepr -> case args of
                [x] -> return $ I.Not (mkExpr x BoolRepr)
            "=>" -> case tp of
              BoolRepr -> return $ I.ImpliesLst (fmap (\v -> mkExpr v BoolRepr) args)
            "if" -> case args of
              [c,x,y] -> return $ I.ITE (mkExpr c BoolRepr) (mkExpr x tp) (mkExpr y tp)
            "=" -> case tp of
              BoolRepr -> case args of
                x:_ -> do
                  srt <- getSort ctx x
                  z3Sort ctx srt $
                    \rtp -> return $ I.EqLst (fmap (\v -> mkExpr v rtp) args)
            "<" -> case tp of
              BoolRepr -> case args of
                [x,y] -> do
                  srt <- getSort ctx x
                  z3Sort ctx srt $
                    \rtp -> case rtp of
                      IntRepr -> return ((mkExpr x IntRepr) I.:<: (mkExpr y IntRepr))
            "<=" -> case tp of
              BoolRepr -> case args of
                [x,y] -> do
                  srt <- getSort ctx x
                  z3Sort ctx srt $
                    \rtp -> case rtp of
                      IntRepr -> return ((mkExpr x IntRepr) I.:<=: (mkExpr y IntRepr))
            ">" -> case tp of
              BoolRepr -> case args of
                [x,y] -> do
                  srt <- getSort ctx x
                  z3Sort ctx srt $
                    \rtp -> case rtp of
                      IntRepr -> return ((mkExpr x IntRepr) I.:>: (mkExpr y IntRepr))
            ">=" -> case tp of
              BoolRepr -> case args of
                [x,y] -> do
                  srt <- getSort ctx x
                  z3Sort ctx srt $
                    \rtp -> case rtp of
                      IntRepr -> return ((mkExpr x IntRepr) I.:>=: (mkExpr y IntRepr))
            "+" -> case tp of
              IntRepr -> return $ I.PlusLst (fmap (\v -> mkExpr v IntRepr) args)
            _ -> error $ "Translate symbol " ++ show symName
    Z3_NUMERAL_AST -> do
      str <- getNumeralString ctx var
      case tp of
        IntRepr -> return $ I.ConstInt (read str)
        BitVecRepr bw -> return $ I.ConstBV (read str) bw
        RealRepr -> return $ I.ConstReal (read str)
    Z3_QUANTIFIER_AST -> error "Quantifier AST"
    Z3_SORT_AST -> error "Sort AST"
    Z3_FUNC_DECL_AST -> error "FuncDecl AST"
    Z3_UNKNOWN_AST -> error "Unknown AST"

z3Sort :: Context -> Sort -> (forall tp. Repr tp -> IO a) -> IO a
z3Sort ctx s f = do
  kind <- getSortKind ctx s
  case kind of
    Z3_BOOL_SORT -> f BoolRepr
    Z3_INT_SORT -> f IntRepr
    Z3_REAL_SORT -> f RealRepr
    Z3_BV_SORT -> do
      sz <- getBvSortSize ctx s
      reifyNat (fromIntegral sz) $
        \bw -> f (BitVecRepr bw)
    Z3_ARRAY_SORT -> do
      dom <- getArraySortDomain ctx s
      range <- getArraySortRange ctx s
      z3Sort ctx dom $
        \dom' -> z3Sort ctx range $
                 \range' -> f (ArrayRepr (dom' ::: Nil) range')

untypedVar :: Z3Expr t -> AST
untypedVar (UntypedVar x _) = x

toZ3App :: Context -> Function Z3Fun '(sig,tp)
        -> List (Expr Z3Solver) sig
        -> IO AST
toZ3App ctx (Eq tp n) args = mkEq' (runIdentity $ List.toList (return.getAST) args)
  where
    mkEq' [] = mkTrue ctx
    mkEq' [x] = mkTrue ctx
    mkEq' [x,y] = mkEq ctx x y
    mkEq' (x:xs) = do
      lst <- mapM (mkEq ctx x) xs
      mkAnd ctx lst
toZ3App ctx Not (x ::: Nil) = mkNot ctx (getAST x)
toZ3App ctx (Logic And _) args = mkAnd ctx $ runIdentity $ List.toList (return.getAST) args
toZ3App ctx (Logic Or _) args = mkOr ctx $ runIdentity $ List.toList (return.getAST) args
toZ3App ctx (Logic Implies _) (lhs ::: rhs ::: Nil) = mkImplies ctx (getAST lhs) (getAST rhs)
toZ3App ctx (Select _ _) (arr ::: idx ::: Nil) = mkSelect ctx (getAST arr) (getAST idx)
toZ3App ctx (Store _ _) (arr ::: val ::: idx ::: Nil)
  = mkStore ctx (getAST arr) (getAST idx) (getAST val)
toZ3App ctx (ConstArray (idx ::: Nil) el) (arg ::: Nil) = do
  srt <- typeToZ3 ctx idx
  mkConstArray ctx srt (getAST arg)
toZ3App ctx (Arith NumInt Plus _) args = mkAdd ctx $ runIdentity $ List.toList (return.getAST) args
toZ3App ctx (Arith NumInt Minus _) args = mkSub ctx $ runIdentity $ List.toList (return.getAST) args
toZ3App ctx (Arith NumInt Mult _) args = mkMul ctx $ runIdentity $ List.toList (return.getAST) args
toZ3App ctx (ArithIntBin Div) (x ::: y ::: Nil) = mkDiv ctx (getAST x) (getAST y)
toZ3App ctx (ArithIntBin Mod) (x ::: y ::: Nil) = mkMod ctx (getAST x) (getAST y)
toZ3App ctx (ArithIntBin Rem) (x ::: y ::: Nil) = mkRem ctx (getAST x) (getAST y)
toZ3App ctx (ITE _) (cond ::: ifT ::: ifF ::: Nil) = mkIte ctx (getAST cond) (getAST ifT) (getAST ifF)
toZ3App ctx (Ord NumInt op) (lhs ::: rhs ::: Nil)
  = (case op of
       Ge -> mkGe
       Gt -> mkGt
       Le -> mkLe
       Lt -> mkLt) ctx (getAST lhs) (getAST rhs)
toZ3App ctx f _ = error $ "toZ3App: "++show f

toZ3Const :: Context -> Value t -> IO AST
toZ3Const ctx (BoolValue False) = mkFalse ctx
toZ3Const ctx (BoolValue True) = mkTrue ctx
toZ3Const ctx (IntValue v) = mkInteger ctx v
toZ3Const ctx (RealValue v) = mkRational ctx v
toZ3Const ctx (BitVecValue v bw)
  = mkBitvector ctx (fromInteger $ naturalToInteger bw) v
toZ3Const ctx val = error $ "toZ3Const: "++show val

