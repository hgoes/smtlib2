module Language.SMTLib2.Z3 where

import Language.SMTLib2.Internals.Backend hiding (CheckSatResult(..))
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Expression

import Z3.Base
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable

data Z3SolverState = Unconfigured
                   | Configured Context
                   | Spawned Context Solver
                   deriving Typeable

data Z3Solver = Z3Solver { solverState :: Z3SolverState
                         , solverNxtVar :: Int
                         }
              deriving Typeable

z3Solver :: Z3Solver
z3Solver = Z3Solver { solverState = Unconfigured
                    , solverNxtVar = 0 }

getContext :: Z3Solver -> IO (Context,Z3Solver)
getContext solv = case solverState solv of
  Unconfigured -> do
    ctx <- withConfig mkContext
    return (ctx,solv { solverState = Configured ctx })
  Configured ctx -> return (ctx,solv)
  Spawned ctx _ -> return (ctx,solv)

getSolver :: Z3Solver -> IO (Context,Solver,Z3Solver)
getSolver solv = case solverState solv of
  Unconfigured -> do
    ctx <- withConfig mkContext
    solver <- mkSimpleSolver ctx
    return (ctx,solver,solv { solverState = Spawned ctx solver })
  Configured ctx -> do
    solver <- mkSimpleSolver ctx
    return (ctx,solver,solv { solverState = Spawned ctx solver })
  Spawned ctx solver -> return (ctx,solver,solv)

nextSymbol :: Z3Solver -> IO (Symbol,Z3Solver)
nextSymbol solv = do
  (ctx,nsolv) <- getContext solv
  sym <- mkIntSymbol ctx (solverNxtVar solv)
  return (sym,nsolv { solverNxtVar = solverNxtVar solv+1 })

type Z3Expr = UntypedVar AST
type Z3Var = UntypedVar AST
type Z3Fun = UntypedFun FuncDecl
type Z3Con = UntypedCon Constructor
type Z3Field = UntypedField FuncDecl

instance Backend Z3Solver where
  type SMTMonad Z3Solver = IO
  type Expr Z3Solver = UntypedVar AST
  type Var Z3Solver = Z3Var
  type QVar Z3Solver = Z3Var
  type Fun Z3Solver = Z3Fun
  type Constr Z3Solver = Z3Con
  type Field Z3Solver = Z3Field
  type FunArg Z3Solver = Z3Var
  type ClauseId Z3Solver = AST
  setOption solv (SMTLogic log) = do
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
    return (nsolv { solverState = Spawned ctx rsolv })
  setOption solv _ = return solv -- TODO
  getInfo solv SMTSolverName = return ("Z3",solv)
  getInfo solv SMTSolverVersion = do
    vers <- getVersion
    return (show vers,solv)
  declareVar solv name = with $ \(_::Proxy tp) -> do
    (ctx,solv1) <- getContext solv
    tp <- typeToZ3 ctx (getType::Repr tp)
    (sym,solv2) <- nextSymbol solv1
    decl <- mkFuncDecl ctx sym [] tp
    var <- mkApp ctx decl []
    return (UntypedVar var,solv2)
    where
      with :: (Proxy t -> IO (Z3Var t,Z3Solver)) -> IO (Z3Var t,Z3Solver)
      with f = f Proxy
  defineVar solv name expr = return (expr,solv)
  toBackend solv expr = do
    (ctx,solv1) <- getContext solv
    nd <- toZ3 ctx expr
    return (UntypedVar nd,solv1)
  assert solv (UntypedVar nd) = do
    (ctx,solver,solv1) <- getSolver solv
    solverAssertCnstr ctx solver nd
    return solv1
  checkSat solv _ _ = do
    (ctx,solver,solv1) <- getSolver solv
    res <- solverCheck ctx solver
    let res' = case res of
          Sat -> B.Sat
          Unsat -> B.Unsat
          Undef -> B.Unknown
    return (res',solv1)
  getValue solv (UntypedVar v) = do
    (ctx,solver,solv1) <- getSolver solv
    mdl <- solverGetModel ctx solver
    res <- modelEval ctx mdl v True
    case res of
      Just ast -> do
        res <- fromZ3Value ctx (UntypedVar ast)
        return (res,solv1)
  push solv = do
    (ctx,solver,solv1) <- getSolver solv
    solverPush ctx solver
    return solv1
  pop solv = do
    (ctx,solver,solv1) <- getSolver solv
    solverPop ctx solver 1
    return solv1
  exit solv = return ()

fromZ3Value :: GetType t => Context -> Z3Expr t -> IO (Value Z3Con t)
fromZ3Value ctx (UntypedVar e::Z3Expr t) = case getType::Repr t of
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
    return (BitVecValue v)

typeToZ3 :: Context -> Repr t -> IO Sort
typeToZ3 ctx BoolRepr = mkBoolSort ctx
typeToZ3 ctx IntRepr = mkIntSort ctx
typeToZ3 ctx RealRepr = mkRealSort ctx
typeToZ3 ctx (BitVecRepr bw) = mkBvSort ctx bw
typeToZ3 ctx (ArrayRepr (Arg idx NoArg) el) = do
  idx' <- typeToZ3 ctx idx
  el' <- typeToZ3 ctx el
  mkArraySort ctx idx' el'

toZ3 :: GetType t => Context
     -> Expression Z3Var Z3Var Z3Fun Z3Con Z3Field Z3Var (UntypedVar AST) t
     -> IO AST
toZ3 ctx (Var (UntypedVar var)) = return var
toZ3 ctx (Const val) = toZ3Const ctx val
toZ3 ctx (App fun args) = toZ3App ctx fun args
--toZ3 ctx (AsArray fun
toZ3 ctx e = error $ "toZ3: "++show e

untypedVar :: Z3Expr t -> AST
untypedVar (UntypedVar x) = x

toZ3App :: (GetTypes sig,GetType tp) => Context -> Function Z3Fun Z3Con Z3Field '(sig,tp)
        -> Args (UntypedVar AST) sig
        -> IO AST
toZ3App ctx Eq args = mkEq' (argsToList (\(UntypedVar v) -> v) args)
  where
    mkEq' [] = mkTrue ctx
    mkEq' [x] = mkTrue ctx
    mkEq' [x,y] = mkEq ctx x y
    mkEq' (x:xs) = do
      lst <- mapM (mkEq ctx x) xs
      mkAnd ctx lst
toZ3App ctx Not (Arg (UntypedVar x) NoArg) = mkNot ctx x
toZ3App ctx (Logic And) args = mkAnd ctx $ argsToList untypedVar args
toZ3App ctx (Logic Or) args = mkOr ctx $ argsToList untypedVar args
toZ3App ctx (Logic Implies) (Arg lhs (Arg rhs NoArg)) = mkImplies ctx (untypedVar lhs) (untypedVar rhs)
toZ3App ctx Select (Arg arr (Arg idx NoArg)) = mkSelect ctx (untypedVar arr) (untypedVar idx)
toZ3App ctx Store (Arg arr (Arg val (Arg idx NoArg)))
  = mkStore ctx (untypedVar arr) (untypedVar idx) (untypedVar val)
toZ3App ctx carr@ConstArray (Arg arg NoArg) = case carr of
  (_::Function Z3Fun Z3Con Z3Field '( '[val],ArrayType sig val))
    -> case getTypes::Args Repr sig of
         Arg idx NoArg -> do
           srt <- typeToZ3 ctx idx
           mkConstArray ctx srt (untypedVar arg)
toZ3App ctx (ArithInt Plus) args = mkAdd ctx $ argsToList untypedVar args
toZ3App ctx ITE (Arg cond (Arg ifT (Arg ifF NoArg))) = mkIte ctx (untypedVar cond) (untypedVar ifT) (untypedVar ifF)
toZ3App ctx (OrdInt op) (Arg lhs (Arg rhs NoArg))
  = (case op of
       Ge -> mkGe
       Gt -> mkGt
       Le -> mkLe
       Lt -> mkLt) ctx (untypedVar lhs) (untypedVar rhs)
toZ3App ctx f _ = error $ "toZ3App: "++show f

toZ3Const :: Context -> Value Z3Con t -> IO AST
toZ3Const ctx (BoolValue False) = mkFalse ctx
toZ3Const ctx (BoolValue True) = mkTrue ctx
toZ3Const ctx (IntValue v) = mkInteger ctx v
toZ3Const ctx (RealValue v) = mkRational ctx v
toZ3Const ctx val@(BitVecValue v)
  = mkBitvector ctx (fromInteger (bw val)) v
  where
    bw :: KnownNat n => Value Z3Con (BitVecType n) -> Integer
    bw (_::Value Z3Con (BitVecType n)) = natVal (Proxy::Proxy n)
toZ3Const ctx val = error $ "toZ3Const: "++show val


{-
exprToZ3 :: Context
         -> Map Integer (AST,String)
         -> Map String FuncDecl
         -> Map (Integer,Integer) AST
         -> 
         -> SMTExpr a
         -> IO AST
exprToZ3 _ vars _ _ (Var i _) = case Map.lookup i vars of
  Just (ast,_) -> return ast
exprToZ3 ctx vars constr _ (Const c ann) = case mangle of
  PrimitiveMangling f -> valueToZ3 ctx constr (f c ann)
  ComplexMangling f -> exprToZ3 ctx vars constr (f c ann)
exprToZ3 ctx vars constr (

valueToZ3 :: Context -> Map String FuncDecl -> Value -> IO AST
valueToZ3 ctx constr (BoolValue v) = mkBool ctx v
valueToZ3 ctx constr (IntValue i)  = mkInteger ctx i
valueToZ3 ctx constr (RealValue r) = mkRational ctx r
valueToZ3 ctx constr (BVValue w v) = mkBitvector ctx (fromIntegral w) v
valueToZ3 ctx constr (Constr name args _) = case Map.lookup name constr of
  Just decl -> do
    args' <- mapM (valueToZ3 ctx constr) args
    mkApp ctx decl args'
-}
