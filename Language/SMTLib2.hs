{- | Example usage: This program tries to find two numbers greater than zero which sum up to 5.

     @
import Language.SMTLib2
import Language.SMTLib2.Solver

program :: SMT (Integer,Integer)
program = do
  x <- var
  y <- var
  assert $ (plus [x,y]) .==. (constant 5)
  assert $ x .>. (constant 0)
  assert $ y .>. (constant 0)
  checkSat
  vx <- getValue x
  vy <- getValue y
  return (vx,vy)

main = withZ3 program >>= print
     @ -}
module Language.SMTLib2 (
  -- * SMT Monad
  SMT(),
  B.Backend(),
  withBackend,
  withBackendExitCleanly,
  -- * Setting options
  setOption,B.SMTOption(..),
  -- * Getting informations about the solver
  getInfo,B.SMTInfo(..),
  -- * Expressions
  B.Expr(),expr,
  -- ** Declaring variables
  declare,declareVar,declareVarNamed,
  -- ** Defining variables
  define,defineVar,defineVarNamed,defConst,
  -- ** Declaring functions
  declareFun,declareFunNamed,
  -- ** Defining functions
  defineFun,defineFunNamed,
  -- ** Constants
  constant,ConcreteValue(..),
  -- *** Boolean constants
  pattern ConstBool,cbool,true,false,
  -- *** Integer constants
  pattern ConstInt,cint,
  -- *** Real constants
  pattern ConstReal,creal,
  -- *** Bitvector constants
  pattern ConstBV,cbv,
  -- ** Functions
  pattern Fun,fun,
  -- *** Equality
  pattern EqLst,pattern Eq,pattern (:==:),
  eq,(.==.),
  pattern DistinctLst,pattern Distinct,pattern (:/=:),
  distinct,(./=.),
  -- *** Map
  map',
  -- *** Comparison
  pattern Ord,pattern (:>=:),pattern (:>:),pattern (:<=:),pattern (:<:),
  ord,(.>=.),(.>.),(.<=.),(.<.),
  -- *** Arithmetic
  pattern ArithLst,pattern Arith,arith,
  pattern PlusLst,pattern Plus,pattern (:+:),plus,(.+.),
  pattern MultLst,pattern Mult,pattern (:*:),mult,(.*.),
  pattern MinusLst,pattern Minus,pattern (:-:),pattern Neg,minus,(.-.),neg,
  pattern Div,pattern Mod,pattern Rem,div',mod',rem',
  pattern (:/:),(./.),
  pattern Abs,abs',
  -- *** Logic
  pattern Not,not',
  pattern LogicLst,pattern Logic,logic,
  pattern AndLst,pattern And,pattern (:&:),and',(.&.),
  pattern OrLst,pattern Or,pattern (:|:),or',(.|.),
  pattern XOrLst,pattern XOr,xor',
  pattern ImpliesLst,pattern Implies,pattern (:=>:),implies,(.=>.),
  -- *** Conversion
  pattern ToReal,pattern ToInt,toReal,toInt,
  -- *** If-then-else
  pattern ITE,ite,
  -- *** Bitvectors
  pattern BVComp,pattern BVULE,pattern BVULT,pattern BVUGE,pattern BVUGT,pattern BVSLE,pattern BVSLT,pattern BVSGE,pattern BVSGT,bvcomp,bvule,bvult,bvuge,bvugt,bvsle,bvslt,bvsge,bvsgt,
  pattern BVBin,pattern BVAdd,pattern BVSub,pattern BVMul,pattern BVURem,pattern BVSRem,pattern BVUDiv,pattern BVSDiv,pattern BVSHL,pattern BVLSHR,pattern BVASHR,pattern BVXor,pattern BVAnd,pattern BVOr,bvbin,bvadd,bvsub,bvmul,bvurem,bvsrem,bvudiv,bvsdiv,bvshl,bvlshr,bvashr,bvxor,bvand,bvor,
  pattern BVUn,pattern BVNot,pattern BVNeg,
  bvun,bvnot,bvneg,
  pattern Concat,pattern Extract,concat',extract',
  -- *** Arrays
  pattern Select,pattern Store,pattern ConstArray,select,select1,store,store1,constArray,
  -- *** Misc
  pattern Divisible,divisible,
  -- ** Analyzation
  AnalyzedExpr(),analyze,getExpr,
  -- * Satisfiability
  assert,checkSat,checkSatWith,
  B.CheckSatResult(..),
  B.CheckSatLimits(..),noLimits,
  -- ** Unsatisfiable core
  assertId,getUnsatCore,B.ClauseId(),
  -- ** Interpolation
  assertPartition,B.Partition(..),
  getInterpolant,
  -- ** Proofs
  getProof,analyzeProof,
  -- ** Stack
  push,pop,stack,
  -- ** Models
  getValue,
  getModel,
  B.Model(),
  modelEvaluate,
  -- * Types
  registerDatatype,
  Type(..),Repr(..),GetType(..),reifyType,bool,int,real,bitvec,array,
  -- ** Numbers
  Nat(..),Natural(..),nat,reifyNat,
  -- ** Lists
  List(..),list,reifyList,list1,list2,list3,(.:.),nil,
  -- * Misc
  comment,simplify
  ) where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List hiding (nil)
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Monad
import qualified Language.SMTLib2.Internals.Expression as E
import Language.SMTLib2.Internals.Embed
import qualified Language.SMTLib2.Internals.Proof as P
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.TH hiding (and',or',xor')
import Language.SMTLib2.Internals.Interface hiding (constant)
import Language.SMTLib2.Strategy

import Control.Monad.State.Strict

setOption :: B.Backend b => B.SMTOption -> SMT b ()
setOption opt = embedSMT $ B.setOption opt

getInfo :: B.Backend b => B.SMTInfo i -> SMT b i
getInfo info = embedSMT $ B.getInfo info

-- | Asserts a boolean expression to be true.
--   A successive successful `checkSat` calls mean that the generated model is consistent with the assertion.
assert :: B.Backend b => B.Expr b BoolType -> SMT b ()
assert = embedSMT . B.assert

-- | Works like `assert`, but additionally allows the user to find the unsatisfiable core of a set of assignments using `getUnsatCore`.
assertId :: B.Backend b => B.Expr b BoolType -> SMT b (B.ClauseId b)
assertId = embedSMT . B.assertId

assertPartition :: B.Backend b => B.Expr b BoolType -> B.Partition -> SMT b ()
assertPartition e p = embedSMT (B.assertPartition e p)

-- | Checks if the set of asserted expressions is satisfiable.
checkSat :: B.Backend b => SMT b B.CheckSatResult
checkSat = embedSMT (B.checkSat Nothing noLimits)

checkSatWith :: B.Backend b => Maybe Tactic -> B.CheckSatLimits -> SMT b B.CheckSatResult
checkSatWith tactic limits = embedSMT (B.checkSat tactic limits)

noLimits :: B.CheckSatLimits
noLimits = B.CheckSatLimits Nothing Nothing

getValue :: (B.Backend b) => B.Expr b t -> SMT b (ConcreteValue t)
getValue e = do
  res <- embedSMT $ B.getValue e
  mkConcr res

-- | After a successful `checkSat` query, return a satisfying assignment that makes all asserted formula true.
getModel :: B.Backend b => SMT b (B.Model b)
getModel = embedSMT B.getModel

-- | Evaluate an expression in a model, yielding a concrete value.
modelEvaluate :: B.Backend b => B.Model b -> B.Expr b t -> SMT b (ConcreteValue t)
modelEvaluate mdl e = do
  res <- embedSMT $ B.modelEvaluate mdl e
  mkConcr res

push,pop :: B.Backend b => SMT b ()
push = embedSMT B.push
pop = embedSMT B.pop

stack :: B.Backend b => SMT b a -> SMT b a
stack act = do
  push
  res <- act
  pop
  return res

defConst :: B.Backend b => B.Expr b t -> SMT b (B.Expr b t)
defConst e = do
  v <- embedSMT $ B.defineVar Nothing e
  embedSMT $ B.toBackend (E.Var v)

declareVar :: B.Backend b => Repr t -> SMT b (B.Expr b t)
declareVar tp = declareVar' tp >>= embedSMT . B.toBackend . E.Var

declareVarNamed :: B.Backend b => Repr t -> String -> SMT b (B.Expr b t)
declareVarNamed tp name = declareVarNamed' tp name >>= embedSMT . B.toBackend . E.Var

defineVar :: (B.Backend b) => B.Expr b t -> SMT b (B.Expr b t)
defineVar e = defineVar' e >>= embedSMT . B.toBackend . E.Var

defineVarNamed :: (B.Backend b) => String -> B.Expr b t -> SMT b (B.Expr b t)
defineVarNamed name e = defineVarNamed' name e >>= embedSMT . B.toBackend . E.Var

declareFun :: B.Backend b => List Repr args -> Repr res -> SMT b (B.Fun b '(args,res))
declareFun args res = embedSMT $ B.declareFun args res Nothing

declareFunNamed :: B.Backend b => List Repr args -> Repr res -> String -> SMT b (B.Fun b '(args,res))
declareFunNamed args res name = embedSMT $ B.declareFun args res (Just name)

defineFun :: B.Backend b => List Repr args
          -> (List (B.Expr b) args -> SMT b (B.Expr b res))
          -> SMT b (B.Fun b '(args,res))
defineFun tps f = do
  args <- List.mapM (\tp -> embedSMT $ B.createFunArg tp Nothing) tps
  args' <- List.mapM (embedSMT . B.toBackend . E.FVar) args
  res <- f args'
  embedSMT $ B.defineFun Nothing args res

defineFunNamed :: B.Backend b => String
               -> List Repr args
               -> (List (B.Expr b) args -> SMT b (B.Expr b res))
               -> SMT b (B.Fun b '(args,res))
defineFunNamed name tps f = do
  args <- List.mapM (\tp -> embedSMT $ B.createFunArg tp Nothing) tps
  args' <- List.mapM (embedSMT . B.toBackend . E.FVar) args
  res <- f args'
  embedSMT $ B.defineFun (Just name) args res

constant :: (B.Backend b) => ConcreteValue t -> SMT b (B.Expr b t)
constant v = do
  val <- valueFromConcrete
         (\(v::dt) f -> do
             st <- get
             let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
             getConstructor v (B.bconstructors bdt) $
               \con args -> f (B.bconRepr con) args
         ) v
  embedSMT $ B.toBackend (E.Const val)

getUnsatCore :: B.Backend b => SMT b [B.ClauseId b]
getUnsatCore = embedSMT B.getUnsatCore

getInterpolant :: B.Backend b => SMT b (B.Expr b BoolType)
getInterpolant = embedSMT B.interpolate

getExpr :: (B.Backend b) => B.Expr b tp
        -> SMT b (E.Expression
                  (B.Var b)
                  (B.QVar b)
                  (B.Fun b)
                  (B.Constr b)
                  (B.Field b)
                  (B.FunArg b)
                  (B.LVar b)
                  (B.Expr b) tp)
getExpr e = do
  st <- get
  return $ B.fromBackend (backend st) e

comment :: (B.Backend b) => String -> SMT b ()
comment msg = embedSMT $ B.comment msg

-- | Use the SMT solver to simplify a given expression.
simplify :: B.Backend b => B.Expr b tp -> SMT b (B.Expr b tp)
simplify e = embedSMT $ B.simplify e

getProof :: B.Backend b => SMT b (B.Proof b)
getProof = embedSMT B.getProof

analyzeProof :: B.Backend b => B.Proof b -> SMT b (P.Proof String (B.Expr b) (B.Proof b))
analyzeProof pr = do
  st <- get
  return $ B.analyzeProof (backend st) pr
