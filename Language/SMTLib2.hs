{- | Example usage: This program tries to find two numbers greater than zero which sum up to 5.

     @
{-# LANGUAGE GADTs #-}
import Language.SMTLib2
import Language.SMTLib2.Pipe

program :: Backend b => SMT b (Integer,Integer)
program = do
  x <- declareVar int
  y <- declareVar int
  assert $ x .+. y .==. cint 5
  assert $ x .>. cint 0
  assert $ y .>. cint 0
  checkSat
  IntValueC vx <- getValue x
  IntValueC vy <- getValue y
  return (vx,vy)

main = withBackend (createPipe "z3" ["-smt2","-in"]) program >>= print
     @ -}
module Language.SMTLib2 (
  -- * SMT Monad
  SMT(),
  B.Backend(SMTMonad),
  withBackend,
  withBackendExitCleanly,
  -- * Setting options
  setOption,B.SMTOption(..),
  -- * Getting informations about the solver
  getInfo,B.SMTInfo(..),
  -- * Expressions
  B.Expr(),
  -- ** Declaring variables
  declareVar,declareVarNamed,
  -- ** Defining variables
  defineVar,defineVarNamed,
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
  pattern Fun,app,fun,
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
  getExpr,
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
  Nat(..),Natural(..),nat,natT,reifyNat,
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
import qualified Language.SMTLib2.Internals.Proof as P
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Interface hiding (constant)
import Language.SMTLib2.Strategy

import Control.Monad.State.Strict

-- | Set an option controlling the behaviour of the SMT solver.
--   Many solvers require you to specify what kind of queries you'll ask them
--   after the model is specified.
--
--   For example, when using interpolation, it is often required to do the
--   following:
--
--   @
-- do
--   setOption (ProduceInterpolants True)
--   -- Declare model
--   interp <- getInterpolant
--   -- Use interpolant
--   @
setOption :: B.Backend b => B.SMTOption -> SMT b ()
setOption opt = embedSMT $ B.setOption opt

-- | Query the solver for information about itself.
--
--   Example:
--
-- > isZ3Solver :: Backend b => SMT b Bool
-- > isZ3Solver = do
-- >   name <- getInfo SMTSolverName
-- >   return $ name=="Z3"
getInfo :: B.Backend b => B.SMTInfo i -> SMT b i
getInfo info = embedSMT $ B.getInfo info

-- | Asserts a boolean expression to be true.
--   A successive successful `checkSat` calls mean that the generated model is consistent with the assertion.
assert :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),MonadResult expr ~ B.Expr b BoolType)
       => expr -> SMT b ()
assert e = embedM e >>= embedSMT . B.assert

-- | Works like `assert`, but additionally allows the user to find the
--   unsatisfiable core of a set of assignments using `getUnsatCore`.
assertId :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),MonadResult expr ~ B.Expr b BoolType)
         => expr -> SMT b (B.ClauseId b)
assertId e = embedM e >>= embedSMT . B.assertId

-- | When using interpolation, use this function to specify if an assertion is
--   part of the A-partition or the B-partition of the original formula.
assertPartition :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),
                    MonadResult expr ~ B.Expr b BoolType)
                => expr -> B.Partition -> SMT b ()
assertPartition e p = do
  e' <- embedM e
  embedSMT (B.assertPartition e' p)

-- | Checks if the set of asserted expressions is satisfiable.
checkSat :: B.Backend b => SMT b B.CheckSatResult
checkSat = embedSMT (B.checkSat Nothing noLimits)

-- | The same as `checkSat`, but can specify an optional `Tactic` that is used
--   to give hints to the SMT solver on how to solve the problem and limits on
--   the amount of time and memory that the solver is allowed to use.
--   If the limits are exhausted, the solver must return `Unknown`.
checkSatWith :: B.Backend b => Maybe Tactic -> B.CheckSatLimits -> SMT b B.CheckSatResult
checkSatWith tactic limits = embedSMT (B.checkSat tactic limits)

noLimits :: B.CheckSatLimits
noLimits = B.CheckSatLimits Nothing Nothing

-- | After a successful `checkSat` query, query the concrete value for a given
--   expression that the SMT solver assigned to it.
getValue :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),
             MonadResult expr ~ B.Expr b t)
         => expr -> SMT b (ConcreteValue t)
getValue e = embedM e >>= embedSMT . B.getValue >>= mkConcr

-- | After a successful `checkSat` query, return a satisfying assignment that makes all asserted formula true.
getModel :: B.Backend b => SMT b (B.Model b)
getModel = embedSMT B.getModel

-- | Evaluate an expression in a model, yielding a concrete value.
modelEvaluate :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),
                  MonadResult expr ~ B.Expr b t)
              => B.Model b -> expr -> SMT b (ConcreteValue t)
modelEvaluate mdl e = embedM e >>= embedSMT . B.modelEvaluate mdl >>= mkConcr

-- | Push a fresh frame on the solver stack.
--   All variable definitions and assertions made in a frame are forgotten when
--   it is `pop`'ed.
push :: B.Backend b => SMT b ()
push = embedSMT B.push

-- | Pop a frame from the solver stack.
pop :: B.Backend b => SMT b ()
pop = embedSMT B.pop

-- | Perform an SMT action by executing it in a fresh stack frame. The frame is
--   `pop`'ed once the action has been performed.
stack :: B.Backend b => SMT b a -> SMT b a
stack act = do
  push
  res <- act
  pop
  return res

-- | Create a fresh variable of a given type.
--
--   Example:
--
--   @
-- do
--   -- Declare a single integer variable
--   v <- declareVar int
--   -- Use variable v
--   @
declareVar :: B.Backend b => Repr t -- ^ The type of the variable
           -> SMT b (B.Expr b t)
declareVar tp = declareVar' tp >>= embedSMT . B.toBackend . E.Var

-- | Create a fresh variable (like `declareVar`), but also give it a name.
--   Note that the name is a hint to the SMT solver that it may ignore.
--
--   Example:
--
--   @
-- do
--   -- Declare a single boolean variable called "x"
--   x <- declareVarNamed bool "x"
--   -- Use variable x
--   @
declareVarNamed :: B.Backend b => Repr t -- ^ Type of the variable
                -> String                -- ^ Name of the variable
                -> SMT b (B.Expr b t)
declareVarNamed tp name = declareVarNamed' tp name >>= embedSMT . B.toBackend . E.Var

-- | Create a new variable that is defined by a given expression.
--
--   Example:
--
--   @
-- do
--   -- x is an integer
--   x <- declareVar int
--   -- y is defined to be x+5
--   y <- defineVar $ x .+. cint 5
--   -- Use x and y
--   @
defineVar :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),
              MonadResult expr ~ B.Expr b t)
          => expr -- ^ The definition expression
          -> SMT b (B.Expr b t)
defineVar e = embedM e >>= defineVar' >>= embedSMT . B.toBackend . E.Var

-- | Create a new named variable that is defined by a given expression (like
--   `defineVar`).
defineVarNamed :: (B.Backend b,HasMonad expr,MatchMonad expr (SMT b),
                   MonadResult expr ~ B.Expr b t)
               => String -- ^ Name of the resulting variable
               -> expr   -- ^ Definition of the variable
               -> SMT b (B.Expr b t)
defineVarNamed name e = embedM e >>= defineVarNamed' name >>= embedSMT . B.toBackend . E.Var

-- | Create a new uninterpreted function by specifying its signature.
--
--   Example:
--
--   @
-- do
--   -- Create a function from (int,bool) to int
--   f <- declareFun (int ::: bool ::: Nil) int
--   -- Use f
--   @
declareFun :: B.Backend b
           => List Repr args -- ^ Function argument types
           -> Repr res       -- ^ Function result type
           -> SMT b (B.Fun b '(args,res))
declareFun args res = embedSMT $ B.declareFun args res Nothing

-- | Create a new uninterpreted function by specifying its signature (like
--   `declareFun`), but also give it a name.
declareFunNamed :: B.Backend b => List Repr args -- ^ Function argument types
                -> Repr res                      -- ^ Function result type
                -> String                        -- ^ Function name
                -> SMT b (B.Fun b '(args,res))
declareFunNamed args res name = embedSMT $ B.declareFun args res (Just name)

-- | Create a new interpreted function with a definition.
--   Given a signature and a (haskell) function from the arguments to the
--   resulting expression.
--
--   Example:
--
--   @
-- do
--   -- Create a function from (int,int) to int that calculates the maximum
--   max <- defineFun (int ::: int ::: Nil) $
--            \(x ::: y ::: Nil) -> ite (x .>. y) x y
--   -- Use max function
--   @
defineFun :: (B.Backend b,HasMonad def,MatchMonad def (SMT b),
              MonadResult def ~ B.Expr b res)
          => List Repr args                -- ^ Function argument types
          -> (List (B.Expr b) args -> def) -- ^ Function definition
          -> SMT b (B.Fun b '(args,res))
defineFun tps f = do
  args <- List.mapM (\tp -> embedSMT $ B.createFunArg tp Nothing) tps
  args' <- List.mapM (embedSMT . B.toBackend . E.FVar) args
  res <- embedM $ f args'
  embedSMT $ B.defineFun Nothing args res

-- | Create a new interpreted function with a definition (like `defineFun`) but
--   also give it a name.
defineFunNamed :: (B.Backend b,HasMonad def,MatchMonad def (SMT b),
                   MonadResult def ~ B.Expr b res)
               => String
               -> List Repr args
               -> (List (B.Expr b) args -> def)
               -> SMT b (B.Fun b '(args,res))
defineFunNamed name tps f = do
  args <- List.mapM (\tp -> embedSMT $ B.createFunArg tp Nothing) tps
  args' <- List.mapM (embedSMT . B.toBackend . E.FVar) args
  res <- embedM $ f args'
  embedSMT $ B.defineFun (Just name) args res

-- | Create a constant, for example an integer:
--
--   Example:
-- 
--   @
-- do
--   x <- declareVar int
--   -- x is greater than 5
--   assert $ x .>. constant (IntValueC 5)
--   @
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

-- | After a `checkSat` query that returned 'Unsat', we can ask the SMT solver
--   for a subset of the assertions that are enough to make the specified
--   problem unsatisfiable. These assertions have to be created using
--   `assertId`.
--
--   Example:
--
-- > do
-- >   setOption (ProduceUnsatCores True)
-- >   x <- declareVar int
-- >   y <- declareVar int
-- >   cl1 <- assertId $ x .>. y
-- >   cl2 <- assertId $ x .>. cint 5
-- >   cl3 <- assertId $ y .>. x
-- >   checkSat
-- >   core <- getUnsatCore
-- >   -- core will contain cl1 and cl3
getUnsatCore :: B.Backend b => SMT b [B.ClauseId b]
getUnsatCore = embedSMT B.getUnsatCore

-- | After a `checkSat` query that returned 'Unsat', we can ask the SMT solver
--   for a formula /C/ such that /A/ (the A-partition) and /(not C)/ is
--   unsatisfiable while /B/ (the B-partition) and /C/ is unsatisfiable.
--   Furthermore, /C/ will only mention variables that occur in both /A/ and
--   /B/.
--
--   Example:
--
--   @
-- do
--   setOption (ProduceInterpolants True)
--   p <- declareVar bool
--   q <- declareVar bool
--   r <- declareVar bool
--   t <- declareVar bool
--   assertPartition ((not' (p .&. q)) .=>. ((not' r) .&. q)) PartitionA
--   assertPartition t PartitionB
--   assertPartition r PartitionB
--   assertPartition (not' p) PartitionB
--   checkSat
--   getInterpolant
--   @
getInterpolant :: B.Backend b => SMT b (B.Expr b BoolType)
getInterpolant = embedSMT B.interpolate

-- | Convert an expression in the SMT solver-specific format into a more
--   general, pattern-matchable format.
--
--   Example:
--
--   @
-- isGE :: Backend b => Expr b tp -> SMT b Bool
-- isGE e = do
--   e' <- getExpr e
--   case e' of
--     _ :>=: _ -> return True
--     _ -> return False
--   @
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

-- | Inject a comment into the SMT command stream.
--   Only useful when using the /smtlib2-debug/ package to inspect the command
--   stream.
comment :: (B.Backend b) => String -> SMT b ()
comment msg = embedSMT $ B.comment msg

-- | Use the SMT solver to simplify a given expression.
simplify :: B.Backend b => B.Expr b tp -> SMT b (B.Expr b tp)
simplify e = embedSMT $ B.simplify e

-- | After a `checkSat` query that returned 'Unsat', we can ask the solver for
--   a proof that the given instance is indeed unsatisfiable.
getProof :: B.Backend b => SMT b (B.Proof b)
getProof = embedSMT B.getProof

-- | Convert the solver-specific proof encoding into a more general,
--   pattern-matchable format.
analyzeProof :: B.Backend b => B.Proof b -> SMT b (P.Proof String (B.Expr b) (B.Proof b))
analyzeProof pr = do
  st <- get
  return $ B.analyzeProof (backend st) pr
