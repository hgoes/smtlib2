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
  B.Expr(),expr,(.==.),(.>=.),(.>.),(.<=.),(.<.),
  -- ** Declaring variables
  declare,declareVar,declareVar',declareVarNamed,declareVarNamed',
  -- ** Defining variables
  define,defineVar,defineVarNamed,defConst,
  -- ** Constants
  constant,ConcreteValue(..),
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
  -- ** Stack
  push,pop,stack,
  -- ** Models
  getValue,
  -- * Types
  registerDatatype,
  Type(..)
  ) where

import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Embed
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.TH
import Language.SMTLib2.Strategy

import Data.Proxy
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
  embedSMT $ B.toBackend (Var v)

declareVar :: (B.Backend b,SMTType t) => SMT b (B.Expr b t)
declareVar = declareVar' getRepr

declareVar' :: B.Backend b => Repr t -> SMT b (B.Expr b t)
declareVar' tp = do
  v <- embedSMT $ B.declareVar tp Nothing
  embedSMT $ B.toBackend (Var v)

declareVarNamed :: (B.Backend b,SMTType t) => String -> SMT b (B.Expr b t)
declareVarNamed = declareVarNamed' getRepr

declareVarNamed' :: B.Backend b => Repr t -> String -> SMT b (B.Expr b t)
declareVarNamed' tp name = do
  v <- embedSMT $ B.declareVar tp (Just name)
  embedSMT $ B.toBackend (Var v)

defineVar :: (B.Backend b) => B.Expr b t -> SMT b (B.Expr b t)
defineVar e = do
  re <- embedSMT $ B.defineVar Nothing e
  embedSMT $ B.toBackend (Var re)

defineVarNamed :: (B.Backend b) => String -> B.Expr b t -> SMT b (B.Expr b t)
defineVarNamed name e = do
  re <- embedSMT $ B.defineVar (Just name) e
  embedSMT $ B.toBackend (Var re)

constant :: (B.Backend b) => ConcreteValue t -> SMT b (B.Expr b t)
constant v = do
  val <- valueFromConcrete
         (\(v::dt) f -> do
             st <- get
             let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
             getConstructor v (B.bconstructors bdt) $
               \con args -> f (B.bconRepr con) args
         ) v
  embedSMT $ B.toBackend (Const val)

getUnsatCore :: B.Backend b => SMT b [B.ClauseId b]
getUnsatCore = embedSMT B.getUnsatCore

getInterpolant :: B.Backend b => SMT b (B.Expr b BoolType)
getInterpolant = embedSMT B.interpolate

getExpr :: (B.Backend b) => B.Expr b tp
        -> SMT b (Expression
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

(.==.) :: (B.Backend b,SMTType t) => B.Expr b t -> B.Expr b t -> SMT b (B.Expr b BoolType)
(.==.) lhs rhs = [expr| (= lhs rhs) |]

(.<=.),(.<.),(.>=.),(.>.) :: (B.Backend b,SMTOrd t) => B.Expr b t -> B.Expr b t -> SMT b (B.Expr b BoolType)
(.<=.) lhs rhs = [expr| (<= lhs rhs) |]
(.<.) lhs rhs = [expr| (< lhs rhs) |]
(.>=.) lhs rhs = [expr| (>= lhs rhs) |]
(.>.) lhs rhs = [expr| (> lhs rhs) |]
