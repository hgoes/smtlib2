{-# LANGUAGE TemplateHaskell,QuasiQuotes #-}
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
  SMT(),
  B.Backend(),
  withBackend,withBackendExitCleanly,
  setOption,B.SMTOption(..),
  getInfo,B.SMTInfo(..),
  registerDatatype,
  declare,declareVar,declareVar',declareVarNamed,declareVarNamed',define,defineVar,defineVarNamed,
  expr,constant,
  AnalyzedExpr(),analyze,getExpr,
  B.Expr(),
  Type(..),
  assert,assertId,assertPartition,B.Partition(..),
  checkSat,checkSatWith,
  B.CheckSatResult(..),
  B.CheckSatLimits(..),noLimits,
  getValue,
  ConcreteValue(..),
  push,pop,stack,
  defConst,
  getUnsatCore,B.ClauseId(),
  getInterpolant,
  (.==.),(.>=.),(.>.),(.<=.),(.<.)
  ) where

import Language.SMTLib2.Internals.Type
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

assert :: B.Backend b => B.Expr b BoolType -> SMT b ()
assert = embedSMT . B.assert

assertId :: B.Backend b => B.Expr b BoolType -> SMT b (B.ClauseId b)
assertId = embedSMT . B.assertId

assertPartition :: B.Backend b => B.Expr b BoolType -> B.Partition -> SMT b ()
assertPartition e p = embedSMT (B.assertPartition e p)

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
  val <- mkAbstr v
  embedSMT $ B.toBackend (Const val)
  where
    mkAbstr :: (B.Backend b) => ConcreteValue tp -> SMT b (Value (B.Constr b) tp)
    mkAbstr (BoolValueC v) = return (BoolValue v)
    mkAbstr (IntValueC v) = return (IntValue v)
    mkAbstr (RealValueC v) = return (RealValue v)
    mkAbstr (BitVecValueC v bw) = return (BitVecValue v bw)
    mkAbstr (ConstrValueC (v::dt)) = do
      st <- get
      let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
      getConstructor v (B.bconstructors bdt) $
        \con args -> do
          rargs <- mapArgs mkAbstr args
          return $ ConstrValue (B.bconRepr con) rargs

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
