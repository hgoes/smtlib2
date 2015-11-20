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
  declare,declareVar,define,defineVar,
  expr,constant,
  B.Expr(),
  Type(..),
  assert,assertId,
  checkSat,
  B.CheckSatResult(..),
  getValue,
  ConcreteValue(..),
  push,pop,stack,
  defConst,
  getUnsatCore,B.ClauseId(),
  (.==.),(.>=.),(.>.),(.<=.),(.<.)
  ) where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.TH

import Control.Monad.State.Strict

setOption :: B.Backend b => B.SMTOption -> SMT b ()
setOption opt = embedSMT $ B.setOption opt

getInfo :: B.Backend b => B.SMTInfo i -> SMT b i
getInfo info = embedSMT $ B.getInfo info

assert :: B.Backend b => B.Expr b BoolType -> SMT b ()
assert = embedSMT . B.assert

assertId :: B.Backend b => B.Expr b BoolType -> SMT b (B.ClauseId b)
assertId = embedSMT . B.assertId

checkSat :: B.Backend b => SMT b B.CheckSatResult
checkSat = embedSMT (B.checkSat Nothing (B.CheckSatLimits Nothing Nothing))

getValue :: (B.Backend b,GetType t) => B.Expr b t -> SMT b (ConcreteValue t)
getValue e = do
  res <- embedSMT $ B.getValue e
  mkConcr res
  where
    mkConcr :: B.Backend b => Value (B.Constr b) t -> SMT b (ConcreteValue t)
    mkConcr (BoolValue v) = return (BoolValueC v)
    mkConcr (IntValue v) = return (IntValueC v)
    mkConcr (RealValue v) = return (RealValueC v)
    mkConcr (BitVecValue v) = return (BitVecValueC v)
    mkConcr (ConstrValue con args) = do
      args' <- mapArgs mkConcr args
      st <- get
      return $ ConstrValueC $
        constructDatatype con args' $
        lookupDatatype DTProxy (datatypes st)

push,pop :: B.Backend b => SMT b ()
push = embedSMT B.push
pop = embedSMT B.pop

stack :: B.Backend b => SMT b a -> SMT b a
stack act = do
  push
  res <- act
  pop
  return res

defConst :: (B.Backend b,GetType t) => B.Expr b t -> SMT b (B.Expr b t)
defConst e = do
  v <- embedSMT $ B.defineVar Nothing e
  embedSMT $ B.toBackend (Var v)

declareVar :: (B.Backend b,GetType t) => SMT b (B.Expr b t)
declareVar = do
  v <- embedSMT $ B.declareVar Nothing
  embedSMT $ B.toBackend (Var v)

defineVar :: (B.Backend b,GetType t) => B.Expr b t -> SMT b (B.Expr b t)
defineVar e = do
  re <- embedSMT $ B.defineVar Nothing e
  embedSMT $ B.toBackend (Var re)

constant :: (B.Backend b,GetType t) => ConcreteValue t -> SMT b (B.Expr b t)
constant v = do
  val <- mkAbstr v
  embedSMT $ B.toBackend (Const val)
  where
    mkAbstr :: (B.Backend b,GetType tp) => ConcreteValue tp -> SMT b (Value (B.Constr b) tp)
    mkAbstr (BoolValueC v) = return (BoolValue v)
    mkAbstr (IntValueC v) = return (IntValue v)
    mkAbstr (RealValueC v) = return (RealValue v)
    mkAbstr (BitVecValueC v) = return (BitVecValue v)
    mkAbstr (ConstrValueC (v::dt)) = do
      st <- get
      let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
      getConstructor v (B.bconstructors bdt) $
        \con args -> do
          rargs <- mapArgs mkAbstr args
          return $ ConstrValue (B.bconRepr con) rargs

getUnsatCore :: B.Backend b => SMT b [B.ClauseId b]
getUnsatCore = embedSMT B.getUnsatCore

(.==.) :: (B.Backend b,GetType t) => B.Expr b t -> B.Expr b t -> SMT b (B.Expr b BoolType)
(.==.) lhs rhs = [expr| (= lhs rhs) |]

(.<=.),(.<.),(.>=.),(.>.) :: (B.Backend b,SMTOrd t) => B.Expr b t -> B.Expr b t -> SMT b (B.Expr b BoolType)
(.<=.) lhs rhs = [expr| (<= lhs rhs) |]
(.<.) lhs rhs = [expr| (< lhs rhs) |]
(.>=.) lhs rhs = [expr| (>= lhs rhs) |]
(.>.) lhs rhs = [expr| (> lhs rhs) |]
