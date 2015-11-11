{-# LANGUAGE TemplateHaskell #-}
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
  withBackend,
  declare,declareVar,define,
  expr,
  B.Expr(),
  assert,
  checkSat,
  B.CheckSatResult(..),
  getValue,
  ConcreteValue(..),
  push,pop,stack,
  defConst
  ) where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.TH

import Control.Monad.State.Strict

assert :: B.Backend b => B.Expr b BoolType -> SMT b ()
assert = embedSMT' . flip B.assert

checkSat :: B.Backend b => SMT b B.CheckSatResult
checkSat = embedSMT (\b -> B.checkSat b Nothing (B.CheckSatLimits Nothing Nothing))

getValue :: (B.Backend b,GetType t) => B.Expr b t -> SMT b (ConcreteValue t)
getValue e = do
  res <- embedSMT $ flip B.getValue e
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
push = embedSMT' B.push
pop = embedSMT' B.pop

stack :: B.Backend b => SMT b a -> SMT b a
stack act = do
  push
  res <- act
  pop
  return res

defConst :: (B.Backend b,GetType t) => B.Expr b t -> SMT b (B.Expr b t)
defConst e = do
  v <- embedSMT $ \b -> B.defineVar b Nothing e
  embedSMT $ flip B.toBackend (Var v)

declareVar :: (B.Backend b,GetType t) => SMT b (B.Expr b t)
declareVar = do
  v <- embedSMT $ flip B.declareVar Nothing
  embedSMT $ flip B.toBackend (Var v)
