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
  B.Backend(SMTMonad,ClauseId),
  L.withBackend,
  SMT(),SMTExpr(),Type(..),analyze,L.setOption,B.SMTOption(..),
  declare,TH.expr,assert,assertId,L.CheckSatResult(..),L.checkSat,getValue,KnownNat(),
  L.Partition(..),
  assertPartition,
  interpolate,L.getUnsatCore,
  L.registerDatatype,
  -- * Expressions
  -- ** Constants
  constant,
  -- ** Comparison
  (.==.),(./=.),
  (.<.),(.<=.),(.>.),(.>=.),
  -- ** Basic logic
  ite,
  -- ** Arithmetic
  (.+.),(.-.),(.*.),abs'
  ) where

import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.LowLevel (SMT,SMTExpr,Backend)
import qualified Language.SMTLib2.LowLevel as L
import qualified Language.SMTLib2.Internals.Expression as E
import qualified Language.SMTLib2.Internals.TH as TH
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.Haskell.TH.Quote

assert :: Backend b => SMTExpr b BoolType -> SMT b ()
assert = L.assert

assertId :: Backend b => SMTExpr b BoolType -> SMT b (L.ClauseId b)
assertId = L.assertId

assertPartition :: Backend b => SMTExpr b BoolType -> L.Partition -> SMT b ()
assertPartition = L.assertPartition

interpolate :: Backend b => SMT b (SMTExpr b BoolType)
interpolate = L.interpolate

analyze :: (Backend b,GetType tp) => SMTExpr b tp -> E.Expression (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) (SMTExpr b) tp
analyze e = case L.extract e of
  Left e' -> e'
  Right sub -> error $ "smtlib2: Cannot analyze embedded object "++show sub++" using this API. Use the LowLevel module."

getValue :: (Backend b,L.FromSMT repr) => SMTExpr b repr -> SMT b (L.ValueType repr)
getValue = L.getValue

declare :: QuasiQuoter
declare = TH.declare' (Just $ \tp -> [t| forall b. Backend b => SMT b (SMTExpr b $(tp)) |])

constant :: (L.ToSMT t,L.FromSMT (L.ValueRepr t),L.ValueType (L.ValueRepr t) ~ t)  => t -> SMTExpr b (L.ValueRepr t)
constant v = L.SpecialExpr (L.Const' v)

(.==.) :: GetType t => SMTExpr b t -> SMTExpr b t -> SMTExpr b BoolType
(.==.) x y = L.SMTExpr (L.App L.Eq (Arg x (Arg y NoArg)))

(./=.) :: GetType t => SMTExpr b t -> SMTExpr b t -> SMTExpr b BoolType
(./=.) x y = L.SMTExpr (L.App L.Distinct (Arg x (Arg y NoArg)))

(.<.),(.<=.),(.>.),(.>=.) :: L.SMTOrd t => SMTExpr b t -> SMTExpr b t -> SMTExpr b BoolType
(.<.) x y = L.SMTExpr (L.App L.lt (Arg x (Arg y NoArg)))
(.<=.) x y = L.SMTExpr (L.App L.le (Arg x (Arg y NoArg)))
(.>.) x y = L.SMTExpr (L.App L.gt (Arg x (Arg y NoArg)))
(.>=.) x y = L.SMTExpr (L.App L.ge (Arg x (Arg y NoArg)))

(.+.),(.-.),(.*.) :: L.SMTArith t => SMTExpr b t -> SMTExpr b t -> SMTExpr b t
(.+.) x y = L.SMTExpr (L.App L.plus (Arg x (Arg y NoArg)))
(.-.) x y = L.SMTExpr (L.App L.minus (Arg x (Arg y NoArg)))
(.*.) x y = L.SMTExpr (L.App L.mult (Arg x (Arg y NoArg)))

abs' :: L.SMTArith t => SMTExpr b t -> SMTExpr b t
abs' x = L.SMTExpr (L.App L.abs' (Arg x NoArg))

ite :: GetType a => SMTExpr b BoolType -> SMTExpr b a -> SMTExpr b a -> SMTExpr b a
ite c ifT ifF = L.SMTExpr $ L.App L.ITE (Arg c (Arg ifT (Arg ifF NoArg)))

instance Num (SMTExpr b IntType) where
  (+) = (.+.)
  (-) = (.-.)
  (*) = (.*.)
  negate x = L.SMTExpr (L.App L.minus (Arg x NoArg))
  abs = abs'
  fromInteger x = L.SMTExpr (L.Const (L.IntValue x))
  signum x = ite (x .==. 0) 0 (ite (x .<. 0) (-1) 1)
