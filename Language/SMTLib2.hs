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
  L.withBackend,
  SMT(),SMTExpr(),Type(..),analyze,L.setOption,B.SMTOption(..),
  declare,TH.expr,assert,L.CheckSatResult(..),L.checkSat,getValue,KnownNat(),
  L.Partition(..),
  assertPartition,
  interpolate,
  L.registerDatatype
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

assertPartition :: Backend b => SMTExpr b BoolType -> L.Partition -> SMT b ()
assertPartition = L.assertPartition

interpolate :: Backend b => SMT b (SMTExpr b BoolType)
interpolate = L.interpolate

analyze :: (Backend b,GetType tp) => SMTExpr b tp -> E.Expression (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) (SMTExpr b) tp
analyze e = case L.extract e of
  Left e' -> e'
  Right sub -> error $ "smtlib2: Cannot analyze embedded object "++E.showVar 11 sub ""++" using this API. Use the LowLevel module."

getValue :: (Backend b,L.SMTValue c repr) => SMTExpr b repr -> SMT b c
getValue = L.getValue

declare :: QuasiQuoter
declare = TH.declare' (Just $ \tp -> [t| forall b. Backend b => SMT b (SMTExpr b $(tp)) |])
