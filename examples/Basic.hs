{-# LANGUAGE GADTs #-}
module Basic where

import           Language.SMTLib2
import           Language.SMTLib2.Debug (debugBackend)
import           Language.SMTLib2.Pipe  (createPipe)

program :: Backend b => SMT b (Integer,Integer)
program = do
  x <- declareVar int
  y <- declareVar int
  assert $ x .+. y .==. cint 5
  assert $ x .>. cint 0
  assert $ y .>. cint 0
  checkSat
  IntValue vx <- getValue x
  IntValue vy <- getValue y
  return (vx,vy)

main = withBackend (fmap debugBackend $ createPipe "z3" ["-in","-smt2"]) program
