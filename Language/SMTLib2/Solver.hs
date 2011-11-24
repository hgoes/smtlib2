module Language.SMTLib2.Solver where

import Language.SMTLib2

withZ3 :: SMT a -> IO a
withZ3 = withSMTSolver "z3 -smt2 -in -m"

withMathSat :: SMT a -> IO a
withMathSat = withSMTSolver "mathsat"

withCVC4 :: SMT a -> IO a
withCVC4 = withSMTSolver "cvc4 --lang smt2"

withSMTInterpol :: SMT a -> IO a
withSMTInterpol = withSMTSolver "java -jar /usr/local/share/java/smtinterpol.jar -q"