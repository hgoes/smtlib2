module Language.SMTLib2.Solver where

import Language.SMTLib2

withZ3 = withSMTSolver "z3" ["-smt2","-in","-m"]

withMathSat = withSMTSolver "mathsat" []

withCVC4 = withSMTSolver "cvc4" ["--lang","smt2"]