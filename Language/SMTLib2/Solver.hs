{- | Gives interfaces to some common SMT solvers.
 -}
module Language.SMTLib2.Solver where

import Language.SMTLib2

-- | Z3 is a solver by Microsoft <http://research.microsoft.com/en-us/um/redmond/projects/z3>.
withZ3 :: SMT a -> IO a
withZ3 = withSMTSolver "z3 -smt2 -in -m"

-- | MathSAT <http://mathsat.fbk.eu>.
withMathSat :: SMT a -> IO a
withMathSat = withSMTSolver "mathsat"

-- | CVC4 is an open-source SMT solver <http://cs.nyu.edu/acsys/cvc4>
withCVC4 :: SMT a -> IO a
withCVC4 = withSMTSolver "cvc4 --lang smt2"

-- | SMTInterpol is an experimental interpolating SMT solver <http://ultimate.informatik.uni-freiburg.de/smtinterpol>
withSMTInterpol :: SMT a -> IO a
withSMTInterpol = withSMTSolver "java -jar /usr/local/share/java/smtinterpol.jar -q"