module Z3Test where

import Language.SMTLib2.Z3
import Language.SMTLib2.QuickCheck

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck
import Data.Either

tests :: IO [Test]
tests = return [testProperty "round-trip"
                (roundTripTest emptyContext (return z3Solver))]
