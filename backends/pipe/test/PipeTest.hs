module PipeTest where

import Language.SMTLib2.Pipe
import Language.SMTLib2.QuickCheck

import Distribution.TestSuite
import Distribution.TestSuite.QuickCheck
import Data.Either

tests :: IO [Test]
tests = return [testProperty "round-trip"
                (roundTripTest emptyContext (createPipe "z3" ["-smt2","-in"]))]
