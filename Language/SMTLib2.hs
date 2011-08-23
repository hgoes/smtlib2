{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies #-}
module Language.SMTLib2 
       (-- * Data types
         SMT(),
         SMTType,
         SMTValue,
         SMTArith,
         SMTExpr,
         SMTOption(..),
         SMTFun,
         -- * Environment
         withSMTSolver,
         setOption,setLogic,
         assert,stack,
         checkSat,
         getValue,
         -- * Expressions
         var,
         constant,
         -- ** Basic logic
         (.==.),
         distinct,
         ite,
         and',or',xor,not',(.=>.),
         forAll,
         -- ** Arithmetic
         (.>=.),(.<=.),(.>.),(.<.),
         plus,minus,mult,div',neg,abs',divide,
         -- ** Arrays
         select,store,arrayConst,unmangleArray,
         -- ** Bitvectors
         bvadd,bvsub,bvmul,
         -- ** Functions
         fun,app,defFun
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Instances