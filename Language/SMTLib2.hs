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
         Constructor,
         Field,
         Args,
         -- * Environment
         withSMTSolver,
         setOption,setLogic,
         assert,stack,
         checkSat,
         getValue,
         -- * Expressions
         var,varNamed,
         constant,
         -- ** Basic logic
         (.==.),
         distinct,
         ite,
         and',or',xor,not',(.=>.),
         forAll,exists,
         -- ** Arithmetic
         (.>=.),(.<=.),(.>.),(.<.),
         plus,minus,mult,div',mod',neg,abs',divide,
         -- ** Arrays
         select,store,arrayConst,unmangleArray,
         -- ** Bitvectors
         bvadd,bvsub,bvmul,
         -- ** Functions
         fun,app,defFun,
         -- ** Data types
         is,(.#)
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Instances