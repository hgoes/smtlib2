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
         SMTInfo(..),SMTSolverName(..),SMTSolverVersion(..),
         assert,stack,
         checkSat,
         getValue,
         comment,
         getInterpolants,getProof,
         -- * Expressions
         var,varNamed,
         constant,let',lets,
         named,
         -- ** Basic logic
         (.==.),
         distinct,
         ite,
         and',or',xor,not',(.=>.),
         forAll,exists,
         forAllList,
         -- ** Arithmetic
         (.>=.),(.<=.),(.>.),(.<.),
         plus,minus,mult,div',mod',neg,abs',divide,
         -- ** Arrays
         select,store,arrayConst,unmangleArray,
         -- ** Bitvectors
         bvadd,bvsub,bvmul,bvurem,bvsrem,
         bvule,bvult,bvuge,bvugt,
         bvsle,bvslt,bvsge,bvsgt,
         -- ** Functions
         fun,app,defFun,
         -- ** Data types
         is,(.#),
         -- ** Lists
         head',tail',insert'
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Instances