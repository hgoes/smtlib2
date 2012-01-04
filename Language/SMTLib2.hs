{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies #-}
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
         SMTInfo(),SMTSolverName(..),SMTSolverVersion(..),
         assert,stack,
         checkSat,
         getValue,
         comment,
         getInterpolants,getProof,
         -- * Expressions
         var,varNamed,varNamedAnn,varAnn,
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