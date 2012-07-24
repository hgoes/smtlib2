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
         SMT(), MonadSMT(..),
         SMTType,
         SMTAnnotation,
         SMTValue,
         SMTArith,
         SMTOrd(..),
         SMTExpr,
         SMTOption(..),
         SMTFun,
         SMTArray,
         Constructor,
         Field,
         Args(..),LiftArgs(..),
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
         var,varNamed,varNamedAnn,varAnn,argVars,argVarsAnn,
         constant,constantAnn,
         extractAnnotation,
         let',lets,letAnn,
         named,
         -- ** Basic logic
         (.==.),
         distinct,
         ite,
         and',or',xor,not',(.=>.),
         forAll,exists,
         forAllAnn,existsAnn,
         forAllList,existsList,
         -- ** Arithmetic
         plus,minus,mult,div',mod',neg,divide,
         -- ** Arrays
         select,store,arrayConst,unmangleArray,asArray,
         -- ** Bitvectors
         bvadd,bvsub,bvmul,bvurem,bvsrem,
         bvule,bvult,bvuge,bvugt,
         bvsle,bvslt,bvsge,bvsgt,
         bvshl,
         ByteStringLen(..),BitstreamLen(..),
         bvconcat,bvconcats,bvextract,bvextractUnsafe,
         bvsplitu16to8,
         bvsplitu32to16,bvsplitu32to8,
         bvsplitu64to32,bvsplitu64to16,bvsplitu64to8,
         -- ** Functions
         funAnn, funAnnRet,fun,app,defFun,defConst,defFunAnn,defConstAnn,
         -- ** Data types
         is,(.#),
         -- ** Lists
         head',tail',insert'
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.SMTMonad
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Internals.Translation
import Language.SMTLib2.Internals.Interface