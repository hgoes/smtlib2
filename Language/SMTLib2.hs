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
         SMTRecordType,
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
         getValue,getValue',
         comment,
         getInterpolants,getProof,getUnsatCore,
         -- * Expressions
         var,varNamed,varNamedAnn,varAnn,argVars,argVarsAnn,argVarsAnnNamed,
         constant,constantAnn,
         extractAnnotation,
         let',lets,letAnn,
         named,named',
         -- ** Basic logic
         (.==.),
         distinct,
         ite,
         (.&&.),(.||.),and',or',xor,not',not'',(.=>.),
         forAll,exists,
         forAllAnn,existsAnn,
         forAllList,existsList,
         -- ** Arithmetic
         plus,minus,mult,div',mod',rem',neg,divide,toReal,toInt,
         -- ** Arrays
         select,store,arrayEquals,unmangleArray,asArray,constArray,
         -- ** Bitvectors
         bvand,bvor,bvnot,
         bvadd,bvsub,bvmul,bvurem,bvsrem,
         bvule,bvult,bvuge,bvugt,
         bvsle,bvslt,bvsge,bvsgt,
         bvshl,bvlshr,bvashr,
         BitVector(..),
         ByteStringLen(..),
         bvconcat,bvextract,bvextractUnsafe,
         bvsplitu16to8,
         bvsplitu32to16,bvsplitu32to8,
         bvsplitu64to32,bvsplitu64to16,bvsplitu64to8,
         -- ** Functions
         funAnn,funAnnNamed,funAnnRet,fun,app,defFun,defConst,defFunAnn,defFunAnnNamed,defConstAnn,map',
         -- ** Data types
         is,(.#),
         -- ** Lists
         head',tail',insert',isNil,isInsert
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Internals.Translation
import Language.SMTLib2.Internals.Interface