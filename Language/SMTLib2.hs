{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,CPP #-}
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
         SMT'(),SMT,
         SMTBackend(),AnyBackend(..),
         SMTType,
         SMTAnnotation,
         SMTValue,
         SMTRecordType,
         SMTArith,
         SMTOrd(..),
         SMTExpr,
         SMTFunction,
         SMTOption(..),
         SMTArray,
         Constructor,
         Field,
         Args(..),LiftArgs(..),
         -- * Environment
         withSMTBackend,withSMTBackendExitCleanly,
         setOption,getInfo,setLogic,
         SMTInfo(..),
         assert,push,pop,stack,
         checkSat,checkSatUsing,apply,
         getValue,getValues,
         comment,
         getProof,getUnsatCore,simplify,
         -- ** Interpolation
         interpolationGroup,
         assertInterp,
         getInterpolant,
         -- * Expressions
         var,varNamed,varNamedAnn,varAnn,argVars,argVarsAnn,argVarsAnnNamed,
         constant,constantAnn,
         extractAnnotation,
         let',lets,letAnn,
         named,named',
         optimizeExpr,optimizeExpr',
         foldExpr,foldExprM,
         foldArgs,foldArgsM,
         -- ** Basic logic
         (.==.),argEq,
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
         bvand,bvor,bvxor,bvnot,bvneg,
         bvadd,bvsub,bvmul,bvurem,bvsrem,bvudiv,bvsdiv,
         bvule,bvult,bvuge,bvugt,
         bvsle,bvslt,bvsge,bvsgt,
         bvshl,bvlshr,bvashr,
         BitVector(..),
#ifdef SMTLIB2_WITH_DATAKINDS
         BVKind(..),
#else
         BVTyped,BVUntyped,
#endif
         BV8,BV16,BV32,BV64,
         N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19,N20,N21,N22,N23,N24,N25,N26,N27,N28,N29,N30,N31,N32,N33,N34,N35,N36,N37,N38,N39,N40,N41,N42,N43,N44,N45,N46,N47,N48,N49,N50,N51,N52,N53,N54,N55,N56,N57,N58,N59,N60,N61,N62,N63,N64,
         bvconcat,--bvextract,bvextractUnsafe,
         bvsplitu16to8,
         bvsplitu32to16,bvsplitu32to8,
         bvsplitu64to32,bvsplitu64to16,bvsplitu64to8,
         bvextract,bvextract',
         -- ** Functions
         funAnn,funAnnNamed,funAnnRet,fun,app,defFun,defConst,defConstNamed,defFunAnn,defFunAnnNamed,map',
         -- ** Data types
         is,(.#),
         -- ** Lists
         head',tail',insert',isNil,isInsert
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Internals.Optimize
import Language.SMTLib2.Internals.Interface
