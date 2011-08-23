{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies #-}
module Language.SMTLib2 
       (SMT(),
        SMTType,
        SMTValue,
        SMTArith,
        SMTExpr,
        SMTOption(..),
        SMTFun,
        withSMTSolver,
        setOption,setLogic,
        assert,stack,
        checkSat,
        getValue,
        var,
        constant,
        (.==.),
        (.>=.),(.<=.),(.>.),(.<.),
        distinct,
        plus,minus,mult,div',neg,abs',
        ite,
        and',not',
        select,store,arrayConst,unmangleArray,
        bvadd,bvsub,bvmul,
        forAll,
        fun,app,defFun
       )
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Instances