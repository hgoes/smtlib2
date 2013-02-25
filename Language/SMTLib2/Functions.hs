{-# LANGUAGE DeriveDataTypeable #-}
module Language.SMTLib2.Functions where

import Language.SMTLib2.Internals
import Data.Typeable
import Data.Text as T

data SMTEq a = Eq Integer deriving (Typeable,Eq)

data SMTMap f a i r = SMTMap f deriving (Typeable,Eq)

-- | Represents a function in the SMT solver. /a/ is the argument of the function in SMT terms, /b/ is the argument in haskell types and /r/ is the result type of the function.
data SMTFun a r = SMTFun T.Text (ArgAnnotation a) (SMTAnnotation r)
                   deriving (Typeable)

instance (Args a,SMTType r) => Eq (SMTFun a r) where
  (==) (SMTFun n1 a1 r1) (SMTFun n2 a2 r2) = n1 == n2 && a1==a2 && r1 == r2

data SMTOrdOp a = Ge
                | Gt
                | Le
                | Lt
                deriving (Typeable,Eq)

data SMTArithOp a = Plus
                  | Mult
                  deriving (Typeable,Eq)

data SMTMinus a = Minus deriving (Typeable,Eq)

data SMTIntArith = Div
                 | Mod
                 | Rem
                 deriving (Typeable,Eq)

data SMTDivide = Divide deriving (Typeable,Eq)

data SMTNeg a = Neg deriving (Typeable,Eq)

data SMTAbs a = Abs deriving (Typeable,Eq)

data SMTNot = Not deriving (Typeable,Eq)

data SMTLogic = And
              | Or
              | XOr
              | Implies
              deriving (Typeable,Eq)

data SMTDistinct a = Distinct deriving (Typeable,Eq)

data SMTToReal = ToReal deriving (Typeable,Eq)

data SMTToInt = ToInt deriving (Typeable,Eq)

data SMTITE a = ITE deriving (Typeable,Eq)

data SMTBVComp a = BVULE
                 | BVULT
                 | BVUGE
                 | BVUGT
                 | BVSLE
                 | BVSLT
                 | BVSGE
                 | BVSGT
                 deriving (Typeable,Eq)

data SMTBVBinOp a = BVAdd
                  | BVSub
                  | BVMul
                  | BVURem
                  | BVSRem
                  | BVUDiv
                  | BVSDiv
                  | BVSHL
                  | BVLSHR
                  | BVASHR
                  | BVXor
                  | BVAnd
                  | BVOr
                  deriving (Typeable,Eq)

data SMTBVUnOp a = BVNot 
                 | BVNeg
                 deriving (Typeable,Eq)

data SMTSelect i v = Select deriving (Typeable,Eq)

data SMTStore i v = Store deriving (Typeable,Eq)

data SMTConstArray i v = ConstArray (ArgAnnotation i) deriving (Typeable)

instance Args i => Eq (SMTConstArray i v) where
  (==) (ConstArray i1) (ConstArray i2) = i1 == i2

data SMTConcat t1 t2 = BVConcat deriving (Typeable,Eq)

data SMTExtract t1 t2 = BVExtract Integer Integer deriving (Typeable,Eq)

data SMTConTest a = ConTest (Constructor a) deriving (Typeable,Eq)

data SMTFieldSel a f = FieldSel (Field a f) deriving (Typeable,Eq)

data SMTHead a = Head deriving (Typeable,Eq)

data SMTTail a = Tail deriving (Typeable,Eq)

data SMTInsert a = Insert deriving (Typeable,Eq)