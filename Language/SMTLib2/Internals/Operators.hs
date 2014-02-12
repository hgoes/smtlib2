module Language.SMTLib2.Internals.Operators where

import Data.Typeable

data SMTOrdOp
  = Ge
  | Gt
  | Le
  | Lt
  deriving (Typeable,Eq,Ord,Show)

data SMTArithOp
  = Plus
  | Mult
  deriving (Typeable,Eq,Ord,Show)

data SMTIntArithOp = Div
                   | Mod
                   | Rem
                   deriving (Typeable,Eq,Ord,Show)

data SMTLogicOp = And
                | Or
                | XOr
                | Implies
                deriving (Typeable,Eq,Ord,Show)

data SMTBVCompOp
  = BVULE
  | BVULT
  | BVUGE
  | BVUGT
  | BVSLE
  | BVSLT
  | BVSGE
  | BVSGT
  deriving (Typeable,Eq,Ord,Show)

data SMTBVBinOp
  = BVAdd
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
  deriving (Typeable,Eq,Ord,Show)

data SMTBVUnOp
  = BVNot 
  | BVNeg
  deriving (Typeable,Eq,Ord,Show)
