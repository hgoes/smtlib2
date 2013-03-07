{-# LANGUAGE DeriveDataTypeable,CPP,ScopedTypeVariables,KindSignatures #-}
module Language.SMTLib2.Functions where

import Language.SMTLib2.Internals
import Data.Typeable
import Data.Text as T
#ifdef SMTLIB2_WITH_DATAKINDS
import Data.Proxy
#endif

data SMTEq (a :: *) = Eq deriving (Typeable,Eq)

data SMTMap (f :: *) (i :: *) (r :: *) = SMTMap f deriving (Typeable,Eq)

-- | Represents a function in the SMT solver. /a/ is the argument of the function in SMT terms, /b/ is the argument in haskell types and /r/ is the result type of the function.
data SMTFun (a :: *) (r :: *) = SMTFun T.Text (SMTAnnotation r)
                              deriving (Typeable)

instance (Args a,SMTType r) => Eq (SMTFun a r) where
  (==) (SMTFun n1 r1) (SMTFun n2 r2) = n1 == n2 && r1 == r2

data SMTOrdOp (a :: *) 
  = Ge
  | Gt
  | Le
  | Lt
  deriving (Typeable,Eq)

data SMTArithOp (a :: *) 
  = Plus
  | Mult
  deriving (Typeable,Eq)

data SMTMinus (a :: *) = Minus deriving (Typeable,Eq)

data SMTIntArith = Div
                 | Mod
                 | Rem
                 deriving (Typeable,Eq)

data SMTDivide = Divide deriving (Typeable,Eq)

data SMTNeg (a :: *) = Neg deriving (Typeable,Eq)

data SMTAbs (a :: *) = Abs deriving (Typeable,Eq)

data SMTNot = Not deriving (Typeable,Eq)

data SMTLogic = And
              | Or
              | XOr
              | Implies
              deriving (Typeable,Eq)

data SMTDistinct (a :: *) = Distinct deriving (Typeable,Eq)

data SMTToReal = ToReal deriving (Typeable,Eq)

data SMTToInt = ToInt deriving (Typeable,Eq)

data SMTITE (a :: *) = ITE deriving (Typeable,Eq)

#ifdef SMTLIB2_WITH_DATAKINDS
data SMTBVComp (a :: BVKind) 
#else
data SMTBVComp (a :: *)
#endif
  = BVULE
  | BVULT
  | BVUGE
  | BVUGT
  | BVSLE
  | BVSLT
  | BVSGE
  | BVSGT
#ifdef SMTLIB2_WITH_DATAKINDS
  deriving Eq

instance TypeableBVKind k => Typeable (SMTBVComp k) where
  typeOf _ = mkTyConApp 
             (mkTyCon3 "smtlib2" "Language.SMTLib2.Functions" "SMTBVComp")
             [typeOfBVKind (Proxy::Proxy k)]
#else
  deriving (Typeable,Eq)
#endif

#ifdef SMTLIB2_WITH_DATAKINDS
data SMTBVBinOp (a :: BVKind)
#else
data SMTBVBinOp (a :: *)
#endif
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
#ifdef SMTLIB2_WITH_DATAKINDS
  deriving Eq

instance TypeableBVKind k => Typeable (SMTBVBinOp k) where
  typeOf _ = mkTyConApp 
             (mkTyCon3 "smtlib2" "Language.SMTLib2.Functions" "SMTBVBinOp")
             [typeOfBVKind (Proxy::Proxy k)]
#else
  deriving (Typeable,Eq)
#endif

#ifdef SMTLIB2_WITH_DATAKINDS
data SMTBVUnOp (a :: BVKind)
#else
data SMTBVUnOp (a :: *)
#endif
  = BVNot 
  | BVNeg
#ifdef SMTLIB2_WITH_DATAKINDS
  deriving Eq

instance TypeableBVKind k => Typeable (SMTBVUnOp k) where
  typeOf _ = mkTyConApp 
             (mkTyCon3 "smtlib2" "Language.SMTLib2.Functions" "SMTBVUnOp")
             [typeOfBVKind (Proxy::Proxy k)]
#else
  deriving (Typeable,Eq)
#endif

data SMTSelect (i :: *) (v :: *) = Select deriving (Typeable,Eq)

data SMTStore (i :: *) (v :: *) = Store deriving (Typeable,Eq)

data SMTConstArray (i :: *) (v :: *) = ConstArray (ArgAnnotation i) deriving (Typeable)

instance Args i => Eq (SMTConstArray i v) where
  (==) (ConstArray i1) (ConstArray i2) = i1 == i2

#ifdef SMTLIB2_WITH_DATAKINDS
data SMTConcat (t1 :: BVKind) (t2 :: BVKind) = BVConcat deriving Eq

instance (TypeableBVKind k1,TypeableBVKind k2) => Typeable (SMTConcat k1 k2) where
  typeOf _ = mkTyConApp 
             (mkTyCon3 "smtlib2" "Language.SMTLib2.Functions" "SMTConcat")
             [typeOfBVKind (Proxy::Proxy k1)
             ,typeOfBVKind (Proxy::Proxy k2)]
#else
data SMTConcat (t1 :: *) (t2 :: *) = BVConcat deriving (Typeable,Eq)
#endif

#ifdef SMTLIB2_WITH_DATAKINDS
data SMTExtract (tp :: BVKind) (start :: Nat) (len :: Nat) = BVExtract deriving Eq

instance (TypeableBVKind tp,TypeableNat start,TypeableNat len)
         => Typeable (SMTExtract tp start len) where
  typeOf _ = mkTyConApp
             (mkTyCon3 "smtlib2" "Language.SMTLib2.Functions" "SMTExtract")
             [typeOfBVKind (Proxy::Proxy tp)
             ,typeOfNat (Proxy::Proxy start)
             ,typeOfNat (Proxy::Proxy len)]
#else
data SMTExtract (tp :: *) (start :: *) (len :: *) = BVExtract deriving (Typeable,Eq)
#endif

data SMTConTest (a :: *) = ConTest (Constructor a) deriving (Typeable,Eq)

data SMTFieldSel (a :: *) (f :: *) = FieldSel (Field a f) deriving (Typeable,Eq)

data SMTHead (a :: *) = Head deriving (Typeable,Eq)

data SMTTail (a :: *) = Tail deriving (Typeable,Eq)

data SMTInsert (a :: *) = Insert deriving (Typeable,Eq)