module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Value
import Language.SMTLib2.Internals.Type

import GHC.TypeLits
import Data.Proxy

class AllEq (l :: List Type) where
  type SameType l :: Type
instance AllEq (Cons a Nil) where
  type SameType (Cons a Nil) = a
instance (AllEq l,SameType l ~ a) => AllEq (Cons a l) where
  type SameType (Cons a l) = a

type family Lifted (l :: List Type) (idx :: List Type) :: List Type where
  Lifted Nil idx = Nil
  Lifted (Cons a l) idx = Cons (ArrayType idx a) (Lifted l idx)

data Function (arg :: List Type) (res :: Type) where
  Eq :: AllEq arg => Function arg BoolType
  Distinct :: AllEq arg => Function arg BoolType
  Map :: Function arg res -> Function (Lifted arg idx) (ArrayType idx res)
  OrdInt :: OrdOp -> Function (Cons IntType (Cons IntType Nil)) BoolType
  OrdReal :: OrdOp -> Function (Cons RealType (Cons RealType Nil)) BoolType
  ArithInt :: (AllEq arg,SameType arg ~ IntType) => ArithOp -> Function arg IntType
  ArithReal :: (AllEq arg,SameType arg ~ RealType) => ArithOp -> Function arg RealType
  ArithIntBin :: ArithOpInt -> Function (Cons IntType (Cons IntType Nil)) IntType
  ArithRealBin :: ArithOpReal -> Function (Cons RealType (Cons RealType Nil)) RealType
  ArithIntUn :: ArithOpUn -> Function (Cons IntType Nil) IntType
  ArithRealUn :: ArithOpUn -> Function (Cons RealType Nil) RealType
  Not :: Function (Cons BoolType Nil) BoolType
  Logic :: (AllEq arg,SameType arg ~ BoolType) => LogicOp -> Function arg BoolType
  ToReal :: Function (Cons IntType Nil) RealType
  ToInt :: Function (Cons RealType Nil) IntType
  ITE :: Function (Cons BoolType (Cons a (Cons a Nil))) a
  BVComp :: BVCompOp -> Function (Cons (BitVecType a) (Cons (BitVecType a) Nil)) BoolType
  BVBin :: BVBinOp -> Function (Cons (BitVecType a) (Cons (BitVecType a) Nil)) (BitVecType a)
  BVUn :: BVUnOp -> Function (Cons (BitVecType a) Nil) (BitVecType a)
  Select :: Function (Cons (ArrayType idx val) idx) val
  Store :: Function (Cons (ArrayType idx val) (Cons val idx)) (ArrayType idx val)
  ConstArray :: Function (Cons val Nil) (ArrayType idx val)
  Concat :: Function (Cons (BitVecType a) (Cons (BitVecType b) Nil)) (BitVecType (a+b))
  Extract :: ((start + len) <= a) => Proxy start -> Proxy len -> Function (Cons (BitVecType a) Nil) (BitVecType len)
  Constructor :: Constr arg a -> Function arg (DataType a)
  Test :: Constr arg a -> Function (Cons (DataType a) Nil) BoolType
  Field :: Field a t -> Function (Cons (DataType a) Nil) t
  Divisible :: Integer -> Function (Cons IntType Nil) BoolType

data OrdOp = Ge | Gt | Le | Lt

data ArithOp = Plus | Mult

data ArithOpInt = MinusInt | Div | Mod | Rem

data ArithOpReal = MinusReal | Divide

data ArithOpUn = Abs | Neg

data LogicOp = And | Or | XOr | Implies

data BVCompOp = BVULE
              | BVULT
              | BVUGE
              | BVUGT
              | BVSLE
              | BVSLT
              | BVSGE
              | BVSGT

data BVBinOp = BVAdd
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

data BVUnOp = BVNot | BVNeg

data LetBinding (v :: Type -> *) (e :: Type -> *) (t :: Type)
  = LetBinding { letVar :: v t
               , letExpr :: e t }

data Expression (v :: Type -> *) (qv :: Type -> *) (e :: Type -> *) (res :: Type) where
  Var :: v res -> Expression v qv e res
  QVar :: qv res -> Expression v qv e res
  App :: Function arg res -> Args e arg -> Expression v qv e res
  Const :: Value a -> Expression v qv e a
  AsArray :: Function arg res -> Expression v qv e (ArrayType arg res)
  Forall :: Args qv arg -> e BoolType -> Expression v qv e BoolType
  Exists :: Args qv arg -> e BoolType -> Expression v qv e BoolType
  Let :: Args (LetBinding v e) arg -> e res -> Expression v qv e res
  Named :: e res -> String -> Expression v qv e res
