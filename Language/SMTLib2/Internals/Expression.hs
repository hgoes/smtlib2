module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Type

import GHC.TypeLits
import Data.Proxy
import Data.Constraint

class AllEq (arg::[Type]) where
  type SameType arg :: Type

instance AllEq '[t] where
  type SameType '[t] = t
instance AllEq (a ': b) => AllEq (a ': a ': b) where
  type SameType (a ': a ': b) = a

class GetTypes l => Liftable (l :: [Type]) where
  type Lifted l (idx :: [Type]) :: [Type]
  getTypeConstr :: GetTypes idx => p l -> q idx -> Dict (Liftable (Lifted l idx))

instance Liftable '[] where
  type Lifted '[] idx = '[]
  getTypeConstr _ _ = Dict
instance (GetType a,Liftable b) => Liftable (a ': b) where
  type Lifted (a ': b) idx = (ArrayType idx a) ': (Lifted b idx)
  getTypeConstr (_::p (a ': b)) pidx = case getTypeConstr (Proxy::Proxy b) pidx of
    Dict -> Dict

data Function (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) (arg :: [Type]) (res :: Type) where
  Fun :: fun arg res -> Function fun con field arg res
  Eq :: AllEq arg => Function fun con field arg BoolType
  Distinct :: AllEq arg => Function fun con field arg BoolType
  Map :: (GetTypes arg,GetType res) => Function fun con field arg res -> Function fun con field (Lifted arg idx) (ArrayType idx res)
  OrdInt :: OrdOp -> Function fun con field '[IntType,IntType] BoolType
  OrdReal :: OrdOp -> Function fun con field '[RealType,RealType] BoolType
  ArithInt :: (AllEq arg, SameType arg ~ IntType) => ArithOp -> Function fun con field arg IntType
  ArithReal :: (AllEq arg, SameType arg ~ RealType) => ArithOp -> Function fun field con arg RealType
  ArithIntBin :: ArithOpInt -> Function fun con field '[IntType,IntType] IntType
  ArithRealBin :: ArithOpReal -> Function fun con field '[RealType,RealType] RealType
  ArithIntUn :: ArithOpUn -> Function fun con field '[IntType] IntType
  ArithRealUn :: ArithOpUn -> Function fun con field '[RealType] RealType
  Not :: Function fun con field '[BoolType] BoolType
  Logic :: (AllEq arg, SameType arg ~ BoolType) => LogicOp -> Function fun con field arg BoolType
  ToReal :: Function fun con field '[IntType] RealType
  ToInt :: Function fun con field '[RealType] IntType
  ITE :: Function fun con field '[BoolType,a,a] a
  BVComp :: BVCompOp -> Function fun con field '[BitVecType a,BitVecType a] BoolType
  BVBin :: BVBinOp -> Function fun con field '[BitVecType a,BitVecType a] (BitVecType a)
  BVUn :: BVUnOp -> Function fun con field '[BitVecType a] (BitVecType a)
  Select :: Function fun con field (ArrayType idx val ': idx) val
  Store :: Function fun con field (ArrayType idx val ': val ': idx) (ArrayType idx val)
  ConstArray :: Function fun con field '[val] (ArrayType idx val)
  Concat :: Function fun con field '[BitVecType a,BitVecType b] (BitVecType (a+b))
  Extract :: (KnownNat start,KnownNat len,(start + len) <= a) => Proxy start -> Proxy len -> Function fun con field '[BitVecType a] (BitVecType len)
  Constructor :: con arg a -> Function fun con field arg (DataType a)
  Test :: con arg a -> Function fun con field '[DataType a] BoolType
  Field :: field a t -> Function fun con field '[DataType a] t
  Divisible :: Integer -> Function fun con field '[IntType] BoolType

--data AnyFunction (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *)
--  = forall (arg :: [Type]) (t :: Type). (Liftable arg,GetType t) => AnyFunction { anyFunction :: Function fun con field arg t }

data AnyFunction (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) where
  AnyFunction :: (Liftable arg,GetType t) => Function fun con field arg t -> AnyFunction fun con field

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

data Expression (v :: Type -> *) (qv :: Type -> *) (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) (fv :: Type -> *) (e :: Type -> *) (res :: Type) where
  Var :: v res -> Expression v qv fun con field fv e res
  QVar :: qv res -> Expression v qv fun con field fv e res
  App :: (GetTypes arg,GetType res) => Function fun con field arg res -> Args e arg
      -> Expression v qv fun con field fv e res
  Const :: Value con a -> Expression v qv fun con field fv e a
  AsArray :: (GetTypes arg,GetType res) => Function fun con field arg res
          -> Expression v qv fun con field fv e (ArrayType arg res)
  Forall :: GetTypes arg => Args qv arg -> e BoolType -> Expression v qv fun con field fv e BoolType
  Exists :: Args qv arg -> e BoolType -> Expression v qv fun con field fv e BoolType
  Let :: Args (LetBinding v e) arg -> e res -> Expression v qv fun con field fv e res
  Named :: e res -> String -> Expression v qv fun con field fv e res

functionType :: (GetTypes arg,GetType res) => Function fun con field arg res -> (Args Repr arg,Repr res)
functionType (_::Function fun con field arg res) = (getTypes (Proxy::Proxy arg),getType (Proxy::Proxy res))
