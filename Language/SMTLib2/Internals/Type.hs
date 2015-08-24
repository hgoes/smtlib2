module Language.SMTLib2.Internals.Type where

import GHC.TypeLits
import Data.Proxy
import Data.Typeable

data Type = BoolType
          | IntType
          | RealType
          | BitVecType Nat
          | ArrayType [Type] Type
          | forall a. DataType a

data PolyDatatype = PolyDatatype { numArgs :: Integer
                                 , instantiate :: [AnyRepr] -> AnyDatatype }

data Datatype a = Datatype { datatypeName :: String
                           , constructors :: [AnyConstr a]
                           , parameter :: [AnyRepr] }

data AnyDatatype = forall a. AnyDatatype (Datatype a)

data AnyConstr a = forall (arg :: [Type]). AnyConstr (Constr arg a)
                                 
data Constr (arg :: [Type]) a
  = Constr { conName :: String
           , conFields :: Args (Field a) arg
           , construct :: Args (Value Constr) arg -> a
           , conTest :: a -> Bool }

data Field a (t :: Type) = Field { fieldName :: String
                                 , fieldGet :: a -> Value Constr t }

data Value (con :: [Type] -> * -> *) (a :: Type) where
  BoolValue :: Bool -> Value con BoolType
  IntValue :: Integer -> Value con IntType
  RealValue :: Rational -> Value con RealType
  BitVecValue :: KnownNat n => Integer -> Value con (BitVecType n)
  ConstrValue :: con arg t -> Args (Value con) arg -> Value con (DataType t)

data AnyValue (con :: [Type] -> * -> *) = forall (t :: Type). AnyValue (Value con t)

data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: Integer -> Repr (BitVecType n)
  ArrayRepr :: (GetTypes idx,GetType val) => Args Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: Datatype a -> Repr (DataType a)

data AnyRepr = forall (t :: Type). AnyRepr (Repr t)

data Args (e :: Type -> *) (a :: [Type]) where
  NoArg :: Args e '[]
  Arg :: GetType t => e t -> Args e ts -> Args e (t ': ts)

data Constrs (con :: [Type] -> * -> *) (a :: [[Type]]) t where
  NoCon :: Constrs con '[] t
  ConsCon :: con arg t -> Constrs con args t -> Constrs con (arg ': args) t

class GetType (t :: Type) where
  getType :: e t -> Repr t

instance GetType BoolType where
  getType _ = BoolRepr
instance GetType IntType where
  getType _ = IntRepr
instance GetType RealType where
  getType _ = RealRepr
instance KnownNat n => GetType (BitVecType n) where
  getType (_::e (BitVecType n)) = BitVecRepr (natVal (Proxy::Proxy n))
instance (GetTypes idx,GetType el) => GetType (ArrayType idx el) where
  getType (_::e (ArrayType idx el)) = ArrayRepr (getTypes (Proxy::Proxy idx)) (getType (Proxy::Proxy el))
instance IsDatatype t => GetType (DataType t) where
  getType (_::e (DataType t)) = DataRepr (getDatatype (Proxy::Proxy t))

class GetTypes (t :: [Type]) where
  getTypes :: e t -> Args Repr t

instance GetTypes '[] where
  getTypes _ = NoArg
instance (GetType t,GetTypes ts) => GetTypes (t ': ts) where
  getTypes (_::e (t ': ts)) = Arg (getType (Proxy::Proxy t)) (getTypes (Proxy::Proxy ts))

class IsDatatype t where
  getDatatype :: e t -> Datatype t
    
mapArgs :: (forall (t :: Type). GetType t => e t -> a) -> Args e arg -> [a]
mapArgs _ NoArg = []
mapArgs f (Arg x xs) = f x:mapArgs f xs
