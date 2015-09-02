module Language.SMTLib2.Internals.Type where

import Language.SMTLib2.Internals.Type.Nat

import Data.Proxy
import Data.Typeable
import Data.Constraint

data Type = BoolType
          | IntType
          | RealType
          | BitVecType Nat
          | ArrayType [Type] Type
          | forall a. DataType a
          deriving Typeable

data PolyDatatype = PolyDatatype { numArgs :: Integer
                                 , instantiate :: [AnyRepr] -> AnyDatatype }

data Datatype a = Datatype { datatypeName :: String
                           , constructors :: [AnyConstr a]
                           , parameter :: [AnyRepr] }

data AnyDatatype = forall a. IsDatatype a => AnyDatatype (Datatype a)

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

data AnyValue (con :: [Type] -> * -> *) = forall (t :: Type). GetType t => AnyValue (Value con t)

data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: KnownNat n => Integer -> Repr (BitVecType n)
  ArrayRepr :: (Liftable idx,GetType val) => Args Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: Datatype a -> Repr (DataType a)

data AnyRepr = forall (t :: Type). AnyRepr (Repr t)

data Args (e :: Type -> *) (a :: [Type]) where
  NoArg :: Args e '[]
  Arg :: GetType t => e t -> Args e ts -> Args e (t ': ts)

data Constrs (con :: [Type] -> * -> *) (a :: [[Type]]) t where
  NoCon :: Constrs con '[] t
  ConsCon :: con arg t -> Constrs con args t -> Constrs con (arg ': args) t

class Typeable t => GetType (t :: Type) where
  getType :: e t -> Repr t

instance GetType BoolType where
  getType _ = BoolRepr
instance GetType IntType where
  getType _ = IntRepr
instance GetType RealType where
  getType _ = RealRepr
instance (Typeable n,KnownNat n) => GetType (BitVecType n) where
  getType (_::e (BitVecType n)) = BitVecRepr (natVal (Proxy::Proxy n))
instance (Liftable idx,GetType el) => GetType (ArrayType idx el) where
  getType (_::e (ArrayType idx el)) = ArrayRepr (getTypes (Proxy::Proxy idx)) (getType (Proxy::Proxy el))
instance IsDatatype t => GetType (DataType t) where
  getType (_::e (DataType t)) = DataRepr (getDatatype (Proxy::Proxy t))

class Typeable t => GetTypes (t :: [Type]) where
  getTypes :: e t -> Args Repr t

instance GetTypes '[] where
  getTypes _ = NoArg
instance (GetType t,GetTypes ts) => GetTypes (t ': ts) where
  getTypes (_::e (t ': ts)) = Arg (getType (Proxy::Proxy t)) (getTypes (Proxy::Proxy ts))

class GetTypes l => Liftable (l :: [Type]) where
  type Lifted l (idx :: [Type]) :: [Type]
  getTypeConstr :: Liftable idx => p l -> q idx -> Dict (Liftable (Lifted l idx))

instance Liftable '[] where
  type Lifted '[] idx = '[]
  getTypeConstr _ _ = Dict
instance (GetType a,Liftable b) => Liftable (a ': b) where
  type Lifted (a ': b) idx = (ArrayType idx a) ': (Lifted b idx)
  getTypeConstr (_::p (a ': b)) pidx = case getTypeConstr (Proxy::Proxy b) pidx of
    Dict -> Dict

class Typeable t => IsDatatype t where
  getDatatype :: e t -> Datatype t

mapArgs :: Monad m => (forall t. GetType t => e1 t -> m (e2 t))
        -> Args e1 arg
        -> m (Args e2 arg)
mapArgs f NoArg = return NoArg
mapArgs f (Arg x xs) = do
  x' <- f x
  xs' <- mapArgs f xs
  return (Arg x' xs')

argsToList :: (forall (t :: Type). GetType t => e t -> a) -> Args e arg -> [a]
argsToList _ NoArg = []
argsToList f (Arg x xs) = f x:argsToList f xs

mapValue :: Monad m
         => (forall arg t. con1 arg t -> m (con2 arg t))
         -> Value con1 a
         -> m (Value con2 a)
mapValue _ (BoolValue b) = return (BoolValue b)
mapValue _ (IntValue i) = return (IntValue i)
mapValue _ (RealValue r) = return (RealValue r)
mapValue _ (BitVecValue b) = return (BitVecValue b)
mapValue f (ConstrValue con args) = do
  con' <- f con
  args' <- mapArgs (mapValue f) args
  return (ConstrValue con' args')
