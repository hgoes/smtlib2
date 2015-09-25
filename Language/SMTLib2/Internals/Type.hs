module Language.SMTLib2.Internals.Type where

import Language.SMTLib2.Internals.Type.Nat

import Data.Proxy
import Data.Typeable
import Data.Constraint
import Numeric
import Text.Show
import Data.List (genericLength,genericReplicate)

data Type = BoolType
          | IntType
          | RealType
          | BitVecType Nat
          | ArrayType [Type] Type
          | forall a. DataType a
          deriving Typeable

#if __GLASGOW_HASKELL__ < 710
deriving instance Typeable 'BoolType
deriving instance Typeable 'IntType
deriving instance Typeable 'RealType
deriving instance Typeable 'BitVecType
deriving instance Typeable 'ArrayType
deriving instance Typeable 'DataType

deriving instance Typeable ('[])
deriving instance Typeable (':)
#endif

class (Typeable t,Typeable (DatatypeSig t)) => IsDatatype t where
  type DatatypeSig t :: [[Type]]
  type TypeCollectionSig t :: [([[Type]],*)]
  getDatatype :: e t -> Datatype (DatatypeSig t) t
  getTypeCollection :: e t -> TypeCollection (TypeCollectionSig t)

type TypeCollection sigs = Datatypes Datatype sigs

data Datatype (sig::[[Type]]) dt
  = Datatype { datatypeName :: String
             , constructors :: Constrs Constr sig dt }

data Constr (arg :: [Type]) a
  = Constr { conName :: String
           , conFields :: Args (Field a) arg
           , construct :: Args ConcreteValue arg -> a
           , conTest :: a -> Bool }

data Field a (t :: Type) = Field { fieldName :: String
                                 , fieldGet :: a -> ConcreteValue t }

data Value (con :: [Type] -> * -> *) (a :: Type) where
  BoolValue :: Bool -> Value con BoolType
  IntValue :: Integer -> Value con IntType
  RealValue :: Rational -> Value con RealType
  BitVecValue :: KnownNat n => Integer -> Value con (BitVecType n)
  ConstrValue :: (Typeable con,GetTypes arg,IsDatatype t)
              => con arg t
              -> Args (Value con) arg
              -> Value con (DataType t)

data ConcreteValue (a :: Type) where
  BoolValueC :: Bool -> ConcreteValue BoolType
  IntValueC :: Integer -> ConcreteValue IntType
  RealValueC :: Rational -> ConcreteValue RealType
  BitVecValueC :: KnownNat n => Integer -> ConcreteValue (BitVecType n)
  ConstrValueC :: IsDatatype t => t -> ConcreteValue (DataType t)

data AnyValue (con :: [Type] -> * -> *) = forall (t :: Type). GetType t => AnyValue (Value con t)

data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: KnownNat n => Integer -> Repr (BitVecType n)
  ArrayRepr :: (Liftable idx,GetType val) => Args Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: IsDatatype dt => Datatype (DatatypeSig dt) dt -> Repr (DataType dt)

data AnyRepr = forall (t :: Type). AnyRepr (Repr t)

data Args (e :: Type -> *) (a :: [Type]) where
  NoArg :: Args e '[]
  Arg :: GetType t => e t -> Args e ts -> Args e (t ': ts)
  deriving Typeable

data Constrs (con :: [Type] -> * -> *) (a :: [[Type]]) t where
  NoCon :: Constrs con '[] t
  ConsCon :: Liftable arg => con arg t -> Constrs con args t -> Constrs con (arg ': args) t

data Datatypes (dts :: [[Type]] -> * -> *) (sigs :: [([[Type]],*)]) where
  NoDts :: Datatypes dts '[]
  ConsDts :: IsDatatype dt
          => dts (DatatypeSig dt) dt
          -> Datatypes dts sigs
          -> Datatypes dts ('(DatatypeSig dt,dt) ': sigs)

class Typeable t => GetType (t :: Type) where
  getType :: e t -> Repr t

instance GetType BoolType where
  getType _ = BoolRepr
instance GetType IntType where
  getType _ = IntRepr
instance GetType RealType where
  getType _ = RealRepr
instance (KnownNat n,Typeable n) => GetType (BitVecType n) where
  getType (_::e (BitVecType n)) = BitVecRepr (natVal (Proxy::Proxy n))
instance (Liftable idx,GetType el) => GetType (ArrayType idx el) where
  getType (_::e (ArrayType idx el)) = ArrayRepr (getTypes (Proxy::Proxy idx))
                                                (getType (Proxy::Proxy el))
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

argsToListM :: Monad m => (forall (t :: Type). GetType t => e t -> m a)
            -> Args e arg -> m [a]
argsToListM _ NoArg = return []
argsToListM f (Arg x xs) = do
  x' <- f x
  xs' <- argsToListM f xs
  return (x':xs')

mapValue :: (Monad m,Typeable con2)
         => (forall arg t. GetTypes arg => con1 arg t -> m (con2 arg t))
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

findConstrByName :: String -> Datatype sig dt
                 -> (forall arg. GetTypes arg => Constr arg dt -> a) -> a
findConstrByName name dt f = find f (constructors dt)
  where
    find :: (forall arg. GetTypes arg => Constr arg dt -> a) -> Constrs Constr sigs dt -> a
    find f NoCon = error $ "smtlib2: Cannot find constructor "++name++" of "++datatypeName dt
    find f (ConsCon con cons)
      = if conName con == name
        then f con
        else find f cons

findConstrByName' :: (IsDatatype dt,Typeable arg) => String -> Datatype sig dt
                  -> Constr arg dt
findConstrByName' name dt = findConstrByName name dt
                            (\con -> case cast con of
                               Just con' -> con')
