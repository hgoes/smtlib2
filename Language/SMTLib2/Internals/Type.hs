module Language.SMTLib2.Internals.Type where

import Language.SMTLib2.Internals.Type.Nat

import Data.Proxy
import Data.Typeable
import Data.Constraint
import Numeric
import Text.Show
import Data.List (genericLength,genericReplicate)
import Data.GADT.Compare
import Data.GADT.Show

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

type family Fst (a :: (p,q)) :: p where
  Fst '(x,y) = x

type family Snd (a :: (p,q)) :: q where
  Snd '(x,y) = y

class (Typeable t,Typeable (DatatypeSig t),Show t,Ord t) => IsDatatype t where
  type DatatypeSig t :: [[Type]]
  type TypeCollectionSig t :: [([[Type]],*)]
  getDatatype :: e t -> Datatype '(DatatypeSig t,t)
  getTypeCollection :: e t -> TypeCollection (TypeCollectionSig t)

type TypeCollection sigs = Datatypes Datatype sigs

data Datatype (sig :: ([[Type]],*))
  = Datatype { datatypeName :: String
             , constructors :: Constrs Constr (Fst sig) (Snd sig) }

data Constr (sig :: ([Type],*))
  = Constr { conName :: String
           , conFields :: Args (Field (Snd sig)) (Fst sig)
           , construct :: Args ConcreteValue (Fst sig) -> Snd sig
           , conTest :: Snd sig -> Bool }

data Field a (t :: Type) = Field { fieldName :: String
                                 , fieldGet :: a -> ConcreteValue t }

data Value (con :: ([Type],*) -> *) (a :: Type) where
  BoolValue :: Bool -> Value con BoolType
  IntValue :: Integer -> Value con IntType
  RealValue :: Rational -> Value con RealType
  BitVecValue :: KnownNat n => Integer -> Value con (BitVecType n)
  ConstrValue :: (Typeable con,GetTypes arg,IsDatatype t)
              => con '(arg,t)
              -> Args (Value con) arg
              -> Value con (DataType t)

data ConcreteValue (a :: Type) where
  BoolValueC :: Bool -> ConcreteValue BoolType
  IntValueC :: Integer -> ConcreteValue IntType
  RealValueC :: Rational -> ConcreteValue RealType
  BitVecValueC :: KnownNat n => Integer -> ConcreteValue (BitVecType n)
  ConstrValueC :: IsDatatype t => t -> ConcreteValue (DataType t)

data AnyValue (con :: ([Type],*) -> *) = forall (t :: Type). GetType t => AnyValue (Value con t)

data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: KnownNat n => Integer -> Repr (BitVecType n)
  ArrayRepr :: (GetTypes idx,GetType val) => Args Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: IsDatatype dt => Datatype '(DatatypeSig dt,dt) -> Repr (DataType dt)

data Args (e :: Type -> *) (a :: [Type]) where
  NoArg :: Args e '[]
  Arg :: (GetType t,GetTypes ts) => e t -> Args e ts -> Args e (t ': ts)
  deriving Typeable

data Constrs (con :: ([Type],*) -> *) (a :: [[Type]]) t where
  NoCon :: Constrs con '[] t
  ConsCon :: GetTypes arg => con '(arg,dt) -> Constrs con args dt
          -> Constrs con (arg ': args) dt

data Datatypes (dts :: ([[Type]],*) -> *) (sigs :: [([[Type]],*)]) where
  NoDts :: Datatypes dts '[]
  ConsDts :: IsDatatype dt
          => dts '(DatatypeSig dt,dt)
          -> Datatypes dts sigs
          -> Datatypes dts ('(DatatypeSig dt,dt) ': sigs)

class Typeable t => GetType (t :: Type) where
  getType :: Repr t

data FunRepr (sig :: ([Type],Type)) where
  FunRepr :: Args Repr arg -> Repr tp -> FunRepr '(arg,tp)

instance GetType BoolType where
  getType = BoolRepr
instance GetType IntType where
  getType = IntRepr
instance GetType RealType where
  getType = RealRepr
instance (KnownNat n,Typeable n) => GetType (BitVecType n) where
  getType = BitVecRepr (natVal (Proxy::Proxy n)) ::Repr (BitVecType n)
instance (GetTypes idx,GetType el) => GetType (ArrayType idx el) where
  getType = ArrayRepr (getTypes ::Args Repr idx)
            (getType::Repr el) :: Repr (ArrayType idx el)
instance IsDatatype t => GetType (DataType t) where
  getType = DataRepr (getDatatype (Proxy::Proxy t)) :: Repr (DataType t)

getTypeOf :: GetType t => p t -> Repr t
getTypeOf _ = getType

class Typeable t => GetTypes (t :: [Type]) where
  type Lifted t (idx :: [Type]) :: [Type]
  getTypes :: Args Repr t
  getTypeConstr :: GetTypes idx => p t -> q idx -> Dict (GetTypes (Lifted t idx))

instance GetTypes '[] where
  type Lifted '[] idx = '[]
  getTypes = NoArg
  getTypeConstr _ _ = Dict

instance (GetType t,GetTypes ts) => GetTypes (t ': ts) where
  type Lifted (a ': b) idx = (ArrayType idx a) ': (Lifted b idx)
  getTypes = Arg (getType :: Repr t) (getTypes :: Args Repr ts) :: Args Repr (t ': ts)
  getTypeConstr (_::p (a ': b)) pidx = case getTypeConstr (Proxy::Proxy b) pidx of
    Dict -> Dict

getTypesOf :: GetTypes t => p t -> Args Repr t
getTypesOf _ = getTypes

instance GEq con => GEq (Value con) where
  geq (BoolValue v1) (BoolValue v2) = if v1==v2 then Just Refl else Nothing
  geq (IntValue v1) (IntValue v2) = if v1==v2 then Just Refl else Nothing
  geq (RealValue v1) (RealValue v2) = if v1==v2 then Just Refl else Nothing
  geq v1@(BitVecValue _) v2@(BitVecValue _) = do
    Refl <- cmp v1 v2
    return Refl
    where
      cmp :: Value con (BitVecType bw1) -> Value con (BitVecType bw2)
          -> Maybe (Value con (BitVecType bw1) :~: Value con (BitVecType bw2))
      cmp (BitVecValue v1 :: Value con (BitVecType bw1))
          (BitVecValue v2 :: Value con (BitVecType bw2)) = do
        Refl <- eqT :: Maybe (bw1 :~: bw2)
        if v1==v2 then Just Refl else Nothing
  geq (ConstrValue c1 arg1) (ConstrValue c2 arg2) = do
    Refl <- geq c1 c2
    Refl <- geq arg1 arg2
    return Refl
  geq _ _ = Nothing

instance GEq con => Eq (Value con t) where
  (==) = defaultEq

instance GEq ConcreteValue where
  geq (BoolValueC v1) (BoolValueC v2) = if v1==v2 then Just Refl else Nothing
  geq (IntValueC v1) (IntValueC v2) = if v1==v2 then Just Refl else Nothing
  geq (RealValueC v1) (RealValueC v2) = if v1==v2 then Just Refl else Nothing
  geq v1@(BitVecValueC _) v2@(BitVecValueC _) = do
    Refl <- cmp v1 v2
    return Refl
    where
      cmp :: ConcreteValue (BitVecType bw1) -> ConcreteValue (BitVecType bw2)
          -> Maybe (ConcreteValue (BitVecType bw1) :~: ConcreteValue (BitVecType bw2))
      cmp (BitVecValueC v1 :: ConcreteValue (BitVecType bw1))
          (BitVecValueC v2 :: ConcreteValue (BitVecType bw2)) = do
        Refl <- eqT :: Maybe (bw1 :~: bw2)
        if v1==v2 then Just Refl else Nothing
  geq (ConstrValueC (v1::a)) (ConstrValueC (v2::b)) = case (eqT :: Maybe (a :~: b)) of
    Just Refl -> if v1==v2
                 then Just Refl
                 else Nothing
    Nothing -> Nothing
  geq _ _ = Nothing

instance GCompare con => GCompare (Value con) where
  gcompare (BoolValue v1) (BoolValue v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (BoolValue _) _ = GLT
  gcompare _ (BoolValue _) = GGT
  gcompare (IntValue v1) (IntValue v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (IntValue _) _ = GLT
  gcompare _ (IntValue _) = GGT
  gcompare (RealValue v1) (RealValue v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (RealValue _) _ = GLT
  gcompare _ (RealValue _) = GGT
  gcompare v1@(BitVecValue v1') v2@(BitVecValue v2') = case v1 of
    (_::Value con (BitVecType bw1)) -> case v2 of
      (_::Value con (BitVecType bw2)) -> case eqT :: Maybe (bw1 :~: bw2) of
        Nothing -> if natVal (Proxy::Proxy bw1) < natVal (Proxy::Proxy bw2)
                   then GLT
                   else GGT
        Just Refl -> case compare v1' v2' of
          EQ -> GEQ
          LT -> GLT
          GT -> GGT
  gcompare (BitVecValue _) _ = GLT
  gcompare _ (BitVecValue _) = GGT
  gcompare (ConstrValue c1 arg1) (ConstrValue c2 arg2) = case gcompare c1 c2 of
    GLT -> GLT
    GGT -> GGT
    GEQ -> GEQ

instance GCompare ConcreteValue where
  gcompare (BoolValueC v1) (BoolValueC v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (BoolValueC _) _ = GLT
  gcompare _ (BoolValueC _) = GGT
  gcompare (IntValueC v1) (IntValueC v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (IntValueC _) _ = GLT
  gcompare _ (IntValueC _) = GGT
  gcompare (RealValueC v1) (RealValueC v2) = case compare v1 v2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (RealValueC _) _ = GLT
  gcompare _ (RealValueC _) = GGT
  gcompare v1@(BitVecValueC v1') v2@(BitVecValueC v2') = case v1 of
    (_::ConcreteValue (BitVecType bw1)) -> case v2 of
      (_::ConcreteValue (BitVecType bw2)) -> case eqT :: Maybe (bw1 :~: bw2) of
        Nothing -> if natVal (Proxy::Proxy bw1) < natVal (Proxy::Proxy bw2)
                   then GLT
                   else GGT
        Just Refl -> case compare v1' v2' of
          EQ -> GEQ
          LT -> GLT
          GT -> GGT
  gcompare (BitVecValueC _) _ = GLT
  gcompare _ (BitVecValueC _) = GGT
  gcompare (ConstrValueC (v1::a)) (ConstrValueC (v2::b)) = case (eqT :: Maybe (a :~: b)) of
    Just Refl -> case compare v1 v2 of
      EQ -> GEQ
      LT -> GLT
      GT -> GGT
    Nothing -> case compare (typeOf v1) (typeOf v2) of
      LT -> GLT
      GT -> GGT

instance GShow ConcreteValue where
  gshowsPrec p (BoolValueC v) = showsPrec p v
  gshowsPrec p (IntValueC v) = showsPrec p v
  gshowsPrec p (RealValueC v) = showsPrec p v
  gshowsPrec p (BitVecValueC v) = showsPrec p v
  gshowsPrec p (ConstrValueC v) = showsPrec p v

instance GEq e => GEq (Args e) where
  geq NoArg NoArg = Just Refl
  geq (Arg x xs) (Arg y ys) = do
    Refl <- geq x y
    Refl <- geq xs ys
    return Refl
  geq _ _ = Nothing

instance GCompare e => GCompare (Args e) where
  gcompare NoArg NoArg = GEQ
  gcompare NoArg _ = GLT
  gcompare _ NoArg = GGT
  gcompare (Arg x xs) (Arg y ys) = case gcompare x y of
    GEQ -> case gcompare xs ys of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance GEq Repr where
  geq BoolRepr BoolRepr = Just Refl
  geq IntRepr IntRepr = Just Refl
  geq RealRepr RealRepr = Just Refl
  geq b1@(BitVecRepr _) b2@(BitVecRepr _) = case b1 of
    (_::Repr (BitVecType n1)) -> case b2 of
      (_::Repr (BitVecType n2)) -> do
        Refl <- eqT :: Maybe (n1 :~: n2)
        return Refl
  geq (ArrayRepr idx1 val1) (ArrayRepr idx2 val2) = do
    Refl <- geq idx1 idx2
    Refl <- geq val1 val2
    return Refl
  geq d1@(DataRepr _) d2@(DataRepr _) = case d1 of
    (_::Repr (DataType dt1)) -> case d2 of
      (_::Repr (DataType dt2)) -> do
        Refl <- eqT :: Maybe (dt1 :~: dt2)
        return Refl
  geq _ _ = Nothing

instance GEq FunRepr where
  geq (FunRepr a1 r1) (FunRepr a2 r2) = do
    Refl <- geq a1 a2
    Refl <- geq r1 r2
    return Refl

instance GCompare Repr where
  gcompare BoolRepr BoolRepr = GEQ
  gcompare BoolRepr _ = GLT
  gcompare _ BoolRepr = GGT
  gcompare IntRepr IntRepr = GEQ
  gcompare IntRepr _ = GLT
  gcompare _ IntRepr = GGT
  gcompare RealRepr RealRepr = GEQ
  gcompare RealRepr _ = GLT
  gcompare _ RealRepr = GGT
  gcompare b1@(BitVecRepr _) b2@(BitVecRepr _) = case b1 of
    (_::Repr (BitVecType n1)) -> case b2 of
      (_::Repr (BitVecType n2)) -> case eqT :: Maybe (n1 :~: n2) of
        Just Refl -> GEQ
        Nothing -> if natVal (Proxy::Proxy n1) < natVal (Proxy::Proxy n2)
                   then GLT
                   else GGT
  gcompare (BitVecRepr _) _ = GLT
  gcompare _ (BitVecRepr _) = GGT
  gcompare (ArrayRepr idx1 val1) (ArrayRepr idx2 val2) = case gcompare idx1 idx2 of
    GEQ -> case gcompare val1 val2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (ArrayRepr _ _) _ = GLT
  gcompare _ (ArrayRepr _ _) = GGT
  gcompare d1@(DataRepr dt1) d2@(DataRepr dt2) = case d1 of
    (_::Repr (DataType dt1)) -> case d2 of
      (_::Repr (DataType dt2)) -> case eqT :: Maybe (dt1 :~: dt2) of
        Just Refl -> GEQ
        Nothing -> if datatypeName dt1 < datatypeName dt2
                   then GLT
                   else GGT

instance GCompare FunRepr where
  gcompare (FunRepr a1 r1) (FunRepr a2 r2) = case gcompare a1 a2 of
    GEQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance GShow con => Show (Value con tp) where
  showsPrec p (BoolValue b) = showsPrec p b
  showsPrec p (IntValue i) = showsPrec p i
  showsPrec p (RealValue i) = showsPrec p i
  showsPrec p (BitVecValue v :: Value con tp) = case getType :: Repr tp of
    BitVecRepr bw
      | bw `mod` 4 == 0 -> let str = showHex v ""
                               exp_len = bw `div` 4
                               len = genericLength str
                           in showString "#x" .
                              showString (genericReplicate (exp_len-len) '0') .
                              showString str
      | otherwise -> let str = showIntAtBase 2 (\x -> case x of
                                                        0 -> '0'
                                                        1 -> '1'
                                               ) v ""
                         len = genericLength str
                     in showString "#b" .
                        showString (genericReplicate (bw-len) '0') .
                        showString str
  showsPrec p (ConstrValue con args) = showParen (p>10) $
                                       showString "ConstrValue " .
                                       gshowsPrec 11 con.
                                       showChar ' ' .
                                       showListWith id (argsToList (showsPrec 0) args)

instance GShow con => GShow (Value con) where
  gshowsPrec = showsPrec

instance GShow e => Show (Args e sig) where
  showsPrec p NoArg = showString "NoArg"
  showsPrec p (Arg x xs) = showParen (p>10) $
                           showString "Arg " .
                           gshowsPrec 11 x . showChar ' ' .
                           showsPrec 11 xs

instance GShow e => GShow (Args e) where
  gshowsPrec = showsPrec

instance Show (Datatype sig) where
  showsPrec p dt = showParen (p>10) $
                   showString "Datatype " .
                   showString (datatypeName dt)

instance GShow Datatype where
  gshowsPrec = showsPrec

deriving instance Show (Repr t)

instance GShow Repr where
  gshowsPrec = showsPrec

mapArgs :: Monad m => (forall t. GetType t => e1 t -> m (e2 t))
        -> Args e1 arg
        -> m (Args e2 arg)
mapArgs f NoArg = return NoArg
mapArgs f (Arg x xs) = do
  x' <- f x
  xs' <- mapArgs f xs
  return (Arg x' xs')

mapAccumArgs :: Monad m => (forall t. GetType t => a -> e1 t -> m (a,e2 t))
             -> a
             -> Args e1 arg
             -> m (a,Args e2 arg)
mapAccumArgs f x NoArg = return (x,NoArg)
mapAccumArgs f x (Arg y ys) = do
  (nx1,ny) <- f x y
  (nx2,nys) <- mapAccumArgs f nx1 ys
  return (nx2,Arg ny nys)

withArgs :: (Monad m,GetTypes tps) => (forall t. GetType t => m (e t)) -> m (Args e tps)
withArgs f = mapArgs (const f) getTypes

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

argsEqM :: Monad m => (forall (t :: Type). GetType t => a t -> b t -> m Bool)
        -> Args a tps
        -> Args b tps
        -> m Bool
argsEqM _ NoArg NoArg = return True
argsEqM eq (Arg x xs) (Arg y ys) = do
  same <- eq x y
  if same
    then argsEqM eq xs ys
    else return False

mapValue :: (Monad m,Typeable con2)
         => (forall arg dt. GetTypes arg => con1 '(arg,dt) -> m (con2 '(arg,dt)))
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

findConstrByName :: String -> Datatype '(cons,dt)
                 -> (forall arg. GetTypes arg => Constr '(arg,dt) -> a) -> a
findConstrByName name dt f = find f (constructors dt)
  where
    find :: (forall arg. GetTypes arg => Constr '(arg,dt) -> a) -> Constrs Constr sigs dt -> a
    find f NoCon = error $ "smtlib2: Cannot find constructor "++name++" of "++datatypeName dt
    find f (ConsCon con cons)
      = if conName con == name
        then f con
        else find f cons

findConstrByName' :: (Typeable arg,Typeable dt) => String -> Datatype '(cons,dt)
                  -> Constr '(arg,dt)
findConstrByName' name dt = findConstrByName name dt
                            (\con -> case cast con of
                               Just con' -> con')
