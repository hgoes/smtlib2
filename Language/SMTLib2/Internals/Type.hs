module Language.SMTLib2.Internals.Type where

import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..),reifyList)
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.Proxy
import Data.Typeable
import Numeric
import Data.List (genericLength,genericReplicate)
import Data.GADT.Compare
import Data.GADT.Show

-- | Describes the kind of all SMT types.
--   It is only used in promoted form, for a concrete representation see 'Repr'.
data Type = BoolType
          | IntType
          | RealType
          | BitVecType Nat
          | ArrayType [Type] Type
          | forall a. DataType a
          deriving Typeable

type family Lifted (tps :: [Type]) (idx :: [Type]) :: [Type] where
  Lifted '[] idx = '[]
  Lifted (tp ': tps) idx = (ArrayType idx tp) ': Lifted tps idx

class Unlift (tps::[Type]) (idx::[Type]) where
  unliftType :: List Repr (Lifted tps idx) -> (List Repr tps,List Repr idx)
  unliftTypeWith :: List Repr (Lifted tps idx) -> List Repr tps -> List Repr idx

instance Unlift '[tp] idx where
  unliftType (ArrayRepr idx tp ::: Nil) = (tp ::: Nil,idx)
  unliftTypeWith (ArrayRepr idx tp ::: Nil) (tp' ::: Nil) = idx

instance Unlift (t2 ': ts) idx => Unlift (t1 ': t2 ': ts) idx where
  unliftType (ArrayRepr idx tp ::: ts)
    = let (tps,idx') = unliftType ts
      in (tp ::: tps,idx)
  unliftTypeWith (ArrayRepr idx tp ::: ts) (tp' ::: tps) = idx

type family Fst (a :: (p,q)) :: p where
  Fst '(x,y) = x

type family Snd (a :: (p,q)) :: q where
  Snd '(x,y) = y

class (Typeable t,Typeable (DatatypeSig t),Show t,Ord t) => IsDatatype t where
  type DatatypeSig t :: [[Type]]
  type TypeCollectionSig t :: [([[Type]],*)]
  getDatatype :: e t -> Datatype '(DatatypeSig t,t)
  getTypeCollection :: e t -> TypeCollection (TypeCollectionSig t)
  getConstructor :: t -> Constrs con (DatatypeSig t) t
                 -> (forall arg. con '(arg,t) -> List ConcreteValue arg -> a)
                 -> a

type TypeCollection sigs = Datatypes Datatype sigs

data Datatype (sig :: ([[Type]],*))
  = Datatype { datatypeName :: String
             , constructors :: Constrs Constr (Fst sig) (Snd sig) }

data Constr (sig :: ([Type],*))
  = Constr { conName :: String
           , conFields :: List (Field (Snd sig)) (Fst sig)
           , construct :: List ConcreteValue (Fst sig) -> Snd sig
           , conTest :: Snd sig -> Bool }

data Field a (t :: Type) = Field { fieldName :: String
                                 , fieldType :: Repr t
                                 , fieldGet :: a -> ConcreteValue t }

-- | Values that can be used as constants in expressions.
data Value (con :: ([Type],*) -> *) (a :: Type) where
  BoolValue :: Bool -> Value con BoolType
  IntValue :: Integer -> Value con IntType
  RealValue :: Rational -> Value con RealType
  BitVecValue :: Integer -> Natural n -> Value con (BitVecType n)
  ConstrValue :: (Typeable con,IsDatatype t)
              => con '(arg,t)
              -> List (Value con) arg
              -> Value con (DataType t)

-- | Concrete values are like `Value`s, except that the SMT-specific
--   constructors are replaced with the actual datatypes.
data ConcreteValue (a :: Type) where
  BoolValueC :: Bool -> ConcreteValue BoolType
  IntValueC :: Integer -> ConcreteValue IntType
  RealValueC :: Rational -> ConcreteValue RealType
  BitVecValueC :: Integer -> Natural n -> ConcreteValue (BitVecType n)
  ConstrValueC :: IsDatatype t => t -> ConcreteValue (DataType t)

data AnyValue (con :: ([Type],*) -> *) = forall (t :: Type). AnyValue (Value con t)

-- | A concrete representation of an SMT type.
--   For aesthetic reasons, it's recommended to use the functions 'bool', 'int', 'real', 'bitvec' or 'array'.
data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: Natural n -> Repr (BitVecType n)
  ArrayRepr :: List Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: IsDatatype dt => Datatype '(DatatypeSig dt,dt) -> Repr (DataType dt)

data NumRepr (t :: Type) where
  NumInt :: NumRepr IntType
  NumReal :: NumRepr RealType

data Constrs (con :: ([Type],*) -> *) (a :: [[Type]]) t where
  NoCon :: Constrs con '[] t
  ConsCon :: con '(arg,dt) -> Constrs con args dt
          -> Constrs con (arg ': args) dt

data Datatypes (dts :: ([[Type]],*) -> *) (sigs :: [([[Type]],*)]) where
  NoDts :: Datatypes dts '[]
  ConsDts :: IsDatatype dt
          => dts '(DatatypeSig dt,dt)
          -> Datatypes dts sigs
          -> Datatypes dts ('(DatatypeSig dt,dt) ': sigs)

data FunRepr (sig :: ([Type],Type)) where
  FunRepr :: List Repr arg -> Repr tp -> FunRepr '(arg,tp)

class GetType v where
  getType :: v tp -> Repr tp

class GetFunType fun where
  getFunType :: fun '(arg,res) -> (List Repr arg,Repr res)

class GetConType con where
  getConType :: IsDatatype dt => con '(arg,dt) -> (List Repr arg,Datatype '(DatatypeSig dt,dt))

class GetFieldType field where
  getFieldType :: IsDatatype dt => field '(dt,tp) -> (Datatype '(DatatypeSig dt,dt),Repr tp)

-- | A representation of the SMT Bool type.
--   Holds the values 'Language.SMTLib2.Internals.Interface.true' or 'Language.SMTLib2.Internals.Interface.false'.
bool :: Repr BoolType
bool = BoolRepr

int :: Repr IntType
int = IntRepr

real :: Repr RealType
real = RealRepr

bitvec :: Natural bw -> Repr (BitVecType bw)
bitvec = BitVecRepr

array :: List Repr idx -> Repr el -> Repr (ArrayType idx el)
array = ArrayRepr

-- | Get a concrete representation for a type.
reifyType :: Type -> (forall tp. Repr tp -> a) -> a
reifyType BoolType f = f BoolRepr
reifyType IntType f = f IntRepr
reifyType RealType f = f RealRepr
reifyType (BitVecType bw) f
  = reifyNat bw $ \bw' -> f (BitVecRepr bw')
reifyType (ArrayType idx el) f
  = reifyList reifyType idx $
    \idx' -> reifyType el $
             \el' -> f (ArrayRepr idx' el')
reifyType (DataType _) _ = error $ "reifyType: Cannot reify user defined datatypes yet."

instance GetType Repr where
  getType = id

instance GetType (Value con) where
  getType = valueType

instance GetType ConcreteValue where
  getType = valueTypeC

instance GEq con => GEq (Value con) where
  geq (BoolValue v1) (BoolValue v2) = if v1==v2 then Just Refl else Nothing
  geq (IntValue v1) (IntValue v2) = if v1==v2 then Just Refl else Nothing
  geq (RealValue v1) (RealValue v2) = if v1==v2 then Just Refl else Nothing
  geq (BitVecValue v1 bw1) (BitVecValue v2 bw2) = do
    Refl <- geq bw1 bw2
    if v1==v2
      then return Refl
      else Nothing
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
  geq (BitVecValueC v1 bw1) (BitVecValueC v2 bw2) = do
    Refl <- geq bw1 bw2
    if v1==v2
      then return Refl
      else Nothing
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
  gcompare (BitVecValue v1 bw1) (BitVecValue v2 bw2)
    = case gcompare bw1 bw2 of
    GEQ -> case compare v1 v2 of
      EQ -> GEQ
      LT -> GLT
      GT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (BitVecValue _ _) _ = GLT
  gcompare _ (BitVecValue _ _) = GGT
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
  gcompare (BitVecValueC v1 bw1) (BitVecValueC v2 bw2) = case gcompare bw1 bw2 of
    GEQ -> case compare v1 v2 of
      EQ -> GEQ
      LT -> GLT
      GT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (BitVecValueC _ _) _ = GLT
  gcompare _ (BitVecValueC _ _) = GGT
  gcompare (ConstrValueC (v1::a)) (ConstrValueC (v2::b)) = case (eqT :: Maybe (a :~: b)) of
    Just Refl -> case compare v1 v2 of
      EQ -> GEQ
      LT -> GLT
      GT -> GGT
    Nothing -> case compare (typeOf v1) (typeOf v2) of
      LT -> GLT
      GT -> GGT

instance GEq Repr where
  geq BoolRepr BoolRepr = Just Refl
  geq IntRepr IntRepr = Just Refl
  geq RealRepr RealRepr = Just Refl
  geq (BitVecRepr bw1) (BitVecRepr bw2) = do
    Refl <- geq bw1 bw2
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

instance Eq (Repr tp) where
  (==) _ _ = True

instance GEq NumRepr where
  geq NumInt NumInt = Just Refl
  geq NumReal NumReal = Just Refl
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
  gcompare (BitVecRepr bw1) (BitVecRepr bw2) = case gcompare bw1 bw2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
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

instance Ord (Repr tp) where
  compare _ _ = EQ

instance GCompare NumRepr where
  gcompare NumInt NumInt = GEQ
  gcompare NumInt _ = GLT
  gcompare _ NumInt = GGT
  gcompare NumReal NumReal = GEQ

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
  showsPrec p (BitVecValue v n)
    | bw `mod` 4 == 0 = let str = showHex rv ""
                            exp_len = bw `div` 4
                            len = genericLength str
                        in showString "#x" .
                           showString (genericReplicate (exp_len-len) '0') .
                           showString str
    | otherwise = let str = showIntAtBase 2 (\x -> case x of
                                              0 -> '0'
                                              1 -> '1'
                                            ) rv ""
                      len = genericLength str
                  in showString "#b" .
                     showString (genericReplicate (bw-len) '0') .
                     showString str
    where
      bw = naturalToInteger n
      rv = v `mod` 2^bw
  showsPrec p (ConstrValue con args) = showParen (p>10) $
                                       showString "ConstrValue " .
                                       gshowsPrec 11 con.
                                       showChar ' ' .
                                       showsPrec 11 args

instance GShow con => GShow (Value con) where
  gshowsPrec = showsPrec

instance Show (ConcreteValue t) where
  showsPrec p (BoolValueC b) = showsPrec p b
  showsPrec p (IntValueC i) = showsPrec p i
  showsPrec p (RealValueC i) = showsPrec p i
  showsPrec p (BitVecValueC v n)
    | bw `mod` 4 == 0 = let str = showHex rv ""
                            exp_len = bw `div` 4
                            len = genericLength str
                        in showString "#x" .
                           showString (genericReplicate (exp_len-len) '0') .
                           showString str
    | otherwise = let str = showIntAtBase 2 (\x -> case x of
                                              0 -> '0'
                                              1 -> '1'
                                            ) rv ""
                      len = genericLength str
                  in showString "#b" .
                     showString (genericReplicate (bw-len) '0') .
                     showString str
    where
      bw = naturalToInteger n
      rv = v `mod` 2^bw
  showsPrec p (ConstrValueC val) = showsPrec p val

instance GShow ConcreteValue where
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

deriving instance Show (NumRepr t)

instance GShow NumRepr where
  gshowsPrec = showsPrec

mapValue :: (Monad m,Typeable con2)
         => (forall arg dt. con1 '(arg,dt) -> m (con2 '(arg,dt)))
         -> Value con1 a
         -> m (Value con2 a)
mapValue _ (BoolValue b) = return (BoolValue b)
mapValue _ (IntValue i) = return (IntValue i)
mapValue _ (RealValue r) = return (RealValue r)
mapValue _ (BitVecValue b bw) = return (BitVecValue b bw)
mapValue f (ConstrValue con args) = do
  con' <- f con
  args' <- List.mapM (mapValue f) args
  return (ConstrValue con' args')

findConstrByName :: String -> Datatype '(cons,dt)
                 -> (forall arg. Constr '(arg,dt) -> a) -> a
findConstrByName name dt f = find f (constructors dt)
  where
    find :: (forall arg. Constr '(arg,dt) -> a) -> Constrs Constr sigs dt -> a
    find f NoCon = error $ "smtlib2: Cannot find constructor "++name++" of "++datatypeName dt
    find f (ConsCon con cons)
      = if conName con == name
        then f con
        else find f cons

{-findConstrByName' :: (Typeable arg,Typeable dt) => String -> Datatype '(cons,dt)
                  -> Constr '(arg,dt)
findConstrByName' name dt = findConstrByName name dt
                            (\con -> case cast con of
                               Just con' -> con')-}

valueToConcrete :: (Monad m)
                => (forall arg tp. (IsDatatype tp)
                    => con '(arg,tp)
                    -> List ConcreteValue arg
                    -> m tp)
                -> Value con t -> m (ConcreteValue t)
valueToConcrete _ (BoolValue v) = return (BoolValueC v)
valueToConcrete _ (IntValue v) = return (IntValueC v)
valueToConcrete _ (RealValue v) = return (RealValueC v)
valueToConcrete _ (BitVecValue v bw) = return (BitVecValueC v bw)
valueToConcrete f (ConstrValue con arg) = do
  arg' <- List.mapM (valueToConcrete f) arg
  res <- f con arg'
  return (ConstrValueC res)

valueFromConcrete :: (Monad m,Typeable con)
                  => (forall tp a. IsDatatype tp
                      => tp
                      -> (forall arg.
                          con '(arg,tp)
                          -> List ConcreteValue arg
                          -> m a)
                      -> m a)
                  -> ConcreteValue t
                  -> m (Value con t)
valueFromConcrete _ (BoolValueC v) = return (BoolValue v)
valueFromConcrete _ (IntValueC v) = return (IntValue v)
valueFromConcrete _ (RealValueC v) = return (RealValue v)
valueFromConcrete _ (BitVecValueC v bw) = return (BitVecValue v bw)
valueFromConcrete f (ConstrValueC v)
  = f v (\con arg -> do
            arg' <- List.mapM (valueFromConcrete f) arg
            return (ConstrValue con arg'))
                                  
valueType :: Value con tp -> Repr tp
valueType (BoolValue _) = BoolRepr
valueType (IntValue _) = IntRepr
valueType (RealValue _) = RealRepr
valueType (BitVecValue _ bw) = BitVecRepr bw
valueType (ConstrValue (_::con '(arg,t)) _) = DataRepr (getDatatype (Proxy::Proxy t))

valueTypeC :: ConcreteValue tp -> Repr tp
valueTypeC (BoolValueC _) = BoolRepr
valueTypeC (IntValueC _) = IntRepr
valueTypeC (RealValueC _) = RealRepr
valueTypeC (BitVecValueC _ bw) = BitVecRepr bw
valueTypeC (ConstrValueC _) = DataRepr (getDatatype Proxy)

liftType :: List Repr tps -> List Repr idx -> List Repr (Lifted tps idx)
liftType Nil idx = Nil
liftType (x ::: xs) idx = (ArrayRepr idx x) ::: (liftType xs idx)

numRepr :: NumRepr tp -> Repr tp
numRepr NumInt = IntRepr
numRepr NumReal = RealRepr

asNumRepr :: Repr tp -> Maybe (NumRepr tp)
asNumRepr IntRepr = Just NumInt
asNumRepr RealRepr = Just NumReal
asNumRepr _ = Nothing

getTypes :: GetType e => List e tps -> List Repr tps
getTypes Nil = Nil
getTypes (x ::: xs) = getType x ::: getTypes xs
