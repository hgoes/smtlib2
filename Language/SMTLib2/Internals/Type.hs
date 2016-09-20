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
import Data.Functor.Identity
import Data.Graph
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Bits

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

class (Typeable (Datatype dt),GCompare (Constr dt),Show (Datatype dt))
      => IsDatatype (dt :: (Type -> *) -> *) where
  type Signature dt :: [[Type]]
  data Datatype dt
  data Constr dt (csig :: [Type])
  data Field dt (csig :: [Type]) (tp :: Type)
  -- | The name of the datatype. Must be unique.
  datatypeName   :: Datatype dt -> String
  constructors   :: Datatype dt -> List (Constr dt) (Signature dt)
  constrName     :: Constr dt csig -> String
  constrTest     :: dt e -> Constr dt csig -> Bool
  constrFields   :: Constr dt csig -> List (Field dt csig) csig
  constrApply    :: ConApp dt e -> dt e
  constrGet      :: dt e -> ConApp dt e
  constrDatatype :: Constr dt csig -> Datatype dt
  fieldName      :: Field dt csig tp -> String
  fieldType      :: Field dt csig tp -> Repr tp
  fieldGet       :: dt e -> Field dt csig tp -> e tp
  fieldConstr    :: Field dt csig tp -> Constr dt csig
  compareField   :: Field dt csig1 tp1 -> Field dt csig2 tp2
                 -> (GOrdering csig1 csig2,Maybe (tp1 :~: tp2))

data ConApp dt e = forall csig. ConApp { constructor :: Constr dt csig
                                       , arguments   :: List e csig }

data AnyDatatype = forall dt. IsDatatype dt => AnyDatatype (Datatype dt)
data AnyConstr = forall dt csig. IsDatatype dt => AnyConstr (Constr dt csig)
data AnyField = forall dt csig tp. IsDatatype dt => AnyField (Field dt csig tp)

data TypeRegistry dt con field = TypeRegistry { allDatatypes :: Map dt AnyDatatype
                                              , revDatatypes :: Map AnyDatatype dt
                                              , allConstructors :: Map con AnyConstr
                                              , revConstructors :: Map AnyConstr con
                                              , allFields :: Map field AnyField
                                              , revFields :: Map AnyField field }

emptyTypeRegistry :: TypeRegistry dt con field
emptyTypeRegistry = TypeRegistry Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

dependencies :: IsDatatype dt
             => Set String -- ^ Already registered datatypes
             -> Datatype dt
             -> (Set String,[[AnyDatatype]])
dependencies known p = (known',dts)
  where
    dts = fmap (\scc -> fmap (\(dt,_,_) -> dt) $ flattenSCC scc) sccs
    sccs = stronglyConnCompR edges
    (known',edges) = dependencies' known p
    
    dependencies' :: IsDatatype dt => Set String -> Datatype dt -> (Set String,[(AnyDatatype,String,[String])])
    dependencies' known dt
      | Set.member (datatypeName dt) known = (known,[])
      | otherwise = let name = datatypeName dt
                        known1 = Set.insert name known
                        deps = concat $ runIdentity $ List.toList
                               (\con -> return $ catMaybes $ runIdentity $ List.toList
                                        (\field -> case fieldType field of
                                                     DataRepr dep -> return $ Just (AnyDatatype dep)
                                                     _ -> return $ Nothing
                                        ) (constrFields con)
                               ) (constructors dt)
                        (known2,edges) = foldl (\(known,lst) (AnyDatatype dt)
                                                -> let (nknown,edges) = dependencies' known dt
                                                   in (nknown,edges++lst)
                                               ) (known1,[]) deps
                    in (known2,(AnyDatatype dt,name,[ datatypeName dt | AnyDatatype dt <- deps ]):edges)

signature :: IsDatatype dt => Datatype dt -> List (List Repr) (Signature dt)
signature dt
  = runIdentity $ List.mapM (\con -> List.mapM (\f -> return (fieldType f)
                                               ) (constrFields con)
                            ) (constructors dt)

constrSig :: IsDatatype dt => Constr dt sig -> List Repr sig
constrSig constr = runIdentity $ List.mapM (\f -> return (fieldType f)) (constrFields constr)

constrEq :: (IsDatatype dt1,IsDatatype dt2) => Constr dt1 sig1 -> Constr dt2 sig2
         -> Maybe (Constr dt1 sig1 :~: Constr dt2 sig2)
constrEq (c1 :: Constr dt1 sig1) (c2 :: Constr dt2 sig2) = do
  Refl <- eqT :: Maybe (Datatype dt1 :~: Datatype dt2)
  Refl <- geq c1 c2
  return Refl
  
constrCompare :: (IsDatatype dt1,IsDatatype dt2) => Constr dt1 sig1 -> Constr dt2 sig2
              -> GOrdering (Constr dt1 sig1) (Constr dt2 sig2)
constrCompare (c1 :: Constr dt1 sig1) (c2 :: Constr dt2 sig2)
  = case eqT :: Maybe (Datatype dt1 :~: Datatype dt2) of
  Just Refl -> case gcompare c1 c2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  Nothing -> case compare (typeOf (Proxy::Proxy (Datatype dt1))) (typeOf (Proxy::Proxy (Datatype dt2))) of
    LT -> GLT
    GT -> GGT

fieldEq :: (IsDatatype dt1,IsDatatype dt2) => Field dt1 sig1 tp1 -> Field dt2 sig2 tp2
        -> Maybe (Field dt1 sig1 tp1 :~: Field dt2 sig2 tp2)
fieldEq (f1 :: Field dt1 sig1 tp1) (f2 :: Field dt2 sig2 tp2) = do
  Refl <- eqT :: Maybe (Datatype dt1 :~: Datatype dt2)
  case compareField f1 f2 of
    (GEQ,Just Refl) -> return Refl
    _ -> Nothing

fieldCompare :: (IsDatatype dt1,IsDatatype dt2) => Field dt1 sig1 tp1 -> Field dt2 sig2 tp2
             -> GOrdering (Field dt1 sig1 tp1) (Field dt2 sig2 tp2)
fieldCompare (f1 :: Field dt1 sig1 tp1) (f2 :: Field dt2 sig2 tp2) = case eqT :: Maybe (Datatype dt1 :~: Datatype dt2) of
  Just Refl -> case compareField f1 f2 of
    (GEQ,Just Refl) -> GEQ
    (GLT,_) -> GLT
    (GGT,_) -> GGT
  Nothing -> case compare (typeOf (Proxy::Proxy (Datatype dt1))) (typeOf (Proxy::Proxy (Datatype dt2))) of
    LT -> GLT
    GT -> GGT

registerType :: (Monad m,IsDatatype tp,Ord dt,Ord con,Ord field) => dt
             -> (forall sig. Constr tp sig -> m con)
             -> (forall sig tp'. Field tp sig tp' -> m field)
             -> Datatype tp -> TypeRegistry dt con field
             -> m (TypeRegistry dt con field)
registerType i f g dt reg
  = List.foldM
    (\reg con -> do
        c <- f con
        let reg' = reg { allConstructors = Map.insert c (AnyConstr con) (allConstructors reg) }
        List.foldM (\reg field -> do
                       fi <- g field
                       return $ reg { allFields = Map.insert fi (AnyField field) (allFields reg) }
                   ) reg' (constrFields con)
    ) reg1 (constructors dt)
  where
    reg1 = reg { allDatatypes = Map.insert i (AnyDatatype dt) (allDatatypes reg)
               , revDatatypes = Map.insert (AnyDatatype dt) i (revDatatypes reg) }

registerTypeName :: IsDatatype dt => Datatype dt
                 -> TypeRegistry String String String
                 -> TypeRegistry String String String
registerTypeName dt reg = runIdentity (registerType (datatypeName dt) (return . constrName) (return . fieldName) dt reg)

instance Eq AnyDatatype where
  (==) (AnyDatatype x) (AnyDatatype y) = datatypeName x == datatypeName y

instance Eq AnyConstr where
  (==) (AnyConstr c1) (AnyConstr c2) = constrName c1 == constrName c2

instance Eq AnyField where
  (==) (AnyField f1) (AnyField f2) = fieldName f1 == fieldName f2

instance Ord AnyDatatype where
  compare (AnyDatatype x) (AnyDatatype y) = compare (datatypeName x) (datatypeName y)

instance Ord AnyConstr where
  compare (AnyConstr c1) (AnyConstr c2) = compare (constrName c1) (constrName c2)

instance Ord AnyField where
  compare (AnyField f1) (AnyField f2) = compare (fieldName f1) (fieldName f2)

data DynamicDatatype (sig :: [[Type]])
  = DynDatatype { dynDatatypeSig :: List DynamicConstructor sig
                , dynDatatypeName :: String }

data DynamicConstructor (sig :: [Type])
  = DynConstructor { dynConstrSig :: List DynamicField sig
                   , dynConstrName :: String }

data DynamicField (sig :: Type)
  = DynField { dynFieldType :: Repr sig
             , dynFieldName :: String }

data DynamicValue (sig :: [[Type]]) e
  = forall n. DynValue { dynValueType :: DynamicDatatype sig
                       , dynValueConstr :: Natural n
                       , dynValueArgs :: List e (List.Index sig n) }

instance Typeable sig => IsDatatype (DynamicValue sig) where
  type Signature (DynamicValue sig) = sig
  data Datatype (DynamicValue sig) = DynDatatypeInfo (DynamicDatatype sig)
  data Constr (DynamicValue sig) csig where
    DynConstr :: DynamicDatatype sig -> Natural n
              -> Constr (DynamicValue sig) (List.Index sig n)
  data Field (DynamicValue sig) csig fsig where
    DynField' :: DynamicDatatype sig -> Natural n -> Natural m
              -> Field (DynamicValue sig) (List.Index sig n) (List.Index (List.Index sig n) m)
  datatypeName (DynDatatypeInfo dt) = dynDatatypeName dt
  constructors (DynDatatypeInfo dt) = runIdentity $ List.mapIndexM
    (\idx _ -> return (DynConstr dt idx))
    (dynDatatypeSig dt)
  constrName (DynConstr dt idx) = dynConstrName $ List.index (dynDatatypeSig dt) idx
  constrTest (DynValue { dynValueConstr = con }) (DynConstr _ idx) = case geq con idx of
    Just Refl -> True
    Nothing -> False
  constrFields (DynConstr dt idx) = runIdentity $ List.mapIndexM
    (\idx' _ -> return (DynField' dt idx idx'))
    (dynConstrSig $ List.index (dynDatatypeSig dt) idx)
  constrApply (ConApp (DynConstr dt idx) arg) = DynValue { dynValueType = dt
                                                         , dynValueConstr = idx
                                                         , dynValueArgs = arg }
  constrGet (DynValue dt idx arg) = ConApp (DynConstr dt idx) arg
  constrDatatype (DynConstr dt _) = DynDatatypeInfo dt
  fieldName (DynField' dt n m) = dynFieldName $ List.index (dynConstrSig $ List.index (dynDatatypeSig dt) n) m
  fieldType (DynField' dt n m) = dynFieldType $ List.index (dynConstrSig $ List.index (dynDatatypeSig dt) n) m
  fieldGet (DynValue dt idx arg) (DynField' dt' n m) = case geq n idx of
    Just Refl -> List.index arg m
  fieldConstr (DynField' dt n m) = DynConstr dt n
  compareField (DynField' _ n1 m1) (DynField' _ n2 m2) = case gcompare n1 n2 of
    GEQ -> case gcompare m1 m2 of
      GEQ -> (GEQ,Just Refl)
      GLT -> (GLT,Nothing)
      GGT -> (GGT,Nothing)
    GLT -> (GLT,Nothing)
    GGT -> (GGT,Nothing)

instance Show (Datatype (DynamicValue sig)) where
  showsPrec p (DynDatatypeInfo dt) = showString (dynDatatypeName dt)

instance GEq (Constr (DynamicValue sig)) where
  geq (DynConstr _ x) (DynConstr _ y) = do
    Refl <- geq x y
    return Refl

instance GCompare (Constr (DynamicValue sig)) where
  gcompare (DynConstr _ x) (DynConstr _ y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

-- | Values that can be used as constants in expressions.
data Value (a :: Type) where
  BoolValue :: Bool -> Value BoolType
  IntValue :: Integer -> Value IntType
  RealValue :: Rational -> Value RealType
  BitVecValue :: Integer -> Natural n -> Value (BitVecType n)
  DataValue :: IsDatatype dt => Datatype dt -> dt Value -> Value (DataType dt)

pattern ConstrValue con args <- DataValue tp (constrGet -> ConApp con args) where
  ConstrValue con args = DataValue (constrDatatype con) (constrApply (ConApp con args))

data AnyValue = forall (t :: Type). AnyValue (Value t)

-- | A concrete representation of an SMT type.
--   For aesthetic reasons, it's recommended to use the functions 'bool', 'int', 'real', 'bitvec' or 'array'.
data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: Natural n -> Repr (BitVecType n)
  ArrayRepr :: List Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: IsDatatype dt => Datatype dt -> Repr (DataType dt)

data NumRepr (t :: Type) where
  NumInt :: NumRepr IntType
  NumReal :: NumRepr RealType

data FunRepr (sig :: ([Type],Type)) where
  FunRepr :: List Repr arg -> Repr tp -> FunRepr '(arg,tp)

class GetType v where
  getType :: v tp -> Repr tp

class GetFunType fun where
  getFunType :: fun '(arg,res) -> (List Repr arg,Repr res)

-- | A representation of the SMT Bool type.
--   Holds the values 'Language.SMTLib2.true' or 'Language.SMTLib2.Internals.false'.
--   Constants can be created using 'Language.SMTLib2.cbool'.
bool :: Repr BoolType
bool = BoolRepr

-- | A representation of the SMT Int type.
--   Holds the unbounded positive and negative integers.
--   Constants can be created using 'Language.SMTLib2.cint'.
int :: Repr IntType
int = IntRepr

-- | A representation of the SMT Real type.
--   Holds positive and negative reals x/y where x and y are integers.
--   Constants can be created using 'Language.SMTLib2.creal'.
real :: Repr RealType
real = RealRepr

-- | A representation of the SMT BitVec type.
--   Holds bitvectors (a vector of booleans) of a certain bitwidth.
--   Constants can be created using 'Language.SMTLib2.cbv'.
bitvec :: Natural bw -- ^ The width of the bitvector
       -> Repr (BitVecType bw)
bitvec = BitVecRepr

-- | A representation of the SMT Array type.
--   Has a list of index types and an element type.
--   Stores one value of the element type for each combination of the index types.
--   Constants can be created using 'Language.SMTLib2.constArray'.
array :: List Repr idx -> Repr el -> Repr (ArrayType idx el)
array = ArrayRepr

-- | A representation of a user-defined datatype.
dt :: IsDatatype dt => Datatype dt -> Repr (DataType dt)
dt = DataRepr

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

instance GetType Value where
  getType = valueType

instance GEq Value where
  geq (BoolValue v1) (BoolValue v2) = if v1==v2 then Just Refl else Nothing
  geq (IntValue v1) (IntValue v2) = if v1==v2 then Just Refl else Nothing
  geq (RealValue v1) (RealValue v2) = if v1==v2 then Just Refl else Nothing
  geq (BitVecValue v1 bw1) (BitVecValue v2 bw2) = do
    Refl <- geq bw1 bw2
    if v1==v2
      then return Refl
      else Nothing
  geq (ConstrValue c1 arg1) (ConstrValue c2 arg2) = do
    Refl <- constrEq c1 c2
    Refl <- geq arg1 arg2
    return Refl
  geq _ _ = Nothing

instance Eq (Value t) where
  (==) = defaultEq

instance GCompare Value where
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
  gcompare (ConstrValue c1 arg1) (ConstrValue c2 arg2) = case constrCompare c1 c2 of
    GEQ -> case gcompare arg1 arg2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance Ord (Value t) where
  compare = defaultCompare

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
  geq (DataRepr (_::Datatype dt1)) (DataRepr (_::Datatype dt2))
    = case eqT :: Maybe (Datatype dt1 :~: Datatype dt2) of
    Just Refl -> Just Refl
    Nothing -> Nothing
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
  gcompare (DataRepr (dt1 :: Datatype dt1)) (DataRepr (dt2 :: Datatype dt2)) = case eqT of
    Just (Refl :: Datatype dt1 :~: Datatype dt2) -> GEQ
    Nothing -> case compare (datatypeName dt1) (datatypeName dt2) of
      LT -> GLT
      GT -> GGT

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

instance Show (Value tp) where
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
    showString (constrName con).
    showChar ' ' .
    showsPrec 11 args

instance GShow Value where
  gshowsPrec = showsPrec

instance Show (Repr t) where
  showsPrec _ BoolRepr = showString "bool"
  showsPrec _ IntRepr = showString "int"
  showsPrec _ RealRepr = showString "real"
  showsPrec p (BitVecRepr n) = showParen (p>10) $
    showString "bitvec " .
    showsPrec 11 n
  showsPrec p (ArrayRepr idx el) = showParen (p>10) $
    showString "array " .
    showsPrec 11 idx . showChar ' ' .
    showsPrec 11 el
  showsPrec p (DataRepr dt) = showParen (p>10) $
    showString "dt " .
    showString (datatypeName dt)

instance GShow Repr where
  gshowsPrec = showsPrec

deriving instance Show (NumRepr t)

instance GShow NumRepr where
  gshowsPrec = showsPrec
                                  
valueType :: Value tp -> Repr tp
valueType (BoolValue _) = BoolRepr
valueType (IntValue _) = IntRepr
valueType (RealValue _) = RealRepr
valueType (BitVecValue _ bw) = BitVecRepr bw
valueType (DataValue tp _) = DataRepr tp

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

-- | Determine the number of elements a type contains.
--   'Nothing' means the type has infinite elements.
typeSize :: Repr tp -> Maybe Integer
typeSize BoolRepr = Just 2
typeSize IntRepr = Nothing
typeSize RealRepr = Nothing
typeSize (BitVecRepr bw) = Just $ 2^(naturalToInteger bw)
typeSize (ArrayRepr idx el) = do
  idxSz <- List.toList typeSize idx
  elSz <- typeSize el
  return $ product (elSz:idxSz)
typeSize (DataRepr dt) = do
  conSz <- List.toList constrSize (constructors dt)
  return $ sum conSz
  where
    constrSize :: IsDatatype dt => Constr dt sig -> Maybe Integer
    constrSize con = do
      fieldSz <- List.toList fieldSize (constrFields con)
      return $ product fieldSz
    fieldSize :: IsDatatype dt => Field dt csig tp -> Maybe Integer
    fieldSize field = typeSize $ fieldType field

instance Enum (Value BoolType) where
  succ (BoolValue x) = BoolValue (succ x)
  pred (BoolValue x) = BoolValue (pred x)
  toEnum i = BoolValue (toEnum i)
  fromEnum (BoolValue x) = fromEnum x
  enumFrom (BoolValue x) = fmap BoolValue (enumFrom x)
  enumFromThen (BoolValue x) (BoolValue y) = fmap BoolValue (enumFromThen x y)
  enumFromTo (BoolValue x) (BoolValue y) = fmap BoolValue (enumFromTo x y)
  enumFromThenTo (BoolValue x) (BoolValue y) (BoolValue z) = fmap BoolValue (enumFromThenTo x y z)

instance Bounded (Value BoolType) where
  minBound = BoolValue False
  maxBound = BoolValue True

instance Num (Value IntType) where
  (+) (IntValue x) (IntValue y) = IntValue (x+y)
  (-) (IntValue x) (IntValue y) = IntValue (x-y)
  (*) (IntValue x) (IntValue y) = IntValue (x*y)
  negate (IntValue x) = IntValue (negate x)
  abs (IntValue x) = IntValue (abs x)
  signum (IntValue x) = IntValue (signum x)
  fromInteger = IntValue

instance Enum (Value IntType) where
  succ (IntValue x) = IntValue (succ x)
  pred (IntValue x) = IntValue (pred x)
  toEnum i = IntValue (toEnum i)
  fromEnum (IntValue x) = fromEnum x
  enumFrom (IntValue x) = fmap IntValue (enumFrom x)
  enumFromThen (IntValue x) (IntValue y) = fmap IntValue (enumFromThen x y)
  enumFromTo (IntValue x) (IntValue y) = fmap IntValue (enumFromTo x y)
  enumFromThenTo (IntValue x) (IntValue y) (IntValue z) = fmap IntValue (enumFromThenTo x y z)

instance Real (Value IntType) where
  toRational (IntValue x) = toRational x

instance Integral (Value IntType) where
  quot (IntValue x) (IntValue y) = IntValue $ quot x y
  rem (IntValue x) (IntValue y) = IntValue $ rem x y
  div (IntValue x) (IntValue y) = IntValue $ div x y
  mod (IntValue x) (IntValue y) = IntValue $ mod x y
  quotRem (IntValue x) (IntValue y) = (IntValue q,IntValue r)
    where
      (q,r) = quotRem x y
  divMod (IntValue x) (IntValue y) = (IntValue d,IntValue m)
    where
      (d,m) = divMod x y
  toInteger (IntValue x) = x

instance Num (Value RealType) where
  (+) (RealValue x) (RealValue y) = RealValue (x+y)
  (-) (RealValue x) (RealValue y) = RealValue (x-y)
  (*) (RealValue x) (RealValue y) = RealValue (x*y)
  negate (RealValue x) = RealValue (negate x)
  abs (RealValue x) = RealValue (abs x)
  signum (RealValue x) = RealValue (signum x)
  fromInteger = RealValue . fromInteger

instance Real (Value RealType) where
  toRational (RealValue x) = x

instance Fractional (Value RealType) where
  (/) (RealValue x) (RealValue y) = RealValue (x/y)
  recip (RealValue x) = RealValue (recip x)
  fromRational = RealValue

instance RealFrac (Value RealType) where
  properFraction (RealValue x) = let (p,q) = properFraction x
                                 in (p,RealValue q)
  truncate (RealValue x) = truncate x
  round (RealValue x) = round x
  ceiling (RealValue x) = ceiling x
  floor (RealValue x) = floor x

withBW :: IsNatural bw => (Natural bw -> Value (BitVecType bw)) -> Value (BitVecType bw)
withBW f = f getNatural

bvAdd :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvAdd (BitVecValue x bw) (BitVecValue y _) = BitVecValue ((x+y) `mod` (2^(naturalToInteger bw))) bw

bvSub :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvSub (BitVecValue x bw) (BitVecValue y _) = BitVecValue ((x-y) `mod` (2^(naturalToInteger bw))) bw

bvMul :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvMul (BitVecValue x bw) (BitVecValue y _) = BitVecValue ((x*y) `mod` (2^(naturalToInteger bw))) bw

bvDiv :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvDiv (BitVecValue x bw) (BitVecValue y _) = BitVecValue (x `div` y) bw

bvMod :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvMod (BitVecValue x bw) (BitVecValue y _) = BitVecValue (x `mod` y) bw

bvNegate :: Value (BitVecType bw) -> Value (BitVecType bw)
bvNegate (BitVecValue x bw) = BitVecValue (if x==0
                                           then 0
                                           else 2^(naturalToInteger bw)-x) bw

bvSignum :: Value (BitVecType bw) -> Value (BitVecType bw)
bvSignum (BitVecValue x bw) = BitVecValue (if x==0 then 0 else 1) bw

instance IsNatural bw => Num (Value (BitVecType bw)) where
  (+) = bvAdd
  (-) = bvSub
  (*) = bvMul
  negate = bvNegate
  abs = id
  signum = bvSignum
  fromInteger x = withBW $ \bw -> BitVecValue (x `mod` (2^(naturalToInteger bw))) bw

-- | Get the smallest bitvector value that is bigger than the given one.
--   Also known as the successor.
bvSucc :: Value (BitVecType bw) -> Value (BitVecType bw)
bvSucc (BitVecValue i bw)
  | i < 2^(naturalToInteger bw) - 1 = BitVecValue (i+1) bw
  | otherwise = error "bvSucc: tried to take `succ' of maxBound"

-- | Get the largest bitvector value that is smaller than the given one.
--   Also known as the predecessor.
bvPred :: Value (BitVecType bw) -> Value (BitVecType bw)
bvPred (BitVecValue i bw)
  | i > 0 = BitVecValue (i-1) bw
  | otherwise = error "bvPred: tried to take `pred' of minBound"

instance IsNatural bw => Enum (Value (BitVecType bw)) where
  succ = bvSucc
  pred = bvPred
  toEnum i = withBW $ \bw -> let i' = toInteger i
                             in if i >= 0 && i < 2^(naturalToInteger bw)
                                then BitVecValue i' bw
                                else error "Prelude.toEnum: argument out of range for bitvector value."
  fromEnum (BitVecValue i _) = fromInteger i
  enumFrom (BitVecValue x bw) = [ BitVecValue i bw | i <- [x..2^(naturalToInteger bw)-1] ]
  enumFromThen (BitVecValue x bw) (BitVecValue y _) = [ BitVecValue i bw | i <- [x,y..2^(naturalToInteger bw)-1] ]
  enumFromTo (BitVecValue x bw) (BitVecValue y _) = [ BitVecValue i bw | i <- [x..y] ]
  enumFromThenTo (BitVecValue x bw) (BitVecValue y _) (BitVecValue z _)
    = [ BitVecValue i bw | i <- [x,y..z] ]

instance IsNatural bw => Bounded (Value (BitVecType bw)) where
  minBound = withBW $ \bw -> BitVecValue 0 bw
  maxBound = withBW $ \bw -> BitVecValue (2^(naturalToInteger bw)-1) bw

-- | Get the minimal value for a bitvector.
--   If unsigned, the value is 0, otherwise 2^(bw-1).
bvMinValue :: Bool -- ^ Signed bitvector?
           -> Repr (BitVecType bw)
           -> Value (BitVecType bw)
bvMinValue False (BitVecRepr bw) = BitVecValue 0 bw
bvMinValue True (BitVecRepr bw) = BitVecValue (2^(naturalToInteger bw-1)) bw

-- | Get the maximal value for a bitvector.
--   If unsigned, the value is 2^(bw-1)-1, otherwise 2^bw-1.
bvMaxValue :: Bool -- ^ Signed bitvector?
           -> Repr (BitVecType bw)
           -> Value (BitVecType bw)
bvMaxValue False (BitVecRepr bw) = BitVecValue (2^(naturalToInteger bw)-1) bw
bvMaxValue True (BitVecRepr bw) = BitVecValue (2^(naturalToInteger bw-1)-1) bw

instance IsNatural bw => Bits (Value (BitVecType bw)) where
  (.&.) (BitVecValue x bw) (BitVecValue y _) = BitVecValue (x .&. y) bw
  (.|.) (BitVecValue x bw) (BitVecValue y _) = BitVecValue (x .|. y) bw
  xor (BitVecValue x bw) (BitVecValue y _)
    = BitVecValue ((x .|. max) `xor` (y .|. max)) bw
    where
      max = bit $ fromInteger $ naturalToInteger bw
  complement (BitVecValue x bw) = BitVecValue (2^(naturalToInteger bw)-1-x) bw
  shift (BitVecValue x bw) i = BitVecValue ((x `shift` i) `mod` (2^(naturalToInteger bw))) bw
  rotate (BitVecValue x bw) i = BitVecValue ((x `rotate` i) `mod` (2^(naturalToInteger bw))) bw
  zeroBits = withBW $ \bw -> BitVecValue 0 bw
  bit n = withBW $ \bw -> if toInteger n < naturalToInteger bw && n >= 0
                          then BitVecValue (bit n) bw
                          else BitVecValue 0 bw
  setBit (BitVecValue x bw) i = if toInteger i < naturalToInteger bw && i >= 0
                                then BitVecValue (setBit x i) bw
                                else BitVecValue x bw
  clearBit (BitVecValue x bw) i = if toInteger i < naturalToInteger bw && i >= 0
                                  then BitVecValue (clearBit x i) bw
                                  else BitVecValue x bw
  complementBit (BitVecValue x bw) i = if toInteger i < naturalToInteger bw && i >= 0
                                       then BitVecValue (complementBit x i) bw
                                       else BitVecValue x bw
  testBit (BitVecValue x _) i = testBit x i
#if MIN_VERSION_base(4,7,0)
  bitSizeMaybe (BitVecValue _ bw) = Just (fromInteger $ naturalToInteger bw)
#endif
  bitSize (BitVecValue _ bw) = fromInteger $ naturalToInteger bw
  isSigned _ = False
  shiftL (BitVecValue x bw) i = BitVecValue ((shiftL x i) `mod` 2^(naturalToInteger bw)) bw
  shiftR (BitVecValue x bw) i = BitVecValue ((shiftR x i) `mod` 2^(naturalToInteger bw)) bw
  rotateL (BitVecValue x bw) i = BitVecValue ((rotateL x i) `mod` 2^(naturalToInteger bw)) bw
  rotateR (BitVecValue x bw) i = BitVecValue ((rotateR x i) `mod` 2^(naturalToInteger bw)) bw
  popCount (BitVecValue x _) = popCount x

#if MIN_VERSION_base(4,7,0)
instance IsNatural bw => FiniteBits (Value (BitVecType bw)) where
  finiteBitSize (BitVecValue _ bw) = fromInteger $ naturalToInteger bw
#endif

instance IsNatural bw => Real (Value (BitVecType bw)) where
  toRational (BitVecValue x _) = toRational x

instance IsNatural bw => Integral (Value (BitVecType bw)) where
  quot (BitVecValue x bw) (BitVecValue y _) = BitVecValue (quot x y) bw
  rem (BitVecValue x bw) (BitVecValue y _) = BitVecValue (rem x y) bw
  div (BitVecValue x bw) (BitVecValue y _) = BitVecValue (div x y) bw
  mod (BitVecValue x bw) (BitVecValue y _) = BitVecValue (mod x y) bw
  quotRem (BitVecValue x bw) (BitVecValue y _) = (BitVecValue q bw,BitVecValue r bw)
    where
      (q,r) = quotRem x y
  divMod (BitVecValue x bw) (BitVecValue y _) = (BitVecValue d bw,BitVecValue m bw)
    where
      (d,m) = divMod x y
  toInteger (BitVecValue x _) = x
