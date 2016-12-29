module Language.SMTLib2.Internals.Type where

import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
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
import Data.Bits
import qualified GHC.TypeLits as TL
import Unsafe.Coerce

-- | Describes the kind of all SMT types.
--   It is only used in promoted form, for a concrete representation see 'Repr'.
data Type = BoolType
          | IntType
          | RealType
          | BitVecType TL.Nat
          | ArrayType [Type] Type
          | forall a. DataType a [Type]
          | ParameterType Nat
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

class (Typeable dt,Ord (Datatype dt),GCompare (Constr dt),GCompare (Field dt))
      => IsDatatype (dt :: [Type] -> (Type -> *) -> *) where
  type Parameters dt :: Nat
  type Signature dt :: [[Type]]
  data Datatype dt :: *
  data Constr dt (csig :: [Type])
  data Field dt (tp :: Type)
  -- | Get the data type from a value
  datatypeGet    :: (GetType e,List.Length par ~ Parameters dt)
                 => dt par e -> (Datatype dt,List Repr par)
  -- | How many polymorphic parameters does this datatype have
  parameters     :: Datatype dt -> Natural (Parameters dt)
  -- | The name of the datatype. Must be unique.
  datatypeName   :: Datatype dt -> String
  -- | Get all of the constructors of this datatype
  constructors   :: Datatype dt -> List (Constr dt) (Signature dt)
  -- | Get the name of a constructor
  constrName     :: Constr dt csig -> String
  -- | Test if a value is constructed using a specific constructor
  test           :: dt par e -> Constr dt csig -> Bool
  -- | Get all the fields of a constructor
  fields         :: Constr dt csig -> List (Field dt) csig
  -- | Construct a value using a constructor
  construct      :: (List.Length par ~ Parameters dt)
                 => List Repr par
                 -> Constr dt csig
                 -> List e (Instantiated csig par)
                 -> dt par e
  -- | Deconstruct a value into a constructor and a list of arguments
  deconstruct    :: GetType e => dt par e -> ConApp dt par e
  -- | Get the name of a field
  fieldName      :: Field dt tp -> String
  -- | Get the type of a field
  fieldType      :: Field dt tp -> Repr tp
  -- | Extract a field value from a value
  fieldGet       :: dt par e -> Field dt tp -> e (CType tp par)

type family CType (tp :: Type) (par :: [Type]) :: Type where
  CType 'BoolType par = 'BoolType
  CType 'IntType par = 'IntType
  CType 'RealType par = 'RealType
  CType ('BitVecType w) par = 'BitVecType w
  CType ('ArrayType idx el) par = 'ArrayType (Instantiated idx par) (CType el par)
  CType ('DataType dt arg) par = 'DataType dt (Instantiated arg par)
  CType ('ParameterType n) par = List.Index par n

type family Instantiated (sig :: [Type]) (par :: [Type]) :: [Type] where
  Instantiated '[] par = '[]
  Instantiated (tp ': tps) par = (CType tp par) ': Instantiated tps par

data ConApp dt par e
  = forall csig.
    (List.Length par ~ Parameters dt) =>
    ConApp { parameters' :: List Repr par
           , constructor :: Constr dt csig
           , arguments   :: List e (Instantiated csig par) }

--data FieldType tp where
--  FieldType :: Repr tp -> FieldType ('Left tp)
--  ParType :: Natural n -> FieldType ('Right n)

data AnyDatatype = forall dt. IsDatatype dt => AnyDatatype (Datatype dt)
data AnyConstr = forall dt csig. IsDatatype dt => AnyConstr (Datatype dt) (Constr dt csig)
data AnyField = forall dt csig tp. IsDatatype dt => AnyField (Datatype dt) (Field dt tp)

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
    
    dependencies' :: IsDatatype dt => Set String -> Datatype dt
                   -> (Set String,[(AnyDatatype,String,[String])])
    dependencies' known dt
      | Set.member (datatypeName dt) known = (known,[])
      | otherwise = let name = datatypeName dt
                        known1 = Set.insert name known
                        deps = dependenciesCons (constructors dt)
                        (known2,edges) = foldl (\(cknown,cedges) (AnyDatatype dt)
                                                -> dependencies' cknown dt
                                               ) (known1,[])
                                         deps
                    in (known2,(AnyDatatype dt,name,[ datatypeName dt | AnyDatatype dt <- deps ]):edges)

    dependenciesCons :: IsDatatype dt => List (Constr dt) tps
                     -> [AnyDatatype]
    dependenciesCons Nil = []
    dependenciesCons (con ::: cons)
      = let dep1 = dependenciesFields (fields con)
            dep2 = dependenciesCons cons
        in dep1++dep2

    dependenciesFields :: IsDatatype dt => List (Field dt) tps
                       -> [AnyDatatype]
    dependenciesFields Nil = []
    dependenciesFields (f ::: fs)
      = let dep1 = dependenciesTp (fieldType f)
            dep2 = dependenciesFields fs
        in dep1++dep2

    dependenciesTp :: Repr tp
                   -> [AnyDatatype]
    dependenciesTp (ArrayRepr idx el)
      = let dep1 = dependenciesTps idx
            dep2 = dependenciesTp el
        in dep1++dep2
    dependenciesTp (DataRepr dt par)
      = let dep1 = [AnyDatatype dt]
            dep2 = dependenciesTps par
        in dep1++dep2
    dependenciesTp _ = []

    dependenciesTps :: List Repr tps
                    -> [AnyDatatype]
    dependenciesTps Nil = []
    dependenciesTps (tp ::: tps)
      = let dep1 = dependenciesTp tp
            dep2 = dependenciesTps tps
        in dep1++dep2

signature :: IsDatatype dt => Datatype dt -> List (List Repr) (Signature dt)
signature dt
  = runIdentity $ List.mapM (\con -> List.mapM (\f -> return (fieldType f)
                                               ) (fields con)
                            ) (constructors dt)

constrSig :: IsDatatype dt => Constr dt sig -> List Repr sig
constrSig constr
  = runIdentity $ List.mapM (\f -> return (fieldType f)) (fields constr)

instantiate :: List Repr sig
            -> List Repr par
            -> (List Repr (Instantiated sig par),
                List.Length sig :~: List.Length (Instantiated sig par))
instantiate Nil _ = (Nil,Refl)
instantiate (tp ::: tps) par = case instantiate tps par of
  (ntps,Refl) -> (ctype tp par ::: ntps,Refl)

ctype :: Repr tp
      -> List Repr par
      -> Repr (CType tp par)
ctype BoolRepr _ = BoolRepr
ctype IntRepr _ = IntRepr
ctype RealRepr _ = RealRepr
ctype (BitVecRepr w) _ = BitVecRepr w
ctype (ArrayRepr idx el) par = case instantiate idx par of
  (nidx,Refl) -> ArrayRepr nidx (ctype el par)
ctype (DataRepr dt args) par = case instantiate args par of
  (nargs,Refl) -> DataRepr dt nargs
ctype (ParameterRepr p) par = List.index par p

determines :: IsDatatype dt
           => Datatype dt
           -> Constr dt sig
           -> Bool
determines dt con = allDetermined (fromInteger $ naturalToInteger $
                                   parameters dt) $
                    determines' (fields con) Set.empty
  where
    determines' :: IsDatatype dt => List (Field dt) tps
                -> Set Integer -> Set Integer
    determines' Nil mp = mp
    determines' (f ::: fs) mp = determines' fs (containedParameter (fieldType f) mp)

    allDetermined sz mp = Set.size mp == sz

containedParameter :: Repr tp -> Set Integer -> Set Integer
containedParameter (ArrayRepr idx el) det
  = runIdentity $ List.foldM (\det tp -> return $ containedParameter tp det
                             ) (containedParameter el det) idx
containedParameter (DataRepr i args) det
  = runIdentity $ List.foldM (\det tp -> return $ containedParameter tp det
                             ) det args
containedParameter (ParameterRepr p) det
  = Set.insert (naturalToInteger p) det
containedParameter _ det = det

typeInference :: Repr atp -- ^ The type containing parameters
              -> Repr ctp -- ^ The concrete type without parameters
              -> (forall n ntp. Natural n -> Repr ntp -> a -> Maybe a) -- ^ Action to execute when a parameter is assigned
              -> a
              -> Maybe a
typeInference BoolRepr BoolRepr _ x = Just x
typeInference IntRepr IntRepr _ x = Just x
typeInference RealRepr RealRepr _ x = Just x
typeInference (BitVecRepr w1) (BitVecRepr w2) _ x = do
  Refl <- geq w1 w2
  return x
typeInference (ParameterRepr n) tp f x = f n tp x
typeInference (ArrayRepr idx el) (ArrayRepr idx' el') f x = do
  x1 <- typeInferences idx idx' f x
  typeInference el el' f x1
typeInference (DataRepr (_::Datatype dt) par) (DataRepr (_::Datatype dt') par') f x = do
  Refl <- eqT :: Maybe (dt :~: dt')
  typeInferences par par' f x
typeInference _ _ _ _ = Nothing

typeInferences :: List Repr atps
               -> List Repr ctps
               -> (forall n ntp. Natural n -> Repr ntp -> a -> Maybe a)
               -> a
               -> Maybe a
typeInferences Nil Nil _ x = Just x
typeInferences (atp ::: atps) (ctp ::: ctps) f x = do
  x1 <- typeInference atp ctp f x
  typeInferences atps ctps f x1
typeInferences _ _ _ _ = Nothing

partialInstantiation :: Repr tp
                     -> (forall n a. Natural n ->
                         (forall ntp. Repr ntp -> a) -> Maybe a)
                     -> (forall rtp. Repr rtp -> a)
                     -> a
partialInstantiation BoolRepr _ res = res BoolRepr
partialInstantiation IntRepr _ res = res IntRepr
partialInstantiation RealRepr _ res = res RealRepr
partialInstantiation (BitVecRepr w) _ res = res (BitVecRepr w)
partialInstantiation (ArrayRepr idx el) f res
  = partialInstantiations idx f $
    \nidx -> partialInstantiation el f $
             \nel -> res $ ArrayRepr nidx nel
partialInstantiation (DataRepr dt par) f res
  = partialInstantiations par f $
    \npar -> res $ DataRepr dt npar
partialInstantiation (ParameterRepr n) f res
  = case f n res of
  Just r -> r
  Nothing -> res (ParameterRepr n)

partialInstantiations :: List Repr tp
                      -> (forall n a. Natural n ->
                          (forall ntp. Repr ntp -> a) -> Maybe a)
                      -> (forall rtp. List.Length tp ~ List.Length rtp
                          => List Repr rtp -> a)
                      -> a
partialInstantiations Nil _ res = res Nil
partialInstantiations (tp ::: tps) f res
  = partialInstantiation tp f $
    \ntp -> partialInstantiations tps f $
            \ntps -> res (ntp ::: ntps)


registerType :: (Monad m,IsDatatype tp,Ord dt,Ord con,Ord field) => dt
             -> (forall sig. Constr tp sig -> m con)
             -> (forall sig tp'. Field tp tp' -> m field)
             -> Datatype tp -> TypeRegistry dt con field
             -> m (TypeRegistry dt con field)
registerType i f g dt reg
  = List.foldM
    (\reg con -> do
        c <- f con
        let reg' = reg { allConstructors = Map.insert c (AnyConstr dt con) (allConstructors reg) }
        List.foldM (\reg field -> do
                       fi <- g field
                       return $ reg { allFields = Map.insert fi (AnyField dt field) (allFields reg) }
                   ) reg' (fields con)
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
  (==) (AnyConstr _ c1) (AnyConstr _ c2) = constrName c1 == constrName c2

instance Eq AnyField where
  (==) (AnyField _ f1) (AnyField _ f2) = fieldName f1 == fieldName f2

instance Ord AnyDatatype where
  compare (AnyDatatype x) (AnyDatatype y) = compare (datatypeName x) (datatypeName y)

instance Ord AnyConstr where
  compare (AnyConstr _ c1) (AnyConstr _ c2) = compare (constrName c1) (constrName c2)

instance Ord AnyField where
  compare (AnyField _ f1) (AnyField _ f2) = compare (fieldName f1) (fieldName f2)

data DynamicDatatype (par :: Nat) (sig :: [[Type]])
  = DynDatatype { dynDatatypeParameters :: Natural par
                , dynDatatypeSig :: List (DynamicConstructor sig) sig
                , dynDatatypeName :: String }
  deriving (Eq,Ord)

data DynamicConstructor
     (sig :: [[Type]])
     (csig :: [Type]) where
  DynConstructor :: Natural idx -> String
                 -> List (DynamicField sig) (List.Index sig idx)
                 -> DynamicConstructor sig (List.Index sig idx)

data DynamicField
     (sig :: [[Type]])
     (tp :: Type) where
  DynField :: Natural idx -> Natural fidx -> String
           -> Repr (List.Index (List.Index sig idx) fidx)
           -> DynamicField sig (List.Index (List.Index sig idx) fidx)

data DynamicValue
     (plen :: Nat)
     (sig :: [[Type]])
     (par :: [Type]) e where
  DynValue :: DynamicDatatype (List.Length par) sig
           -> List Repr par
           -> DynamicConstructor sig csig
           -> List e (Instantiated csig par)
           -> DynamicValue (List.Length par) sig par e

instance (Typeable l,Typeable sig) => IsDatatype (DynamicValue l sig) where
  type Parameters (DynamicValue l sig) = l
  type Signature (DynamicValue l sig) = sig
  newtype Datatype (DynamicValue l sig)
    = DynDatatypeInfo { dynDatatypeInfo :: DynamicDatatype l sig }
    deriving (Eq,Ord)
  data Constr (DynamicValue l sig) csig
    = DynConstr (DynamicDatatype l sig) (DynamicConstructor sig csig)
  newtype Field (DynamicValue l sig) tp
    = DynField' (DynamicField sig tp)
  parameters = dynDatatypeParameters . dynDatatypeInfo
  datatypeGet (DynValue dt par _ _) = (DynDatatypeInfo dt,par)
  datatypeName = dynDatatypeName . dynDatatypeInfo
  constructors (DynDatatypeInfo dt) = runIdentity $ List.mapM
    (\con -> return (DynConstr dt con))
    (dynDatatypeSig dt)
  constrName (DynConstr _ (DynConstructor _ n _)) = n
  test (DynValue _ _ (DynConstructor n _ _) _)
    (DynConstr _ (DynConstructor m _ _))
    = case geq n m of
        Just Refl -> True
        Nothing -> False
  fields (DynConstr _ (DynConstructor _ _ fs)) = runIdentity $ List.mapM
    (\f -> return (DynField' f)) fs
  construct par (DynConstr dt con) args
    = DynValue dt par con args
  deconstruct (DynValue dt par con args) = ConApp par (DynConstr dt con) args
  fieldName (DynField' (DynField _ _ n _)) = n
  fieldType (DynField' (DynField _ _ _ tp)) = tp
  fieldGet (DynValue dt par con@(DynConstructor cidx _ fs) args)
    (DynField' (DynField cidx' fidx _ _))
    = case geq cidx cidx' of
    Just Refl -> index par fs args fidx
    where
      index :: List Repr par
            -> List (DynamicField sig) csig
            -> List e (Instantiated csig par)
            -> Natural n
            -> e (CType (List.Index csig n) par)
      index _ (_ ::: _) (tp ::: _) Zero = tp
      index par (_ ::: sig) (_ ::: tps) (Succ n) = index par sig tps n

instance Show (Datatype (DynamicValue l sig)) where
  showsPrec p (DynDatatypeInfo dt) = showString (dynDatatypeName dt)

instance GEq (DynamicConstructor sig) where
  geq (DynConstructor i1 _ _) (DynConstructor i2 _ _) = do
    Refl <- geq i1 i2
    return Refl

instance GCompare (DynamicConstructor sig) where
  gcompare (DynConstructor i1 _ _) (DynConstructor i2 _ _)
    = case gcompare i1 i2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance GEq (Constr (DynamicValue l sig)) where
  geq (DynConstr _ (DynConstructor n _ _)) (DynConstr _ (DynConstructor m _ _)) = do
    Refl <- geq n m
    return Refl

instance GCompare (Constr (DynamicValue l sig)) where
  gcompare (DynConstr _ (DynConstructor n _ _))
    (DynConstr _ (DynConstructor m _ _)) = case gcompare n m of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance GEq (Field (DynamicValue l sig)) where
  geq (DynField' (DynField cidx1 fidx1 _ _))
    (DynField' (DynField cidx2 fidx2 _ _)) = do
    Refl <- geq cidx1 cidx2
    Refl <- geq fidx1 fidx2
    return Refl

instance GCompare (Field (DynamicValue l sig)) where
  gcompare (DynField' (DynField cidx1 fidx1 _ _))
    (DynField' (DynField cidx2 fidx2 _ _))
    = case gcompare cidx1 cidx2 of
    GEQ -> case gcompare fidx1 fidx2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

newtype BitWidth (bw :: TL.Nat) = BitWidth { bwSize :: Integer }

getBw :: Integer -> (forall bw. TL.KnownNat bw => BitWidth bw -> a) -> a
getBw w f = case TL.someNatVal w of
  Just (TL.SomeNat (_::Proxy bw))
    -> f (BitWidth w::BitWidth bw)

-- | Values that can be used as constants in expressions.
data Value (a :: Type) where
  BoolValue :: Bool -> Value BoolType
  IntValue :: Integer -> Value IntType
  RealValue :: Rational -> Value RealType
  BitVecValue :: Integer
              -> BitWidth bw
              -> Value (BitVecType bw)
  DataValue :: (IsDatatype dt,List.Length par ~ Parameters dt)
            => dt par Value -> Value (DataType dt par)

#if __GLASGOW_HASKELL__ >= 800
pattern ConstrValue :: ()
                    => (List.Length par ~ Parameters dt,a ~ DataType dt par,IsDatatype dt)
#else
pattern ConstrValue :: (List.Length par ~ Parameters dt,a ~ DataType dt par,IsDatatype dt)
                    => ()
#endif
                    => List Repr par
                    -> Constr dt csig
                    -> List Value (Instantiated csig par)
                    -> Value a
pattern ConstrValue par con args <- DataValue (deconstruct -> ConApp par con args) where
  ConstrValue par con args = DataValue (construct par con args)

data AnyValue = forall (t :: Type). AnyValue (Value t)

-- | A concrete representation of an SMT type.
--   For aesthetic reasons, it's recommended to use the functions 'bool', 'int', 'real', 'bitvec' or 'array'.
data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: BitWidth bw -> Repr (BitVecType bw)
  ArrayRepr :: List Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: (IsDatatype dt,List.Length par ~ Parameters dt) => Datatype dt -> List Repr par -> Repr (DataType dt par)
  ParameterRepr :: Natural p -> Repr (ParameterType p)

data NumRepr (t :: Type) where
  NumInt :: NumRepr IntType
  NumReal :: NumRepr RealType

data FunRepr (sig :: ([Type],Type)) where
  FunRepr :: List Repr arg -> Repr tp -> FunRepr '(arg,tp)

class GetType v where
  getType :: v tp -> Repr tp

class GetFunType fun where
  getFunType :: fun '(arg,res) -> (List Repr arg,Repr res)

bw :: TL.KnownNat bw => Proxy bw -> BitWidth bw
bw = BitWidth . TL.natVal

instance Eq (BitWidth bw) where
  (==) (BitWidth _) (BitWidth _) = True

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

-- | A typed representation of the SMT BitVec type.
--   Holds bitvectors (a vector of booleans) of a certain bitwidth.
--   Constants can be created using 'Language.SMTLib2.cbv'.
bitvec :: BitWidth bw -- ^ The width of the bitvector
       -> Repr (BitVecType bw)
bitvec = BitVecRepr

-- | A representation of the SMT Array type.
--   Has a list of index types and an element type.
--   Stores one value of the element type for each combination of the index types.
--   Constants can be created using 'Language.SMTLib2.constArray'.
array :: List Repr idx -> Repr el -> Repr (ArrayType idx el)
array = ArrayRepr

-- | A representation of a user-defined datatype without parameters.
dt :: (IsDatatype dt,Parameters dt ~ 'Z) => Datatype dt -> Repr (DataType dt '[])
dt dt = DataRepr dt List.Nil

-- | A representation of a user-defined datatype with parameters.
dt' :: (IsDatatype dt,List.Length par ~ Parameters dt) => Datatype dt -> List Repr par -> Repr (DataType dt par)
dt' = DataRepr

instance GEq BitWidth where
  geq (BitWidth bw1) (BitWidth bw2)
    | bw1==bw2 = Just $ unsafeCoerce Refl
    | otherwise = Nothing

instance GCompare BitWidth where
  gcompare (BitWidth bw1) (BitWidth bw2)
    = case compare bw1 bw2 of
    EQ -> unsafeCoerce GEQ
    LT -> GLT
    GT -> GGT

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
  geq (DataValue (v1::dt1 par1 Value)) (DataValue (v2::dt2 par2 Value)) = do
    Refl <- eqT :: Maybe (dt1 :~: dt2)
    case deconstruct v1 of
      ConApp p1 c1 arg1 -> case deconstruct v2 of
        ConApp p2 c2 arg2 -> do
          Refl <- geq p1 p2
          Refl <- geq c1 c2
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
  gcompare (DataValue (v1::dt1 par1 Value)) (DataValue (v2::dt2 par2 Value))
    = case eqT :: Maybe (dt1 :~: dt2) of
    Just Refl -> case deconstruct v1 of
      ConApp p1 c1 arg1 -> case deconstruct v2 of
        ConApp p2 c2 arg2 -> case gcompare p1 p2 of
          GEQ -> case gcompare c1 c2 of
            GEQ -> case gcompare arg1 arg2 of
              GEQ -> GEQ
              GLT -> GLT
              GGT -> GGT
            GLT -> GLT
            GGT -> GGT
          GLT -> GLT
          GGT -> GGT
    Nothing -> case compare (typeRep (Proxy::Proxy dt1))
                            (typeRep (Proxy::Proxy dt2)) of
      LT -> GLT
      GT -> GGT

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
  geq (DataRepr (_::Datatype dt1) p1) (DataRepr (_::Datatype dt2) p2) = do
    Refl <- eqT :: Maybe (Datatype dt1 :~: Datatype dt2)
    Refl <- geq p1 p2
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
  gcompare (DataRepr (dt1 :: Datatype dt1) p1 ) (DataRepr (dt2 :: Datatype dt2) p2)
    = case eqT of
    Just (Refl :: Datatype dt1 :~: Datatype dt2) -> case gcompare p1 p2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
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
    = showBitVec p v (bwSize n)
  showsPrec p (DataValue val) = case deconstruct val of
    ConApp par con args -> showParen (p>10) $
                           showString "ConstrValue " .
                           showString (constrName con).
                           showChar ' ' .
                           showsPrec 11 args

showBitVec :: Int -> Integer -> Integer -> ShowS
showBitVec p v bw
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
    rv = v `mod` 2^bw

instance GShow Value where
  gshowsPrec = showsPrec

instance Show (Repr t) where
  showsPrec _ BoolRepr = showString "bool"
  showsPrec _ IntRepr = showString "int"
  showsPrec _ RealRepr = showString "real"
  showsPrec p (BitVecRepr n) = showParen (p>10) $
    showString "bitvec " .
    showsPrec 11 (bwSize n)
  showsPrec p (ArrayRepr idx el) = showParen (p>10) $
    showString "array " .
    showsPrec 11 idx . showChar ' ' .
    showsPrec 11 el
  showsPrec p (DataRepr dt par) = showParen (p>10) $
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
valueType (DataValue v) = let (dt,par) = datatypeGet v
                          in DataRepr dt par

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
typeSize :: Maybe (List Repr par) -> Repr tp -> Maybe Integer
typeSize _ BoolRepr = Just 2
typeSize _ IntRepr = Nothing
typeSize _ RealRepr = Nothing
typeSize _ (BitVecRepr bw) = Just $ 2^(bwSize bw)
typeSize par (ArrayRepr idx el) = do
  idxSz <- List.toList (typeSize par) idx
  elSz <- typeSize par el
  return $ product (elSz:idxSz)
typeSize _ (DataRepr dt par) = do
  conSz <- List.toList (constrSize dt par) (constructors dt)
  return $ sum conSz
  where
    constrSize :: IsDatatype dt => Datatype dt -> List Repr par
               -> Constr dt sig -> Maybe Integer
    constrSize dt par con = do
      fieldSz <- List.toList (fieldSize dt par) (fields con)
      return $ product fieldSz
    fieldSize :: IsDatatype dt => Datatype dt -> List Repr par
              -> Field dt tp -> Maybe Integer
    fieldSize dt par field = typeSize (Just par) (fieldType field)
typeSize (Just par) (ParameterRepr p) = typeSize Nothing (List.index par p)

typeFiniteDomain :: Repr tp -> Maybe [Value tp]
typeFiniteDomain BoolRepr = Just [BoolValue False,BoolValue True]
typeFiniteDomain (BitVecRepr bw) = Just [ BitVecValue n bw
                                        | n <- [0..2^(bwSize bw)-1] ]
typeFiniteDomain _ = Nothing

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

withBW :: TL.KnownNat bw => (Proxy bw -> res (BitVecType bw))
       -> res (BitVecType bw)
withBW f = f Proxy

bvAdd :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvAdd (BitVecValue x bw1) (BitVecValue y bw2)
  | bw1 /= bw2 = error "bvAdd: Bitvector size mismatch"
  | otherwise = BitVecValue ((x+y) `mod` (2^(bwSize bw1))) bw1

bvSub :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvSub (BitVecValue x bw1) (BitVecValue y bw2)
  | bw1 /= bw2 = error "bvSub: Bitvector size mismatch"
  | otherwise = BitVecValue ((x-y) `mod` (2^(bwSize bw1))) bw1

bvMul :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvMul (BitVecValue x bw1) (BitVecValue y bw2)
  | bw1 /= bw2 = error "bvMul: Bitvector size mismatch"
  | otherwise =  BitVecValue ((x*y) `mod` (2^(bwSize bw1))) bw1

bvDiv :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvDiv (BitVecValue x bw1) (BitVecValue y bw2)
  | bw1 /= bw2 = error "bvDiv: Bitvector size mismatch"
  | otherwise = BitVecValue (x `div` y) bw1

bvMod :: Value (BitVecType bw) -> Value (BitVecType bw) -> Value (BitVecType bw)
bvMod (BitVecValue x bw1) (BitVecValue y bw2)
  | bw1 /= bw2 = error "bvMod: Bitvector size mismatch"
  | otherwise = BitVecValue (x `mod` y) bw1

bvNegate :: Value (BitVecType bw) -> Value (BitVecType bw)
bvNegate (BitVecValue x bw) = BitVecValue (if x==0
                                           then 0
                                           else 2^(bwSize bw)-x) bw

bvSignum :: Value (BitVecType bw) -> Value (BitVecType bw)
bvSignum (BitVecValue x bw) = BitVecValue (if x==0 then 0 else 1) bw

instance TL.KnownNat bw => Num (Value (BitVecType bw)) where
  (+) = bvAdd
  (-) = bvSub
  (*) = bvMul
  negate = bvNegate
  abs = id
  signum = bvSignum
  fromInteger x = withBW $ \pr -> let bw = TL.natVal pr
                                  in BitVecValue (x `mod` (2^bw)) (BitWidth bw)

-- | Get the smallest bitvector value that is bigger than the given one.
--   Also known as the successor.
bvSucc :: Value (BitVecType bw) -> Value (BitVecType bw)
bvSucc (BitVecValue i bw)
  | i < 2^(bwSize bw) - 1 = BitVecValue (i+1) bw
  | otherwise = error "bvSucc: tried to take `succ' of maxBound"

-- | Get the largest bitvector value that is smaller than the given one.
--   Also known as the predecessor.
bvPred :: Value (BitVecType bw) -> Value (BitVecType bw)
bvPred (BitVecValue i bw)
  | i > 0 = BitVecValue (i-1) bw
  | otherwise = error "bvPred: tried to take `pred' of minBound"

instance TL.KnownNat bw => Enum (Value (BitVecType bw)) where
  succ = bvSucc
  pred = bvPred
  toEnum i = withBW $ \bw -> let i' = toInteger i
                                 bw' = TL.natVal bw
                             in if i >= 0 && i < 2^bw'
                                then BitVecValue i' (BitWidth bw')
                                else error "Prelude.toEnum: argument out of range for bitvector value."
  fromEnum (BitVecValue i _) = fromInteger i
  enumFrom (BitVecValue x bw) = [ BitVecValue i bw | i <- [x..2^(bwSize bw)-1] ]
  enumFromThen (BitVecValue x bw) (BitVecValue y _) = [ BitVecValue i bw | i <- [x,y..2^(bwSize bw)-1] ]
  enumFromTo (BitVecValue x bw) (BitVecValue y _) = [ BitVecValue i bw | i <- [x..y] ]
  enumFromThenTo (BitVecValue x bw) (BitVecValue y _) (BitVecValue z _)
    = [ BitVecValue i bw | i <- [x,y..z] ]

instance TL.KnownNat bw => Bounded (Value (BitVecType bw)) where
  minBound = withBW $ \w -> BitVecValue 0 (bw w)
  maxBound = withBW $ \bw -> let bw' = TL.natVal bw
                             in BitVecValue (2^bw'-1) (BitWidth bw')

-- | Get the minimal value for a bitvector.
--   If unsigned, the value is 0, otherwise 2^(bw-1).
bvMinValue :: Bool -- ^ Signed bitvector?
           -> Repr (BitVecType bw)
           -> Value (BitVecType bw)
bvMinValue False (BitVecRepr bw) = BitVecValue 0 bw
bvMinValue True (BitVecRepr bw) = BitVecValue (2^(bwSize bw-1)) bw

-- | Get the maximal value for a bitvector.
--   If unsigned, the value is 2^(bw-1)-1, otherwise 2^bw-1.
bvMaxValue :: Bool -- ^ Signed bitvector?
           -> Repr (BitVecType bw)
           -> Value (BitVecType bw)
bvMaxValue False (BitVecRepr bw) = BitVecValue (2^(bwSize bw)-1) bw
bvMaxValue True (BitVecRepr bw) = BitVecValue (2^(bwSize bw-1)-1) bw

instance TL.KnownNat bw => Bits (Value (BitVecType bw)) where
  (.&.) (BitVecValue x bw) (BitVecValue y _) = BitVecValue (x .&. y) bw
  (.|.) (BitVecValue x bw) (BitVecValue y _) = BitVecValue (x .|. y) bw
  xor (BitVecValue x bw) (BitVecValue y _)
    = BitVecValue ((x .|. max) `xor` (y .|. max)) bw
    where
      max = bit $ fromInteger $ bwSize bw
  complement (BitVecValue x bw) = BitVecValue (2^(bwSize bw)-1-x) bw
  shift (BitVecValue x bw) i = BitVecValue ((x `shift` i) `mod` (2^(bwSize bw))) bw
  rotate (BitVecValue x bw) i = BitVecValue ((x `rotate` i) `mod` (2^(bwSize bw))) bw
  zeroBits = withBW $ \w -> BitVecValue 0 (bw w)
  bit n = withBW $ \bw -> let bw' = TL.natVal bw
                          in if toInteger n < bw' && n >= 0
                             then BitVecValue (bit n) (BitWidth bw')
                             else BitVecValue 0 (BitWidth bw')
  setBit (BitVecValue x bw) i = if toInteger i < bwSize bw && i >= 0
                                then BitVecValue (setBit x i) bw
                                else BitVecValue x bw
  clearBit (BitVecValue x bw) i = if toInteger i < bwSize bw && i >= 0
                                  then BitVecValue (clearBit x i) bw
                                  else BitVecValue x bw
  complementBit (BitVecValue x bw) i = if toInteger i < bwSize bw && i >= 0
                                       then BitVecValue (complementBit x i) bw
                                       else BitVecValue x bw
  testBit (BitVecValue x _) i = testBit x i
#if MIN_VERSION_base(4,7,0)
  bitSizeMaybe (BitVecValue _ bw) = Just (fromInteger $ bwSize bw)
#endif
  bitSize (BitVecValue _ bw) = fromInteger $ bwSize bw
  isSigned _ = False
  shiftL (BitVecValue x bw) i = BitVecValue ((shiftL x i) `mod` 2^(bwSize bw)) bw
  shiftR (BitVecValue x bw) i = BitVecValue ((shiftR x i) `mod` 2^(bwSize bw)) bw
  rotateL (BitVecValue x bw) i = BitVecValue ((rotateL x i) `mod` 2^(bwSize bw)) bw
  rotateR (BitVecValue x bw) i = BitVecValue ((rotateR x i) `mod` 2^(bwSize bw)) bw
  popCount (BitVecValue x _) = popCount x

#if MIN_VERSION_base(4,7,0)
instance TL.KnownNat bw => FiniteBits (Value (BitVecType bw)) where
  finiteBitSize (BitVecValue _ bw) = fromInteger $ bwSize bw
#endif

instance TL.KnownNat bw => Real (Value (BitVecType bw)) where
  toRational (BitVecValue x _) = toRational x

instance TL.KnownNat bw => Integral (Value (BitVecType bw)) where
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

instance GetType NumRepr where
  getType NumInt = IntRepr
  getType NumReal = RealRepr

instance Show (BitWidth bw) where
  showsPrec p bw = showsPrec p (bwSize bw)

bwAdd :: BitWidth bw1 -> BitWidth bw2 -> BitWidth (bw1 TL.+ bw2)
bwAdd (BitWidth w1) (BitWidth w2) = BitWidth (w1+w2)

datatypeEq :: (IsDatatype dt1,IsDatatype dt2)
           => Datatype dt1 -> Datatype dt2 -> Maybe (dt1 :~: dt2)
datatypeEq (d1 :: Datatype dt1) (d2 :: Datatype dt2) = do
  Refl <- eqT :: Maybe (dt1 :~: dt2)
  if d1==d2
    then return Refl
    else Nothing

datatypeCompare :: (IsDatatype dt1,IsDatatype dt2)
                => Datatype dt1 -> Datatype dt2
                -> GOrdering dt1 dt2
datatypeCompare (d1 :: Datatype dt1) (d2 :: Datatype dt2)
  = case eqT of
  Just (Refl :: dt1 :~: dt2) -> case compare d1 d2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  Nothing -> case compare
                  (typeRep (Proxy::Proxy dt1))
                  (typeRep (Proxy::Proxy dt2)) of
    LT -> GLT
    GT -> GGT
