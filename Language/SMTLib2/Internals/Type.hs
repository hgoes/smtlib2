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

class (Typeable dt,GCompare (Constr dt),GCompare (Field dt))
      => IsDatatype (dt :: (Type -> *) -> *) where
  type Signature dt :: [[Type]]
  data Constr dt (sig :: [Type])
  data Field dt (tp :: Type)
  -- | The name of the datatype. Must be unique.
  datatypeName :: Proxy dt -> String
  constructors :: List (Constr dt) (Signature dt)
  constrName   :: Constr dt sig -> String
  constrTest   :: dt e -> Constr dt sig -> Bool
  constrFields :: Constr dt sig -> List (Field dt) sig
  constrApply  :: ConApp dt e -> dt e
  constrGet    :: dt e -> ConApp dt e
  fieldName    :: Field dt tp -> String
  fieldType    :: Field dt tp -> Repr tp
  fieldGet     :: dt e -> Field dt tp -> e tp

data ConApp dt e = forall sig. ConApp { constructor :: Constr dt sig
                                      , arguments   :: List e sig }

data AnyDatatype = forall dt. IsDatatype dt => AnyDatatype (Proxy dt)
data AnyConstr = forall dt sig. IsDatatype dt => AnyConstr (Constr dt sig)
data AnyField = forall dt tp. IsDatatype dt => AnyField (Field dt tp)

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
             -> Proxy dt
             -> (Set String,[[AnyDatatype]])
dependencies known p = (known',dts)
  where
    dts = fmap (\scc -> fmap (\(dt,_,_) -> dt) $ flattenSCC scc) sccs
    sccs = stronglyConnCompR edges
    (known',edges) = dependencies' known p
    
    dependencies' :: IsDatatype dt => Set String -> Proxy dt -> (Set String,[(AnyDatatype,String,[String])])
    dependencies' known (dt::Proxy dt)
      | Set.member (datatypeName dt) known = (known,[])
      | otherwise = let name = datatypeName dt
                        known1 = Set.insert name known
                        deps = concat $ runIdentity $ List.toList
                               (\con -> return $ catMaybes $ runIdentity $ List.toList
                                        (\field -> case fieldType field of
                                                     DataRepr dep -> return $ Just (AnyDatatype dep)
                                                     _ -> return $ Nothing
                                        ) (constrFields con)
                               ) (constructors::List (Constr dt) (Signature dt))
                        (known2,edges) = foldl (\(known,lst) (AnyDatatype dt)
                                                -> let (nknown,edges) = dependencies' known dt
                                                   in (nknown,edges++lst)
                                               ) (known1,[]) deps
                    in (known2,(AnyDatatype dt,name,[ datatypeName dt | AnyDatatype dt <- deps ]):edges)

signature :: IsDatatype dt => Proxy dt -> List (List Repr) (Signature dt)
signature (Proxy::Proxy dt)
  = runIdentity $ List.mapM (\con -> List.mapM (\f -> return (fieldType f)
                                               ) (constrFields con)
                            ) (constructors :: List (Constr dt) (Signature dt))

constrSig :: IsDatatype dt => Constr dt sig -> List Repr sig
constrSig constr = runIdentity $ List.mapM (\f -> return (fieldType f)) (constrFields constr)

constrEq :: (IsDatatype dt1,IsDatatype dt2) => Constr dt1 sig1 -> Constr dt2 sig2
         -> Maybe (Constr dt1 sig1 :~: Constr dt2 sig2)
constrEq (c1 :: Constr dt1 sig1) (c2 :: Constr dt2 sig2) = do
  Refl <- eqT :: Maybe (dt1 :~: dt2)
  Refl <- geq c1 c2
  return Refl
  
constrCompare :: (IsDatatype dt1,IsDatatype dt2) => Constr dt1 sig1 -> Constr dt2 sig2
              -> GOrdering (Constr dt1 sig1) (Constr dt2 sig2)
constrCompare (c1 :: Constr dt1 sig1) (c2 :: Constr dt2 sig2)
  = case eqT :: Maybe (dt1 :~: dt2) of
  Just Refl -> case gcompare c1 c2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  Nothing -> case compare (typeOf (Proxy::Proxy dt1)) (typeOf (Proxy::Proxy dt2)) of
    LT -> GLT
    GT -> GGT

fieldEq :: (IsDatatype dt1,IsDatatype dt2) => Field dt1 tp1 -> Field dt2 tp2
        -> Maybe (Field dt1 tp1 :~: Field dt2 tp2)
fieldEq (f1 :: Field dt1 tp1) (f2 :: Field dt2 tp2) = do
  Refl <- eqT :: Maybe (dt1 :~: dt2)
  Refl <- geq f1 f2
  return Refl

fieldCompare :: (IsDatatype dt1,IsDatatype dt2) => Field dt1 tp1 -> Field dt2 tp2
             -> GOrdering (Field dt1 tp1) (Field dt2 tp2)
fieldCompare (f1 :: Field dt1 tp1) (f2 :: Field dt2 tp2) = case eqT :: Maybe (dt1 :~: dt2) of
  Just Refl -> case gcompare f1 f2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  Nothing -> case compare (typeOf (Proxy::Proxy dt1)) (typeOf (Proxy::Proxy dt2)) of
    LT -> GLT
    GT -> GGT

registerType :: (Monad m,IsDatatype tp,Ord dt,Ord con,Ord field) => dt
             -> (forall sig. Constr tp sig -> m con)
             -> (forall tp'. Field tp tp' -> m field)
             -> Proxy tp -> TypeRegistry dt con field
             -> m (TypeRegistry dt con field)
registerType i f g (dt::Proxy dt) reg
  = List.foldM
    (\reg con -> do
        c <- f con
        let reg' = reg { allConstructors = Map.insert c (AnyConstr con) (allConstructors reg) }
        List.foldM (\reg field -> do
                       fi <- g field
                       return $ reg { allFields = Map.insert fi (AnyField field) (allFields reg) }
                   ) reg' (constrFields con)
    ) reg1 (constructors :: List (Constr dt) (Signature dt))
  where
    reg1 = reg { allDatatypes = Map.insert i (AnyDatatype dt) (allDatatypes reg)
               , revDatatypes = Map.insert (AnyDatatype dt) i (revDatatypes reg) }

registerTypeName :: IsDatatype dt => Proxy dt -> TypeRegistry String String String -> TypeRegistry String String String
registerTypeName dt reg = runIdentity (registerType (datatypeName dt) (return . constrName) (return . fieldName) dt reg)

instance Eq AnyDatatype where
  (==) (AnyDatatype x) (AnyDatatype y) = datatypeName x == datatypeName y

instance Eq AnyConstr where
  (==) (AnyConstr c1) (AnyConstr c2) = case constrEq c1 c2 of
    Just Refl -> True
    Nothing -> False

instance Eq AnyField where
  (==) (AnyField f1) (AnyField f2) = case fieldEq f1 f2 of
    Just Refl -> True
    Nothing -> False

instance Ord AnyDatatype where
  compare (AnyDatatype x) (AnyDatatype y) = compare (datatypeName x) (datatypeName y)

instance Ord AnyConstr where
  compare (AnyConstr c1) (AnyConstr c2) = case constrCompare c1 c2 of
    GEQ -> EQ
    GLT -> LT
    GGT -> GT

instance Ord AnyField where
  compare (AnyField f1) (AnyField f2) = case fieldCompare f1 f2 of
    GEQ -> EQ
    GLT -> LT
    GGT -> GT

data Test e = A { size :: e IntType
                , arr  :: e (ArrayType '[IntType] BoolType) }
            | B { cond :: e BoolType }
            deriving Typeable

instance IsDatatype Test where
  type Signature Test = [[IntType,ArrayType '[IntType] BoolType],'[BoolType]]
  data Constr Test sig where
    ConA :: Constr Test [IntType,ArrayType '[IntType] BoolType]
    ConB :: Constr Test '[BoolType]
  data Field Test tp where
    FieldSize :: Field Test IntType
    FieldArr  :: Field Test (ArrayType '[IntType] BoolType)
    FieldCond :: Field Test BoolType
  datatypeName _ = "Test"
  constructors = ConA ::: ConB ::: Nil
  constrName ConA = "A"
  constrName ConB = "B"
  constrTest (A {}) ConA = True
  constrTest (B {}) ConB = True
  constrTest _ _ = False
  constrFields ConA = FieldSize ::: FieldArr ::: Nil
  constrFields ConB = FieldCond ::: Nil
  constrApply (ConApp ConA (sz ::: arr ::: Nil)) = A sz arr
  constrApply (ConApp ConB (cond ::: Nil)) = B cond
  constrGet (A sz arr) = ConApp ConA (sz ::: arr ::: Nil)
  constrGet (B cond) = ConApp ConB (cond ::: Nil)
  fieldName FieldSize = "size"
  fieldName FieldArr = "arr"
  fieldName FieldCond = "cond"
  fieldType FieldSize = IntRepr
  fieldType FieldArr  = ArrayRepr (IntRepr ::: Nil) BoolRepr
  fieldType FieldCond = BoolRepr
  fieldGet dt FieldSize = size dt
  fieldGet dt FieldArr  = arr dt
  fieldGet dt FieldCond = cond dt

instance GEq (Constr Test) where
  geq ConA ConA = Just Refl
  geq ConB ConB = Just Refl
  geq _ _ = Nothing

instance GCompare (Constr Test) where
  gcompare ConA ConA = GEQ
  gcompare ConA _    = GLT
  gcompare _ ConA    = GGT
  gcompare ConB ConB = GEQ

instance GEq (Field Test) where
  geq FieldSize FieldSize = Just Refl
  geq FieldArr FieldArr = Just Refl
  geq FieldCond FieldCond = Just Refl
  geq _ _ = Nothing

instance GCompare (Field Test) where
  gcompare FieldSize FieldSize = GEQ
  gcompare FieldSize _         = GLT
  gcompare _ FieldSize         = GGT
  gcompare FieldArr FieldArr   = GEQ
  gcompare FieldArr _          = GLT
  gcompare _ FieldArr          = GGT
  gcompare FieldCond FieldCond = GEQ

-- | Values that can be used as constants in expressions.
data Value (a :: Type) where
  BoolValue :: Bool -> Value BoolType
  IntValue :: Integer -> Value IntType
  RealValue :: Rational -> Value RealType
  BitVecValue :: Integer -> Natural n -> Value (BitVecType n)
  DataValue :: IsDatatype dt => dt Value -> Value (DataType dt)

pattern ConstrValue con args <- DataValue (constrGet -> ConApp con args) where
  ConstrValue con args = DataValue (constrApply (ConApp con args))

data AnyValue = forall (t :: Type). AnyValue (Value t)

-- | A concrete representation of an SMT type.
--   For aesthetic reasons, it's recommended to use the functions 'bool', 'int', 'real', 'bitvec' or 'array'.
data Repr (t :: Type) where
  BoolRepr :: Repr BoolType
  IntRepr :: Repr IntType
  RealRepr :: Repr RealType
  BitVecRepr :: Natural n -> Repr (BitVecType n)
  ArrayRepr :: List Repr idx -> Repr val -> Repr (ArrayType idx val)
  DataRepr :: IsDatatype dt => Proxy dt -> Repr (DataType dt)

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
  geq (DataRepr _) (DataRepr _) = eqT
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
  gcompare (DataRepr (dt1 :: Proxy dt1)) (DataRepr (dt2 :: Proxy dt2)) = case eqT of
    Just (Refl :: dt1 :~: dt2) -> GEQ
    Nothing -> case compare (typeRep dt1) (typeRep dt2) of
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

deriving instance Show (Repr t)

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
valueType (DataValue (_::dt Value)) = DataRepr (Proxy::Proxy dt)

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

