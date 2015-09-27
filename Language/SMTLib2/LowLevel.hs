{-# LANGUAGE ViewPatterns,ConstraintKinds,QuasiQuotes #-}
module Language.SMTLib2.LowLevel (
  -- * SMT Monad
  Backend(Expr,Var,QVar,Fun,Constr,Field,FunArg,ClauseId),
  SMT(),withBackend,withBackendExitCleanly,
  SMTOption(..),setOption,
  SMTInfo(..),getInfo,
  comment,
  registerDatatype,
  -- * Queries
  CheckSatResult(..),
  assert,checkSat,push,pop,stack,
  -- * Models
  getValue,
  -- * Unsatisfiable Core
  assertId,getUnsatCore,
  -- * Interpolation
  Partition(..),assertPartition,interpolate,
  -- * Expressions
  Type(..),Nat(..),GetType(..),GetTypes(..),
  SMTExpr(..),SMTExpr'(..),SMTValue(..),Embed(..),Expression(..),Function(..),
  Args(..),
  -- ** Operators
  LogicOp(..),OrdOp(..),ArithOp(..),ArithOpInt(..),BVCompOp(..),BVBinOp(..),BVUnOp(..),
  -- ** Variables
  var,varNamed,
  -- ** Constants
  Value(..),
  constant,
  -- ** Comparison
  SMTOrd(..),
  -- ** Basic logic
  -- ** Arithmetic
  SMTArith(..),
  -- ** Functions
  fun,
  defFun,
  app,app',appLst,
  -- ** Arrays
  -- ** Bitvectors
  SMTBV(..)
  -- ** Accessors
  --asVar,asConstant,asEq
  ) where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Backend hiding (setOption,getInfo,comment,assert,
                                                  checkSat,getValue,push,pop,assertId,
                                                  getUnsatCore,interpolate,assertPartition,
                                                  Constr,Field)
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat

import Data.Typeable
import Data.Type.Equality
import Control.Monad.State.Strict
import Control.Monad.Identity
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IMap
import Data.GADT.Compare
import Data.GADT.Show
import Control.Exception (bracket)

newtype Backend b => SMT b a = SMT (StateT (SMTState b) (SMTMonad b) a)

data SMTState b = SMTState { backend :: !b
                           , datatypes :: !(DatatypeInfo (B.Constr b) (B.Field b)) }

instance Backend b => Functor (SMT b) where
  fmap f (SMT act) = SMT (fmap f act)

instance Backend b => Applicative (SMT b) where
  pure x = SMT (pure x)
  (<*>) (SMT fun) (SMT arg) = SMT (fun <*> arg)

instance Backend b => Monad (SMT b) where
  (>>=) (SMT act) app = SMT (act >>= (\res -> case app res of
                                                  SMT p -> p))

instance Backend b => MonadState (SMTState b) (SMT b) where
  get = SMT get
  put x = SMT (put x)
  state act = SMT (state act)

liftSMT :: Backend b => SMTMonad b a -> SMT b a
liftSMT act = SMT (lift act)

class (Typeable c,Show c,Ord c,ValueRepr c ~ repr,ValueType repr ~ c,GetType repr) => SMTValue c repr where
  type ValueRepr c :: Type
  type ValueType repr :: *
  toValue :: (Typeable con,Typeable field)
          => DatatypeInfo con field -> c -> Value con (ValueRepr c)
  fromValue :: (Typeable con,GCompare con,Typeable field)
            => DatatypeInfo con field -> Value con repr -> ValueType repr

instance SMTValue Bool BoolType where
  type ValueRepr Bool = BoolType
  type ValueType BoolType = Bool
  toValue _ b = BoolValue b
  fromValue _ (BoolValue b) = b

instance SMTValue Integer IntType where
  type ValueRepr Integer = IntType
  type ValueType IntType = Integer
  toValue _ i = IntValue i
  fromValue _ (IntValue i) = i

instance SMTValue Rational RealType where
  type ValueRepr Rational = RealType
  type ValueType RealType = Rational
  toValue _ v = RealValue v
  fromValue _ (RealValue v) = v

newtype SMTBV (bw::Nat) = SMTBV Integer deriving (Show,Eq,Ord)

instance KnownNat n => SMTValue (SMTBV n) (BitVecType n) where
  type ValueRepr (SMTBV n) = BitVecType n
  type ValueType (BitVecType n) = SMTBV n
  toValue _ (SMTBV v) = BitVecValue v
  fromValue _ (BitVecValue v) = SMTBV v

data DT dt = DT dt deriving (Show,Eq,Ord)

instance (IsDatatype dt) => SMTValue (DT dt) (DataType dt) where
  type ValueRepr (DT dt) = DataType dt
  type ValueType (DataType dt) = (DT dt)
  toValue info (DT (dt::dt)) = case Map.lookup (typeOf (Proxy::Proxy dt)) info of
    Just (RegisteredDT rdt) -> case castReg rdt of
      Just (rdt'::B.BackendDatatype con field '(DatatypeSig dt,dt))
        -> findConstr info dt (bconstructors rdt')
    where
      findConstr :: (Typeable con,Typeable field)
                 => DatatypeInfo con field
                 -> dt -> Constrs (B.BackendConstr con field) sig dt
                 -> Value con (DataType dt)
      findConstr info dt (ConsCon con cons)
        = if bconTest con dt
          then ConstrValue (bconRepr con) (extractVal info dt (bconFields con))
          else findConstr info dt cons

      castReg :: (Typeable con,Typeable field,
                  Typeable dt,Typeable dt',
                  Typeable (DatatypeSig dt),Typeable (DatatypeSig dt'))
              => B.BackendDatatype con field '(DatatypeSig dt',dt')
              -> Maybe (B.BackendDatatype con field '(DatatypeSig dt,dt))
      castReg = cast

      extractVal :: (Typeable con,Typeable field)
                 => DatatypeInfo con field
                 -> dt -> Args (B.BackendField field dt) arg
                 -> Args (Value con) arg
      extractVal info dt NoArg = NoArg
      extractVal info dt (Arg f fs) = Arg (transVal info $ bfieldGet f dt)
                                          (extractVal info dt fs)

      transVal :: (Typeable con,Typeable field)
               => DatatypeInfo con field
               -> ConcreteValue t
               -> Value con t
      transVal _ (BoolValueC b) = BoolValue b
      transVal _ (IntValueC v) = IntValue v
      transVal _ (RealValueC v) = RealValue v
      transVal _ (BitVecValueC v) = BitVecValue v
      transVal info (ConstrValueC v)
        = toValue info (DT v)
  fromValue info (ConstrValue con args :: Value con (DataType dt))
    = case Map.lookup (typeOf (Proxy::Proxy dt)) info of
        Just (RegisteredDT rdt) -> case castReg rdt of
          Just (rdt'::B.BackendDatatype con field '(DatatypeSig dt,dt))
            -> findConstr info con args (bconstructors rdt')
    where
      castReg :: (Typeable con,Typeable field,
                  Typeable dt,Typeable dt',
                  Typeable (DatatypeSig dt),Typeable (DatatypeSig dt'))
              => B.BackendDatatype con field '(DatatypeSig dt',dt')
              -> Maybe (B.BackendDatatype con field '(DatatypeSig dt,dt))
      castReg = cast

      findConstr :: (Typeable con,GEq con,Typeable field,GetTypes arg)
                 => DatatypeInfo con field
                 -> con '(arg,dt) -> Args (Value con) arg
                 -> Constrs (B.BackendConstr con field) sig dt
                 -> DT dt
      findConstr info con args (ConsCon con' cons)
        = case geq con (bconRepr con') of
            Just Refl -> DT (bconstruct con' (transArgs info args))
            Nothing -> findConstr info con args cons

      castCon :: (Typeable con,Typeable field,Typeable arg,Typeable arg',Typeable dt)
              => B.BackendConstr con field '(arg,dt)
              -> Maybe (B.BackendConstr con field '(arg',dt))
      castCon = cast

      transArgs :: Typeable field => DatatypeInfo con field
                -> Args (Value con) arg -> Args ConcreteValue arg
      transArgs info NoArg = NoArg
      transArgs info (Arg v vs) = Arg (transArg info v) (transArgs info vs)

      transArg :: Typeable field => DatatypeInfo con field -> Value con t -> ConcreteValue t
      transArg info (BoolValue b) = BoolValueC b
      transArg info (IntValue v) = IntValueC v
      transArg info (RealValue v) = RealValueC v
      transArg info (BitVecValue v) = BitVecValueC v
      transArg info val@(ConstrValue con args) = let DT v = fromValue info val
                                                 in ConstrValueC v

data AnyQVar b = forall t. GetType t => AnyQVar (QVar b t)

data SMTExpr b t where
  SMTExpr :: Expression (Var b)
                        (QVar b)
                        (Fun b)
                        (B.Constr b)
                        (B.Field b)
                        (FunArg b)
                        (SMTExpr b) t
          -> SMTExpr b t
  SpecialExpr :: SMTExpr' b t -> SMTExpr b t

data SMTExpr' b t where
  QVar' :: GetType t => Int -> !Int -> SMTExpr' b t
  Quantification' :: GetTypes arg => Quantifier -> Int -> Args Proxy arg
                  -> SMTExpr b BoolType
                  -> SMTExpr' b BoolType
  TestConstr :: IsDatatype dt => String -> Proxy (dt:: *) -> SMTExpr b (DataType dt) -> SMTExpr' b BoolType
  GetField :: (IsDatatype dt,GetType tp) => String -> String -> Proxy (dt :: *) -> Proxy tp -> SMTExpr b (DataType dt) -> SMTExpr' b tp
  Const' :: SMTValue c tp => c -> SMTExpr' b tp

instance Backend b => Show (SMTExpr' b t) where
  showsPrec p (QVar' lvl n) = showParen (p>10) $
                              showString "QVar' " .
                              showsPrec 11 lvl .
                              showChar ' ' .
                              showsPrec 11 n
  showsPrec p (Quantification' q lvl args body)
    = showParen (p>10) $
      showString "Quantification' " .
      showsPrec 11 q . showChar ' ' .
      showsPrec 11 lvl . showChar ' ' .
      showsPrec 11 (length (argsToList (const ()) args)) . showChar ' ' .
      showsPrec 11 body
  showsPrec p (Const' c) = showParen (p>10) $
                           showString "Const' " .
                           showsPrec 11 c

instance Backend b => GShow (SMTExpr' b) where
  gshowsPrec = showsPrec

instance Backend b => GEq (SMTExpr b) where
  geq (SMTExpr x) (SMTExpr y) = geq x y
  geq (SpecialExpr x) (SpecialExpr y) = geq x y
  geq _ _ = Nothing

instance Backend b => GEq (SMTExpr' b) where
  geq v1@(QVar' lvl1 nr1) v2@(QVar' lvl2 nr2)
    = if (lvl1,nr1) == (lvl2,nr2)
      then case v1 of
             (_::SMTExpr' b t1) -> case v2 of
               (_::SMTExpr' b t2) -> do
                 Refl <- eqT :: Maybe (t1 :~: t2)
                 return Refl
      else Nothing
  geq (Quantification' q1 lvl1 (_::Args Proxy args1) body1)
      (Quantification' q2 lvl2 (_::Args Proxy args2) body2)
    | (q1,lvl1) == (q2,lvl2) = do
        Refl <- geq (getTypes (Proxy::Proxy args1))
                    (getTypes (Proxy::Proxy args2))
        Refl <- geq body1 body2
        return Refl
    | otherwise = Nothing
  geq (TestConstr name1 _ body1) (TestConstr name2 _ body2)
    | name1==name2 = do
      Refl <- geq body1 body2
      return Refl
    | otherwise = Nothing
  geq (GetField cname1 fname1 _ (_::Proxy t1) body1)
      (GetField cname2 fname2 _ (_::Proxy t2) body2)
    | (cname1,fname1) == (cname2,fname2) = do
        Refl <- eqT :: Maybe (t1 :~: t2)
        Refl <- geq body1 body2
        return Refl
    | otherwise = Nothing
  geq (Const' (c1::t1)) (Const' (c2::t2)) = do
    Refl <- eqT :: Maybe (t1 :~: t2)
    if c1==castWith Refl c2
      then return Refl
      else Nothing
  geq _ _ = Nothing

instance Backend b => GCompare (SMTExpr b) where
  gcompare (SMTExpr x) (SMTExpr y) = gcompare x y
  gcompare (SMTExpr _) _ = GLT
  gcompare _ (SMTExpr _) = GGT
  gcompare (SpecialExpr e1) (SpecialExpr e2) = gcompare e1 e2

instance Backend b => GCompare (SMTExpr' b) where
  gcompare q1@(QVar' lvl1 nr1) q2@(QVar' lvl2 nr2)
    = case compare (lvl1,nr1) (lvl2,nr2) of
        EQ -> case q1 of
          (_::SMTExpr' b t1) -> case q2 of
            (_::SMTExpr' b t2) -> gcompare (getType (Proxy::Proxy t1))
                                           (getType (Proxy::Proxy t2))
        LT -> GLT
        GT -> GGT
  gcompare (QVar' _ _) _ = GLT
  gcompare _ (QVar' _ _) = GGT
  gcompare e1@(Quantification' q1 lvl1 args1 body1) e2@(Quantification' q2 lvl2 args2 body2)
    = case compare (q1,lvl1) (q2,lvl2) of
        EQ -> case e1 of
          (_::SMTExpr' b t1) -> case e2 of
            (_::SMTExpr' b t2) -> gcompare (getType (Proxy::Proxy t1))
                                           (getType (Proxy::Proxy t2))
        GT -> GGT
        LT -> GLT
  gcompare (Quantification' _ _ _ _) _ = GLT
  gcompare _ (Quantification' _ _ _ _) = GGT
  gcompare (TestConstr name1 _ body1) (TestConstr name2 _ body2) = case compare name1 name2 of
    EQ -> case gcompare body1 body2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (TestConstr _ _ _) _ = GLT
  gcompare _ (TestConstr _ _ _) = GGT
  gcompare (GetField cname1 fname1 _ (Proxy::Proxy t1) body1)
           (GetField cname2 fname2 _ (Proxy::Proxy t2) body2)
    = case compare (cname1,fname1) (cname2,fname2) of
        EQ -> case gcompare body1 body2 of
          GEQ -> case eqT :: Maybe (t1 :~: t2) of
            Just Refl -> GEQ
          GLT -> GLT
          GGT -> GGT
        LT -> GLT
        GT -> GGT
  gcompare (GetField _ _ _ _ _) _ = GLT
  gcompare _ (GetField _ _ _ _ _) = GGT
  gcompare (Const' (c1::t1)) (Const' (c2::t2)) = case eqT :: Maybe (t1 :~: t2) of
    Just Refl -> case compare c1 (castWith Refl c2) of
      EQ -> GEQ
      LT -> GLT
      GT -> GGT
    Nothing -> case compare (typeOf c1) (typeOf c2) of
      LT -> GLT
      GT -> GGT

instance Backend b => Show (SMTExpr b t) where
  showsPrec p (SMTExpr e) = showsPrec p e
  showsPrec p (SpecialExpr e) = showsPrec p e

instance Backend b => GShow (SMTExpr b) where
  gshowsPrec = showsPrec

instance Backend b => Embed (SMTExpr b) where
  type EmbedBackend (SMTExpr b) = b
  type EmbedSub (SMTExpr b) = SMTExpr' b
  type EmbedState (SMTExpr b) = IMap.IntMap [AnyQVar b]
  embed = SMTExpr
  embedQuantifier q (f::Args (SMTExpr b) arg -> SMTExpr b BoolType)
    = SpecialExpr (Quantification' q level qargs body)
    where
      body = f args
      level = getLevel body
      --level = 0
      args = mkArg 0 (getTypes $ (Proxy::Proxy arg))
      qargs = runIdentity $ mapArgs (\_ -> return Proxy) args

      mkArg :: Int -> Args Repr arg' -> Args (SMTExpr b) arg'
      mkArg n NoArg = NoArg
      mkArg n (Arg _ xs) = Arg (SpecialExpr $ QVar' level n) (mkArg (n+1) xs)

      getLevel :: SMTExpr b t -> Int
      getLevel (SMTExpr (App _ args)) = maximum $ argsToList getLevel args
      getLevel (SMTExpr (Let bind body))
        = maximum $ (getLevel body):(argsToList (getLevel . letExpr) bind)
      getLevel (SpecialExpr e) = case e of
        Quantification' _ lvl _ _ -> lvl+1
        TestConstr _ _ dt -> getLevel dt
        GetField _ _ _ _ dt -> getLevel dt
        _ -> 0
      getLevel _ = 0

  extract (SMTExpr e) = Left e
  extract (SpecialExpr e) = Right e

  encodeSub pr e = encode' pr IMap.empty (SpecialExpr e)
    where
      encode' :: (Embed e,GetType tp)
              => Proxy e
              -> IMap.IntMap [AnyQVar (EmbedBackend e)]
              -> SMTExpr (EmbedBackend e) tp
              -> SMT (EmbedBackend e) (Expr (EmbedBackend e) tp)
      encode' pr mp (SpecialExpr (Quantification' q lvl vars body)) = do
        (lst,qarg) <- declareQVars pr vars
        let nmp = IMap.insert lvl lst mp
        body' <- encode' pr nmp body
        updateBackend $ \b -> B.toBackend b (Quantification q qarg body')
      encode' _ mp (SpecialExpr (QVar' lvl nr)) = case IMap.lookup lvl mp of
        Just vars -> case vars!!nr of
          AnyQVar qv -> case gcast qv of
            Just qv' -> updateBackend $ \b -> B.toBackend b (QVar qv')
      encode' pr mp (SpecialExpr (TestConstr con dt expr)) = do
        st <- get
        lookupDatatypeCon dt con (datatypes st) $
          \rcon -> do
               expr' <- encode' pr mp expr
               let res = App (Test $ bconRepr rcon) (Arg expr' NoArg)
               updateBackend $ \b -> B.toBackend b res
      encode' pr mp (SpecialExpr (GetField field con dt (_::Proxy tp) expr)) = do
        st <- get
        lookupDatatypeField dt con field (datatypes st) $
          \rfield -> case gcast rfield of
             Just rfield' -> do
               expr' <- encode' pr mp expr
               let res = App (Field $ bfieldRepr rfield') (Arg expr' NoArg)
               updateBackend $ \b -> B.toBackend b res
      encode' pr mp (SpecialExpr (Const' c)) = do
        st <- get
        updateBackend $ \b -> B.toBackend b (Const $ toValue (datatypes st) c)
      encode' pr mp (SMTExpr e) = do
        e' <- mapSubExpressions (encode' pr mp) e
        updateBackend $ \b -> B.toBackend b e'

      declareQVars :: Embed e => Proxy e -> Args Proxy arg
                   -> SMT (EmbedBackend e) ([AnyQVar (EmbedBackend e)],
                                            Args (QVar (EmbedBackend e)) arg)
      declareQVars _ NoArg = return ([],NoArg)
      declareQVars pr (Arg _ args) = do
        qvar <- updateBackend (\b -> createQVar b Nothing)
        (lst,args') <- declareQVars pr args
        return ((AnyQVar qvar):lst,Arg qvar args')

  extractSub _ = return Nothing

class (Backend (EmbedBackend e),GShow e) => Embed e where
  type EmbedBackend e :: *
  type EmbedSub e :: Type -> *
  type EmbedState e :: *
  embed :: GetType tp
        => Expression (Var (EmbedBackend e))
                      (QVar (EmbedBackend e))
                      (Fun (EmbedBackend e))
                      (B.Constr (EmbedBackend e))
                      (B.Field (EmbedBackend e))
                      (FunArg (EmbedBackend e)) e tp
        -> e tp
  embedQuantifier :: GetTypes arg => Quantifier
                  -> (Args e arg -> e BoolType)
                  -> e BoolType
  extract :: GetType tp
          => e tp
          -> Either (Expression (Var (EmbedBackend e))
                                (QVar (EmbedBackend e))
                                (Fun (EmbedBackend e))
                                (B.Constr (EmbedBackend e))
                                (B.Field (EmbedBackend e))
                                (FunArg (EmbedBackend e)) e tp)
                    (EmbedSub e tp)
  encodeSub :: GetType tp => Proxy e -> EmbedSub e tp
            -> SMT (EmbedBackend e) (Expr (EmbedBackend e) tp)
  extractSub :: Expr (EmbedBackend e) tp -> SMT (EmbedBackend e) (Maybe (e tp))

type DatatypeInfo con field = Map.Map TypeRep (RegisteredDT con field)

data RegisteredDT con field
  = forall dt. IsDatatype dt => RegisteredDT (B.BackendDatatype con field '(DatatypeSig dt,dt))
  deriving (Typeable)

registerDatatype :: (Backend b,IsDatatype dt) => Proxy dt -> SMT b ()
registerDatatype pr = do
  let repr = typeOf pr
  st <- get
  if Map.member repr (datatypes st)
    then return ()
    else do
      (dts,nb) <- liftSMT $ B.declareDatatypes (backend st) (getTypeCollection pr)
      put $ st { backend = nb
               , datatypes = insertTypes dts (datatypes st) }
  where
    insertTypes :: B.BackendTypeCollection con field sigs -> DatatypeInfo con field -> DatatypeInfo con field
    insertTypes NoDts mp = mp
    insertTypes (ConsDts (dt::B.BackendDatatype con field '(DatatypeSig dt,dt)) dts) mp
      = let repr = typeOf (Proxy::Proxy dt)
            nmp =  Map.insert repr (RegisteredDT dt) mp
         in insertTypes dts nmp

lookupDatatype :: TypeRep -> DatatypeInfo con field
               -> (forall dt. IsDatatype dt => B.BackendDatatype con field '(DatatypeSig dt,dt) -> a)
               -> a
lookupDatatype rep dts f = case Map.lookup rep dts of
  Just (RegisteredDT dt) -> f dt
  Nothing -> error $ "smtlib2: Datatype "++show rep++" is not registered."

lookupConstructor :: String -> B.BackendDatatype con field '(DatatypeSig dt,dt)
                  -> (forall arg. GetTypes arg => B.BackendConstr con field '(arg,dt) -> a)
                  -> a
lookupConstructor name dt f = lookup (bconstructors dt) f
  where
    lookup :: Constrs (B.BackendConstr con field) sigs dt
           -> (forall arg. GetTypes arg => B.BackendConstr con field '(arg,dt) -> a)
           -> a
    lookup NoCon _ = error $ "smtlib2: "++name++" is not a constructor."
    lookup (ConsCon con cons) f = if bconName con==name
                                  then f con
                                  else lookup cons f


lookupField :: String -> B.BackendConstr con field '(arg,dt)
            -> (forall tp. GetType tp => B.BackendField field dt tp -> a)
            -> a
lookupField name con f = lookup (bconFields con) f
  where
    lookup :: Args (B.BackendField field dt) arg
           -> (forall tp. GetType tp => B.BackendField field dt tp -> a)
           -> a
    lookup NoArg _ = error $ "smtlib2: "++name++" is not a field."
    lookup (Arg x xs) f = if bfieldName x==name
                          then f x
                          else lookup xs f

lookupDatatypeCon :: (IsDatatype dt,Typeable con,Typeable field)
                  => Proxy dt -> String -> DatatypeInfo con field
                  -> (forall arg. GetTypes arg => B.BackendConstr con field '(arg,dt) -> a)
                  -> a
lookupDatatypeCon pr name info f
  = lookupDatatype (typeOf pr) info $
    \dt -> case cast dt of
       Just dt' -> lookupConstructor name dt' f

lookupDatatypeField :: (IsDatatype dt,Typeable con,Typeable field)
                  => Proxy dt -> String -> String -> DatatypeInfo con field
                  -> (forall tp. GetType tp => B.BackendField field dt tp -> a)
                  -> a
lookupDatatypeField pr con field info f
  = lookupDatatypeCon pr con info $
    \con' -> lookupField field con' f

withBackend :: Backend b => b -> SMT b a -> SMTMonad b a
withBackend b (SMT act) = do
  (res,nb) <- runStateT act (SMTState b Map.empty)
  exit (backend nb)
  return res

withBackendExitCleanly :: (Backend b,SMTMonad b ~ IO) => b -> SMT b a -> IO a
withBackendExitCleanly b (SMT act)
  = bracket
    (return b)
    (\b -> exit b)
    (\b -> do
        (res,nb) <- runStateT act (SMTState b Map.empty)
        return res)


app :: (Embed e,GetType tp,GetTypes arg)
    => Function (Fun (EmbedBackend e)) (B.Constr (EmbedBackend e)) (B.Field (EmbedBackend e)) '(arg,tp)
    -> Args e arg
    -> e tp
app f arg = embed (App f arg)

appLst :: (Embed e,GetType tp,GetType t,
           fun ~ Fun (EmbedBackend e),
           con ~ B.Constr (EmbedBackend e),field ~ B.Field (EmbedBackend e))
       => (forall arg. (AllEq arg,SameType arg ~ t) => Function fun con field '(arg,tp))
       -> [e t]
       -> e tp
appLst fun args = embed $ allEqFromList args $ App fun

map' :: (GetTypes arg,GetTypes idx,GetType res)
     => Function fun con field '(arg,res)
     -> Function fun con field '(Lifted arg idx,ArrayType idx res)
map' = Map

class GetType t => SMTOrd (t :: Type) where
  lt :: Function fun con field '( '[t,t],BoolType)
  le :: Function fun con field '( '[t,t],BoolType)
  gt :: Function fun con field '( '[t,t],BoolType)
  ge :: Function fun con field '( '[t,t],BoolType)

instance SMTOrd IntType where
  lt = OrdInt Lt
  le = OrdInt Le
  gt = OrdInt Gt
  ge = OrdInt Ge

instance SMTOrd RealType where
  lt = OrdReal Lt
  le = OrdReal Le
  gt = OrdReal Gt
  ge = OrdReal Ge

mapSubExpressions :: (Monad m,GetType tp)
                  => (forall t. GetType t => e t -> m (e' t))
                  -> Expression v qv fun con field fv e tp
                  -> m (Expression v qv fun con field fv e' tp)
mapSubExpressions f (Var v) = return $ Var v
mapSubExpressions f (QVar v) = return $ QVar v
mapSubExpressions f (FVar v) = return $ FVar v
mapSubExpressions f (App fun arg) = do
  arg' <- mapArgs f arg
  return (App fun arg')
mapSubExpressions f (Const c) = return $ Const c
mapSubExpressions f (AsArray fun) = return $ AsArray fun
mapSubExpressions f (Quantification q args body) = do
  body' <- f body
  return (Quantification q args body')
mapSubExpressions f (Let bnds body) = do
  bnds' <- mapArgs (\bnd -> do
                       ne <- f (letExpr bnd)
                       return (bnd { letExpr = ne })
                   ) bnds
  body' <- f body
  return (Let bnds' body')

updateBackend :: Backend b => (b -> SMTMonad b (a,b)) -> SMT b a
updateBackend act = do
  st <- get
  (res,nb) <- liftSMT $ act (backend st)
  put $ st { backend = nb }
  return res

updateBackend' :: Backend b => (b -> SMTMonad b b) -> SMT b ()
updateBackend' act = do
  st <- get
  nb <- liftSMT $ act (backend st)
  put $ st { backend = nb }

-- SMT functions
checkSat :: Backend b => SMT b B.CheckSatResult
checkSat = updateBackend (\b -> B.checkSat b Nothing (B.CheckSatLimits Nothing Nothing))

getUnsatCore :: Backend b => SMT b [ClauseId b]
getUnsatCore = updateBackend B.getUnsatCore

push :: Backend b => SMT b ()
push = updateBackend' B.push

pop :: Backend b => SMT b ()
pop = updateBackend' B.pop

stack :: Backend b => SMT b a -> SMT b a
stack act = do
  push
  res <- act
  pop
  return res

comment :: Backend b => String -> SMT b ()
comment str = updateBackend' $ \b -> B.comment b str

setOption :: Backend b => SMTOption -> SMT b ()
setOption opt = updateBackend' $ \b -> B.setOption b opt

getInfo :: Backend b => SMTInfo i -> SMT b i
getInfo inf = updateBackend $ \b -> B.getInfo b inf

toBackendExpr :: (Embed e,GetType tp)
              => e tp
              -> SMT (EmbedBackend e) (Expr (EmbedBackend e) tp)
toBackendExpr (e :: e tp) = case extract e of
  Left e' -> do
    e'' <- mapSubExpressions toBackendExpr e'
    updateBackend $ \b -> B.toBackend b e''
  Right sub -> encodeSub (Proxy::Proxy e) sub

fromBackendExpr :: (Embed e,GetType tp)
                => Expr (EmbedBackend e) tp -> SMT (EmbedBackend e) (e tp)
fromBackendExpr e = do
  sub <- extractSub e
  case sub of
    Just sub' -> return sub'
    Nothing -> do
      e' <- updateBackend $ \b -> B.fromBackend b e
      e'' <- mapSubExpressions fromBackendExpr e'
      return $ embed e''

assert :: (Embed e) => e BoolType -> SMT (EmbedBackend e) ()
assert e = do
  e' <- toBackendExpr e
  updateBackend' $ \b -> B.assert b e'

assertId :: (Embed e) => e BoolType -> SMT (EmbedBackend e) (ClauseId (EmbedBackend e))
assertId e = do
  e' <- toBackendExpr e
  updateBackend $ \b -> B.assertId b e'

assertPartition :: (Embed e) => e BoolType -> Partition -> SMT (EmbedBackend e) ()
assertPartition e part = do
  e' <- toBackendExpr e
  updateBackend' $ \b -> B.assertPartition b e' part

interpolate :: (Embed e) => SMT (EmbedBackend e) (e BoolType)
interpolate = do
  interp <- updateBackend B.interpolate
  fromBackendExpr interp

var :: (Embed e,GetType t) => SMT (EmbedBackend e) (e t)
var = do
  v <- updateBackend $ \b -> B.declareVar b Nothing
  return $ embed (Var v)

varNamed :: (Embed e,GetType t) => String -> SMT (EmbedBackend e) (e t)
varNamed name = do
  v <- updateBackend $ \b -> B.declareVar b (Just name)
  return $ embed (Var v)

constant :: (Embed e,GetType t) => Value (B.Constr (EmbedBackend e)) t -> e t
constant v = embed (Const v)

getValue :: (Embed e,SMTValue c repr) => e repr -> SMT (EmbedBackend e) c
getValue e = do
  e' <- toBackendExpr e
  val <- updateBackend $ \b -> B.getValue b e'
  dtinfo <- gets datatypes
  return $ fromValue dtinfo val

fun :: (Backend b,GetTypes arg,GetType res) => SMT b (Function (Fun b) con field '(arg,res))
fun = do
  fun <- updateBackend $ \b -> declareFun b Nothing
  return (Fun fun)

defFun :: (Embed e,GetTypes arg,GetType res)
       => (Args e arg -> e res)
       -> SMT (EmbedBackend e) (Function (Fun (EmbedBackend e)) con field '(arg,res))
defFun (f :: Args e arg -> e res) = do
  args <- mapArgs (\_ -> updateBackend $ \b -> B.createFunArg b Nothing
                  ) (getTypes (Proxy::Proxy arg))
  fargs <- mapArgs (return . embed . FVar) args
  body <- toBackendExpr (f fargs)
  fun <- updateBackend $ \b -> B.defineFun b Nothing args body
  return (Fun fun)

class GetType t => SMTArith t where
  plus :: (AllEq arg, SameType arg ~ t)
       => Function fun con field '(arg,t)
  minus :: (AllEq arg,SameType arg ~ t)
        => Function fun con field '(arg,t)
  mult :: (AllEq arg, SameType arg ~ t)
       => Function fun con field '(arg,t)
  abs' :: Function fun con field '( '[t],t)

instance SMTArith IntType where
  plus = ArithInt Plus
  minus = ArithInt Minus
  mult = ArithInt Mult
  abs' = AbsInt

instance SMTArith RealType where
  plus = ArithReal Plus
  minus = ArithReal Minus
  mult = ArithReal Mult
  abs' = AbsReal

class (AppExpr' fun ~ e,
       AppRet' sig fun ~ res,
       AppFun' sig e res ~ fun
       --AppSig' fun ~ sig
      )
      => MkApp (sig :: [Type]) (e::Type -> *) res fun where
  type AppFun' sig e res
  type AppExpr' fun :: Type -> *
  type AppRet' sig fun
  --type AppSig' fun :: [Type]
  toApp :: (Args e sig -> res) -> fun

instance GetType t => MkApp '[t] e res (e t -> res) where
  type AppFun' '[t] e res = e t -> res
  type AppExpr' (e t -> res) = e
  type AppRet' '[t] (e t -> res) = res
  --type AppSig' (e t -> res) = '[t]
  toApp f x = f (Arg x NoArg)

instance (GetType x1,MkApp (x2 ': xs) e res fun)
         => MkApp (x1 ': x2 ': xs) e res (e x1 -> fun) where
  type AppFun' (x1 ': x2 ': xs) e res = e x1 -> AppFun' (x2 ': xs) e res
  type AppExpr' (e x1 -> fun) = e
  type AppRet' (x1 ': x2 ': xs) (e x1 -> fun) = AppRet' (x2 ': xs) fun
  --type AppSig' (e x1 -> fun) = x1 ': AppSig' fun
  toApp f p = toApp (\arg -> f (Arg p arg))

app' :: (Embed e,GetTypes sig,MkApp sig e (e ret) rfun,GetType ret)
    => Function (Fun (EmbedBackend e)) (B.Constr (EmbedBackend e)) (B.Field (EmbedBackend e)) '(sig,ret)
    -> rfun
app' fun = toApp (embed . App fun)
