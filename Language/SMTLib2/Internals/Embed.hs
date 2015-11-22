module Language.SMTLib2.Internals.Embed where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Backend

import Data.Functor.Identity
import Data.Proxy
import Control.Monad.State
import Control.Monad.Trans
import Data.Typeable
import Data.GADT.Compare

class (Monad m,Typeable (EmConstr m e)) => Embed m e where
  type EmVar m e :: Type -> *
  type EmQVar m e :: Type -> *
  type EmFun m e :: ([Type],Type) -> *
  type EmConstr m e :: ([Type],*) -> *
  type EmField m e :: (*,Type) -> *
  type EmFunArg m e :: Type -> *
  embed :: GetType tp => Expression (EmVar m e) (EmQVar m e) (EmFun m e) (EmConstr m e) (EmField m e) (EmFunArg m e) e tp
        -> m (e tp)
  embedQuantifier :: GetTypes arg => Quantifier
                  -> (forall m e. Embed m e => Args (EmQVar m e) arg -> m (e BoolType))
                  -> m (e BoolType)
  embedConstrTest :: IsDatatype dt => String -> Proxy dt -> e (DataType dt)
                  -> m (e BoolType)
  embedGetField :: (IsDatatype dt,GetType tp)
                => String -> String -> Proxy dt -> Proxy tp
                -> e (DataType dt)
                -> m (e tp)
  embedConst :: GetType tp => ConcreteValue tp -> m (e tp)

class (GCompare (ExVar i e),
       GCompare (ExQVar i e),
       GCompare (ExFun i e),
       GCompare (ExConstr i e),
       GCompare (ExField i e),
       GCompare (ExFunArg i e),
       Typeable (ExConstr i e)) => Extract i e where
  type ExVar i e :: Type -> *
  type ExQVar i e :: Type -> *
  type ExFun i e :: ([Type],Type) -> *
  type ExConstr i e :: ([Type],*) -> *
  type ExField i e :: (*,Type) -> *
  type ExFunArg i e :: Type -> *
  extract :: GetType tp => i -> e tp
          -> Maybe (Expression (ExVar i e) (ExQVar i e) (ExFun i e) (ExConstr i e) (ExField i e) (ExFunArg i e) e tp)

instance (Backend b,e ~ Expr b) => Embed (SMT b) e where
  type EmVar (SMT b) e = Var b
  type EmQVar (SMT b) e = QVar b
  type EmFun (SMT b) e = Fun b
  type EmConstr (SMT b) e = Constr b
  type EmField (SMT b) e = Field b
  type EmFunArg (SMT b) e = FunArg b
  embed = embedSMT . toBackend
  embedQuantifier quant f = do
    args <- withArgs (embedSMT (createQVar Nothing))
    body <- f args
    embedSMT $ toBackend (Quantification quant args body)
  embedConstrTest name (_::Proxy dt) e = do
    st <- get
    let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
    lookupConstructor name bdt $
      \bcon -> embedSMT $ toBackend (App (Test (bconRepr bcon)) (Arg e NoArg))
  embedGetField name fname (_::Proxy dt) _ e = do
    st <- get
    lookupDatatypeField (DTProxy::DTProxy dt) fname name (datatypes st) $
      \field -> case gcast (bfieldRepr field) of
      Just field' -> embedSMT $ toBackend (App (Field field') (Arg e NoArg))
  embedConst v = do
    rv <- mkAbstr v
    embedSMT $ toBackend (Const rv)

newtype BackendInfo b = BackendInfo b

instance (Backend b,e ~ Expr b) => Extract (BackendInfo b) e where
  type ExVar (BackendInfo b) e = Var b
  type ExQVar (BackendInfo b) e = QVar b
  type ExFun (BackendInfo b) e = Fun b
  type ExConstr (BackendInfo b) e = Constr b
  type ExField (BackendInfo b) e = Field b
  type ExFunArg (BackendInfo b) e = FunArg b
  extract (BackendInfo b) e = Just (fromBackend b e)

data SMTExpr var qvar fun con field farg tp where
  SMTExpr :: Expression var qvar fun con field farg
             (SMTExpr var qvar fun con field farg)
             tp -> SMTExpr var qvar fun con field farg tp
  SMTQuant :: GetTypes args
           => Quantifier
           -> (Args qvar args
               -> SMTExpr var qvar fun con field farg BoolType)
           -> SMTExpr var qvar fun con field farg BoolType
  SMTTestCon :: IsDatatype dt => String -> Proxy dt
             -> SMTExpr var qvar fun con field farg (DataType dt)
             -> SMTExpr var qvar fun con field farg BoolType
  SMTGetField :: (IsDatatype dt,GetType tp)
              => String -> String -> Proxy dt -> Proxy tp
              -> SMTExpr var qvar fun con field farg (DataType dt)
              -> SMTExpr var qvar fun con field farg tp
  SMTConst :: ConcreteValue tp -> SMTExpr var qvar fun con field farg tp

instance Typeable con => Embed Identity (SMTExpr var qvar fun con field farg) where
  type EmVar Identity (SMTExpr var qvar fun con field farg) = var
  type EmQVar Identity (SMTExpr var qvar fun con field farg) = qvar
  type EmFun Identity (SMTExpr var qvar fun con field farg) = fun
  type EmConstr Identity (SMTExpr var qvar fun con field farg) = con
  type EmField Identity (SMTExpr var qvar fun con field farg) = field
  type EmFunArg Identity (SMTExpr var qvar fun con field farg) = farg
  embed e = return (SMTExpr e)
  embedQuantifier quant f = return $ SMTQuant quant (runIdentity . f)
  embedConstrTest name pr e = return $ SMTTestCon name pr e
  embedGetField name fname dt pr e = return $ SMTGetField name fname dt pr e
  embedConst = return . SMTConst

instance (GCompare var,
          GCompare qvar,
          GCompare fun,
          GCompare con,
          GCompare field,
          GCompare farg,
          Typeable con) => Extract () (SMTExpr var qvar fun con field farg) where
  type ExVar () (SMTExpr var qvar fun con field farg) = var
  type ExQVar () (SMTExpr var qvar fun con field farg) = qvar
  type ExFun () (SMTExpr var qvar fun con field farg) = fun
  type ExConstr () (SMTExpr var qvar fun con field farg) = con
  type ExField () (SMTExpr var qvar fun con field farg) = field
  type ExFunArg () (SMTExpr var qvar fun con field farg) = farg
  extract _ (SMTExpr e) = Just e
  extract _ _ = Nothing

encodeExpr :: (Backend b,GetType tp)
           => SMTExpr (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) tp
           -> SMT b (Expr b tp)
encodeExpr (SMTExpr e) = do
  e' <- mapExpr return return return return return return
        encodeExpr e
  embedSMT $ toBackend e'
encodeExpr (SMTQuant q f) = do
  args <- withArgs (embedSMT (createQVar Nothing))
  body <- encodeExpr (f args)
  embedSMT $ toBackend (Quantification q args body)
encodeExpr (SMTTestCon name (_::Proxy dt) e) = do
  e' <- encodeExpr e
  st <- get
  let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
  lookupConstructor name bdt $
    \bcon -> embedSMT $ toBackend (App (Test (bconRepr bcon)) (Arg e' NoArg))
encodeExpr (SMTGetField name fname (_::Proxy dt) _ e) = do
  e' <- encodeExpr e
  st <- get
  lookupDatatypeField (DTProxy::DTProxy dt) fname name (datatypes st) $
    \field -> case gcast (bfieldRepr field) of
    Just field' -> embedSMT $ toBackend (App (Field field') (Arg e' NoArg))
encodeExpr (SMTConst c) = do
  rc <- mkAbstr c
  embedSMT $ toBackend (Const rc)

decodeExpr :: (Backend b,GetType tp) => Expr b tp
           -> SMT b (SMTExpr (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) tp)
decodeExpr e = do
  st <- get
  let e' = fromBackend (backend st) e
  e'' <- mapExpr return return return return return return decodeExpr e'
  return (SMTExpr e'')

instance (MonadTrans t,Monad (t m),Embed m e) => Embed (t m) e where
  type EmVar (t m) e = EmVar m e
  type EmQVar (t m) e = EmQVar m e
  type EmFun (t m) e = EmFun m e
  type EmConstr (t m) e = EmConstr m e
  type EmField (t m) e = EmField m e
  type EmFunArg (t m) e = EmFunArg m e
  embed = lift . embed
  embedQuantifier q f = lift (embedQuantifier q f)
  embedConstrTest name dt e = lift (embedConstrTest name dt e)
  embedGetField name fname dt pr e = lift (embedGetField name fname dt pr e)
  embedConst = lift . embedConst

data AnalyzedExpr i e tp
  = AnalyzedExpr (Maybe (Expression
                         (ExVar i e)
                         (ExQVar i e)
                         (ExFun i e)
                         (ExConstr i e)
                         (ExField i e)
                         (ExFunArg i e)
                         (AnalyzedExpr i e)
                         tp)) (e tp)

analyze' :: (Extract i e,GetType tp) => i -> e tp -> AnalyzedExpr i e tp
analyze' i expr
  = AnalyzedExpr expr' expr
  where
    expr' = do
      e <- extract i expr
      return $ runIdentity (mapExpr return return return return return return
                            (return . analyze' i) e)

analyze :: (Backend b,GetType tp) => Expr b tp -> SMT b (AnalyzedExpr (BackendInfo b) (Expr b) tp)
analyze e = do
  st <- get
  return (analyze' (BackendInfo (backend st)) e)

{-
import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Monad

import Data.GADT.Show
import Data.GADT.Compare
import Data.Proxy
import Data.Typeable
import Data.Constraint
import qualified Data.Map.Strict as Map

class (Backend (EmbedBackend e),GShow e) => Embed e where
  type EmbedBackend e :: *
  type EmbedSub e :: Type -> *
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
  embedConstant :: (ToSMT c,FromSMT (ValueRepr c),ValueType (ValueRepr c) ~ c)
                => c -> e (ValueRepr c)
  embedConstrTest :: IsDatatype dt => String -> Proxy dt -> e (DataType dt) -> e BoolType
  embedGetField :: (IsDatatype dt,GetType tp)
                => String -> String -> Proxy dt -> Proxy tp
                -> e (DataType dt) -> e tp
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

class (GetType repr,ToSMT (ValueType repr),ValueRepr (ValueType repr) ~ repr) => FromSMT repr where
  type ValueType repr :: *
  fromValue :: (Typeable con,GCompare con,Typeable field)
            => DatatypeInfo con field -> Value con repr -> ValueType repr

class (Typeable tp,Show tp,Ord tp) => ToSMT tp where
  type ValueRepr tp :: Type
  toValue :: (Typeable con,Typeable field)
          => DatatypeInfo con field -> tp -> Value con (ValueRepr tp)
  toSMTCtx :: Proxy tp -> Dict (FromSMT (ValueRepr tp),ValueType (ValueRepr tp) ~ tp)

instance FromSMT BoolType where
  type ValueType BoolType = Bool
  fromValue _ (BoolValue b) = b

instance ToSMT Bool where
  type ValueRepr Bool = BoolType
  toValue _ b = BoolValue b
  toSMTCtx _ = Dict

instance FromSMT IntType where
  type ValueType IntType = Integer
  fromValue _ (IntValue i) = i

instance ToSMT Integer where
  type ValueRepr Integer = IntType
  toValue _ i = IntValue i
  toSMTCtx _ = Dict

instance FromSMT RealType where
  type ValueType RealType = Rational
  fromValue _ (RealValue v) = v

instance ToSMT Rational where
  type ValueRepr Rational = RealType
  toValue _ v = RealValue v
  toSMTCtx _ = Dict

newtype SMTBV (bw::Nat) = SMTBV Integer deriving (Show,Eq,Ord)

instance KnownNat n => FromSMT (BitVecType n) where
  type ValueType (BitVecType n) = SMTBV n
  fromValue _ (BitVecValue v) = SMTBV v

instance KnownNat n => ToSMT (SMTBV n) where
  type ValueRepr (SMTBV n) = BitVecType n
  toValue _ (SMTBV v) = BitVecValue v
  toSMTCtx _ = Dict

data DT dt = DT dt deriving (Show,Eq,Ord)

instance (IsDatatype dt) => FromSMT (DataType dt) where
  type ValueType (DataType dt) = (DT dt)
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

instance IsDatatype dt => ToSMT (DT dt) where
  type ValueRepr (DT dt) = DataType dt
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
  toSMTCtx _ = Dict
-}
