module Language.SMTLib2.Internals.Monad where

import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type

import Control.Monad.State.Strict
import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as Map
import Control.Exception (onException)

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

instance (Backend b,MonadIO (SMTMonad b)) => MonadIO (SMT b) where
  liftIO act = SMT (liftIO act)

withBackend :: Backend b => SMTMonad b b -> SMT b a -> SMTMonad b a
withBackend constr (SMT act) = do
  b <- constr
  (res,nb) <- runStateT act (SMTState b emptyDatatypeInfo)
  exit (backend nb)
  return res

withBackendExitCleanly :: (Backend b,SMTMonad b ~ IO) => IO b -> SMT b a -> IO a
withBackendExitCleanly constr (SMT act) = do
  b <- constr
  (do
      (res,nb) <- runStateT act (SMTState b emptyDatatypeInfo)
      exit (backend nb)
      return res) `onException` (exit b)

liftSMT :: Backend b => SMTMonad b a -> SMT b a
liftSMT act = SMT (lift act)

embedSMT :: Backend b => (b -> SMTMonad b (a,b)) -> SMT b a
embedSMT act = SMT $ do
  b <- get
  (res,nb) <- lift $ act (backend b)
  put (b { backend = nb })
  return res

embedSMT' :: Backend b => (b -> SMTMonad b b) -> SMT b ()
embedSMT' act = SMT $ do
  b <- get
  nb <- lift $ act (backend b)
  put (b { backend = nb })

data DTProxy dt where
  DTProxy :: IsDatatype dt => DTProxy dt

instance GEq DTProxy where
  geq DTProxy DTProxy = eqT

instance GCompare DTProxy where
  gcompare x@(DTProxy::DTProxy a) y@(DTProxy::DTProxy b) = case (eqT :: Maybe (a :~: b)) of
    Just Refl -> GEQ
    Nothing -> case compare (typeRep x) (typeRep y) of
      LT -> GLT
      GT -> GGT

instance GShow DTProxy where
  gshowsPrec p pr@DTProxy = showsPrec p (typeRep pr)

instance Show (DTProxy dt) where
  showsPrec = gshowsPrec

type DatatypeInfo con field = DMap DTProxy (RegisteredDT con field)

newtype RegisteredDT con field dt
  = RegisteredDT (B.BackendDatatype con field '(DatatypeSig dt,dt))
  deriving (Typeable)

emptyDatatypeInfo :: DatatypeInfo con field
emptyDatatypeInfo = Map.empty

reproxyDT :: IsDatatype dt => Proxy dt -> DTProxy dt
reproxyDT _ = DTProxy

registerDatatype :: (Backend b,IsDatatype dt) => Proxy dt -> SMT b ()
registerDatatype pr = do
  st <- get
  if Map.member (reproxyDT pr) (datatypes st)
    then return ()
    else do
      (dts,nb) <- liftSMT $ B.declareDatatypes (getTypeCollection pr) (backend st)
      put $ st { backend = nb
               , datatypes = insertTypes dts (datatypes st) }
  where
    insertTypes :: B.BackendTypeCollection con field sigs -> DatatypeInfo con field -> DatatypeInfo con field
    insertTypes NoDts mp = mp
    insertTypes (ConsDts (dt::B.BackendDatatype con field '(DatatypeSig dt,dt)) dts) mp
      = let nmp =  Map.insert (DTProxy::DTProxy dt) (RegisteredDT dt) mp
         in insertTypes dts nmp

lookupDatatype :: DTProxy dt -> DatatypeInfo con field
               -> B.BackendDatatype con field '(DatatypeSig dt,dt)
lookupDatatype pr dts = case Map.lookup pr dts of
  Just (RegisteredDT dt) -> dt
  Nothing -> error $ "smtlib2: Datatype "++show pr++" is not registered."

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

constructDatatype :: GEq con => con '(arg,ret)
                  -> Args ConcreteValue arg
                  -> B.BackendDatatype con field '(cons,ret)
                  -> ret
constructDatatype con args dt = get con args (bconstructors dt)
  where
    get :: GEq con => con '(arg,ret) -> Args ConcreteValue arg
        -> Constrs (BackendConstr con field) sigs ret -> ret
    get con args (ConsCon x xs)
      = case geq con (bconRepr x) of
      Just Refl -> bconstruct x args
      Nothing -> get con args xs

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
                  => DTProxy dt -> String -> DatatypeInfo con field
                  -> (forall arg. GetTypes arg => B.BackendConstr con field '(arg,dt) -> a)
                  -> a
lookupDatatypeCon pr name info f
  = lookupConstructor name (lookupDatatype pr info) f

lookupDatatypeField :: (IsDatatype dt,Typeable con,Typeable field)
                  => DTProxy dt -> String -> String -> DatatypeInfo con field
                  -> (forall tp. GetType tp => B.BackendField field dt tp -> a)
                  -> a
lookupDatatypeField pr con field info f
  = lookupDatatypeCon pr con info $
    \con' -> lookupField field con' f

mkConcr :: B.Backend b => Value (B.Constr b) t -> SMT b (ConcreteValue t)
mkConcr (BoolValue v) = return (BoolValueC v)
mkConcr (IntValue v) = return (IntValueC v)
mkConcr (RealValue v) = return (RealValueC v)
mkConcr (BitVecValue v) = return (BitVecValueC v)
mkConcr (ConstrValue con args) = do
  args' <- mapArgs mkConcr args
  st <- get
  return $ ConstrValueC $
    constructDatatype con args' $
    lookupDatatype DTProxy (datatypes st)

mkAbstr :: (B.Backend b,GetType t) => ConcreteValue t -> SMT b (Value (B.Constr b) t)
mkAbstr (BoolValueC v) = return (BoolValue v)
mkAbstr (IntValueC v) = return (IntValue v)
mkAbstr (RealValueC v) = return (RealValue v)
mkAbstr (BitVecValueC v) = return (BitVecValue v)
mkAbstr (ConstrValueC v) = do
  st <- get
  getConstructor v (bconstructors $ lookupDatatype DTProxy (datatypes st)) $
    \con args -> do
      rargs <- mapArgs mkAbstr args
      return $ ConstrValue (bconRepr con) rargs
