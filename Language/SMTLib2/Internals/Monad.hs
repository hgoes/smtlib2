module Language.SMTLib2.Internals.Monad where

import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type

import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Typeable

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

liftSMT :: Backend b => SMTMonad b a -> SMT b a
liftSMT act = SMT (lift act)

type DatatypeInfo con field = Map TypeRep (RegisteredDT con field)

data RegisteredDT con field
  = forall dt. IsDatatype dt => RegisteredDT (B.BackendDatatype con field '(DatatypeSig dt,dt))
  deriving (Typeable)

emptyDatatypeInfo :: DatatypeInfo con field
emptyDatatypeInfo = Map.empty

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
