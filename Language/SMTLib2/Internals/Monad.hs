module Language.SMTLib2.Internals.Monad where

import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type

import Control.Monad.State.Strict
import Data.Typeable
import Control.Exception (onException)
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (foldlM)

-- | The SMT monad is used to perform communication with the SMT solver. The
--   type of solver is given by the /b/ parameter.
newtype SMT b a = SMT { runSMT :: StateT (SMTState b) (SMTMonad b) a }

data SMTState b = SMTState { backend :: !b
                           , datatypes :: !(Set String) }

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

-- | Execute an SMT action on a given backend.
withBackend :: Backend b => SMTMonad b b -- ^ An action that creates a fresh backend.
            -> SMT b a                   -- ^ The SMT action to perform.
            -> SMTMonad b a
withBackend constr act = do
  b <- constr
  (res,nb) <- runStateT (runSMT act) (SMTState b Set.empty)
  exit (backend nb)
  return res

-- | Like `withBackend` but specialized to the 'IO' monad so exeptions can be
--   handled by gracefully exiting the solver.
withBackendExitCleanly :: (Backend b,SMTMonad b ~ IO) => IO b -> SMT b a -> IO a
withBackendExitCleanly constr (SMT act) = do
  b <- constr
  (do
      (res,nb) <- runStateT act (SMTState b Set.empty)
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

registerDatatype :: (Backend b,IsDatatype dt) => Proxy dt -> SMT b ()
registerDatatype pr = do
  st <- get
  if Set.member (datatypeName pr) (datatypes st)
    then return ()
    else do
      let (ndts,deps) = dependencies (datatypes st) pr
      nb <- foldlM (\b dts -> do
                       ((),nb) <- liftSMT $ B.declareDatatypes dts b
                       return nb
                   ) (backend st) deps
      put $ st { backend = nb
               , datatypes = ndts }

defineVar' :: (B.Backend b) => B.Expr b t -> SMT b (B.Var b t)
defineVar' e = embedSMT $ B.defineVar Nothing e

defineVarNamed' :: (B.Backend b) => String -> B.Expr b t -> SMT b (B.Var b t)
defineVarNamed' name e = embedSMT $ B.defineVar (Just name) e

declareVar' :: B.Backend b => Repr t -> SMT b (B.Var b t)
declareVar' tp = embedSMT $ B.declareVar tp Nothing

declareVarNamed' :: B.Backend b => Repr t -> String -> SMT b (B.Var b t)
declareVarNamed' tp name = embedSMT $ B.declareVar tp (Just name)
