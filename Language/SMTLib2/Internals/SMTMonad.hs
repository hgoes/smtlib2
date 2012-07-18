module Language.SMTLib2.Internals.SMTMonad where

import System.IO (Handle)

import Data.Map (Map)
import Data.Text as T (Text)
import Data.Typeable (TypeRep)

import Data.Monoid (Monoid)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Cont (ContT)
import Control.Monad.Error (ErrorT, Error)
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.List (ListT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State.Lazy as Lazy (StateT)
import Control.Monad.State.Strict as Strict (StateT)
import Control.Monad.Writer.Lazy as Lazy (WriterT)
import Control.Monad.Writer.Strict as Strict (WriterT)

-- | The SMT monad used for communating with the SMT solver
type SMT = ReaderT (Handle,Handle) (Lazy.StateT (Integer,[TypeRep],Map T.Text TypeRep) IO)

-- | Lift an SMT action into an arbitrary monad (like liftIO).
class Monad m => MonadSMT m where
  liftSMT :: SMT a -> m a

instance MonadSMT m => MonadSMT (ContT r m) where
  liftSMT = lift . liftSMT

instance (Error e, MonadSMT m) => MonadSMT (ErrorT e m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (IdentityT m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (ListT m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (MaybeT m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (ReaderT r m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (Lazy.StateT s m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (Strict.StateT s m) where
  liftSMT = lift . liftSMT

instance (Monoid w, MonadSMT m) => MonadSMT (Lazy.WriterT w m) where
  liftSMT = lift . liftSMT

instance (Monoid w, MonadSMT m) => MonadSMT (Strict.WriterT w m) where
  liftSMT = lift . liftSMT
