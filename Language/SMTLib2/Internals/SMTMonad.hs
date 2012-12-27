module Language.SMTLib2.Internals.SMTMonad (
  SMT(..), askSMT, getSMT, putSMT, modifySMT, MonadSMT(..), SMTState
  ) where

import System.IO (Handle)

import Data.Map (Map)
import Data.Set (Set)
import Data.Text as T (Text)
import Data.Typeable (TypeRep,TyCon)
import Data.Monoid (Monoid)

import Control.Monad.Trans.Class (lift)
import Control.Monad.IO.Class
import Control.Monad.Cont (ContT)
import Control.Monad.Error (ErrorT, Error)
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.List (ListT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Reader (ReaderT, MonadReader(..))
import Control.Monad.State (MonadState(..), modify)
import Control.Monad.State.Lazy as Lazy (StateT)
import Control.Monad.State.Strict as Strict (StateT)
import Control.Monad.Writer.Lazy as Lazy (WriterT)
import Control.Monad.Writer.Strict as Strict (WriterT)
import Control.Monad.Fix (MonadFix(..))
import Control.Applicative (Applicative(..))
import Control.Monad (ap)

type SMTRead = (Handle, Handle)
type SMTState = (Integer,Set TyCon,Map T.Text TypeRep)

-- | The SMT monad used for communating with the SMT solver
newtype SMT a = SMT { runSMT :: ReaderT SMTRead (Lazy.StateT SMTState IO) a }

instance Functor SMT where
  fmap f = SMT . fmap f . runSMT

instance Monad SMT where
  return = SMT . return
  m >>= f = SMT $ (runSMT m) >>= runSMT . f

instance MonadIO SMT where
  liftIO = SMT . liftIO

instance MonadFix SMT where
  mfix f = SMT $ mfix (runSMT . f)

instance Applicative SMT where
  pure = return
  (<*>) = ap

askSMT :: SMT SMTRead
askSMT = SMT ask

getSMT :: SMT SMTState
getSMT = SMT get

putSMT :: SMTState -> SMT ()
putSMT = SMT . put

modifySMT :: (SMTState -> SMTState) -> SMT ()
modifySMT f = SMT $ modify f

-- | Lift an SMT action into an arbitrary monad (like liftIO).
class Monad m => MonadSMT m where
  liftSMT :: SMT a -> m a

instance MonadSMT SMT where
  liftSMT = id

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
