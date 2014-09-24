{- | This module can be used if the simple 'Language.SMTLib2.withSMTSolver'-interface isn't
     sufficient, e.g. if you don't want to wrap your whole program into one big
     'Language.SMTLib2.MonadSMT' or you want to run multiple solvers side by side. -}
module Language.SMTLib2.Connection
       (SMTConnection()
       ,open
       ,close
       ,performSMT
       ,performSMTExitCleanly
       ) where

import Language.SMTLib2.Internals
import Control.Concurrent.MVar
import Control.Monad.State (runStateT)
import Control.Monad.Reader (runReaderT)
import Control.Monad.Trans (MonadIO,liftIO)
import Control.Exception
import Prelude (($),IO,return)

-- | Represents a connection to an SMT solver.
--   The SMT solver runs in a seperate thread and communication is handled via handles.
data SMTConnection b = SMTConnection { backend :: b
                                     , status :: MVar SMTState
                                     }

-- | Create a new connection to a SMT solver by spawning a shell command.
--   The solver must be able to read from stdin and write to stdout.
open :: (MonadIO m,SMTBackend b m) => b -- ^ The backend for the SMT solver.
        -> m (SMTConnection b)
open solver = do
  st <- liftIO $ newMVar emptySMTState
  return (SMTConnection { backend = solver
                        , status = st
                        })

-- | Closes an open SMT connection. Do not use the connection afterwards.
close :: (MonadIO m,SMTBackend b m) => SMTConnection b -> m ()
close conn = do
  st <- liftIO $ takeMVar (status conn)
  smtHandle (backend conn) st SMTExit
  return ()

-- | Perform an action in the SMT solver associated with this connection and return the result.
performSMT :: (MonadIO m,SMTBackend b m)
              => SMTConnection b -- ^ The connection to the SMT solver to use
              -> SMT' m a -- ^ The action to perform
              -> m a
performSMT conn act = do
  st <- liftIO $ takeMVar (status conn)
  (res,nst) <- runStateT (runReaderT (runSMT act) (AnyBackend $ backend conn)) st
  liftIO $ putMVar (status conn) nst
  return res

performSMTExitCleanly :: SMTBackend b IO
                         => SMTConnection b
                         -> SMT' IO a
                         -> IO a
performSMTExitCleanly conn act = do
  st <- takeMVar (status conn)
  catch (do
            (res,nst) <- runStateT (runReaderT (runSMT act) (AnyBackend $ backend conn)) st
            putMVar (status conn) nst
            return res)
    (\e -> do
        smtHandle (backend conn) st SMTExit
        throw (e :: SomeException))
