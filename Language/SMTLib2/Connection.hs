{- | This module can be used if the simple 'Language.SMTLib2.withSMTSolver'-interface isn't
     sufficient, e.g. if you don't want to wrap your whole program into one big
     'Language.SMTLib2.MonadSMT' or you want to run multiple solvers side by side. -}
module Language.SMTLib2.Connection
       (SMTConnection()
       ,open
       ,close
       ,performSMT
       ) where

import Language.SMTLib2.Internals
import System.IO
import System.Process
import Control.Concurrent.MVar
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.State (runStateT)
import Control.Monad.Reader (runReaderT)

-- | Represents a connection to an SMT solver.
--   The SMT solver runs in a seperate thread and communication is handled via handles.
data SMTConnection = SMTConnection { input :: Handle
                                   , output :: Handle
                                   , handle :: ProcessHandle
                                   , status :: MVar SMTState
                                   }

-- | Create a new connection to a SMT solver by spawning a shell command.
--   The solver must be able to read from stdin and write to stdout.
open :: String -- ^ The shell command to start the SMT solver.
        -> IO SMTConnection
open solver = do
  let cmd = CreateProcess { cmdspec = ShellCommand solver
                          , cwd = Nothing
                          , env = Nothing
                          , std_in = CreatePipe
                          , std_out = CreatePipe
                          , std_err = Inherit
                          , close_fds = False
                          , create_group = False
                          }
  (Just hin,Just hout,_,hand) <- createProcess cmd
  st <- newMVar (Map.empty,Map.empty,Map.empty)
  return (SMTConnection { input = hin
                        , output = hout
                        , handle = hand
                        , status = st
                        })

-- | Closes an open SMT connection. Do not use the connection afterwards.
close :: SMTConnection -> IO ()
close conn = do
  hClose (input conn)
  hClose (output conn)
  terminateProcess (handle conn)
  _ <- waitForProcess (handle conn)
  return ()

-- | Perform an action in the SMT solver associated with this connection and return the result.
performSMT :: SMTConnection -- ^ The connection to the SMT solver to use
              -> SMT a -- ^ The action to perform
              -> IO a
performSMT conn act = modifyMVar (status conn) (fmap (\(x,y) -> (y,x)) . runStateT (runReaderT (runSMT act) (input conn,output conn)))