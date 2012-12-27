module Language.SMTLib2.Internals.Connection where

import Language.SMTLib2.Internals.SMTMonad
import System.IO
import System.Process
import Control.Concurrent.MVar
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.State (runStateT)
import Control.Monad.Reader (runReaderT)

data SMTConnection = SMTConnection { input :: Handle
                                   , output :: Handle
                                   , handle :: ProcessHandle
                                   , status :: MVar SMTState
                                   }

open :: String -> IO SMTConnection
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
  st <- newMVar (0,Set.empty,Map.empty)
  return (SMTConnection { input = hin
                        , output = hout
                        , handle = hand
                        , status = st
                        })

close :: SMTConnection -> IO ()
close conn = do
  hClose (input conn)
  hClose (output conn)
  terminateProcess (handle conn)
  _ <- waitForProcess (handle conn)
  return ()

performSMT :: SMTConnection -> SMT a -> IO a
performSMT conn act = modifyMVar (status conn) (fmap (\(x,y) -> (y,x)) . runStateT (runReaderT (runSMT act) (input conn,output conn)))