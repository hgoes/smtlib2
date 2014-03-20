module Language.SMTLib2.Debug where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe

import System.Console.ANSI
import System.IO
import Control.Monad.Trans

debugBackend :: b -> DebugBackend b
debugBackend b = DebugBackend b stderr

data DebugBackend b = DebugBackend { debugBackend' :: b
                                   , debugHandle :: Handle
                                   }

instance (SMTBackend b m,MonadIO m) => SMTBackend (DebugBackend b) m where
  smtHandle b st req = do
    liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Green]
    case renderSMTRequest st req of
      Left l -> liftIO $ hPutStrLn (debugHandle b) (show l)
      Right msg -> liftIO $ hPutStr (debugHandle b) $ unlines $ fmap (\xs -> ';':xs) (lines msg)
    resp <- smtHandle (debugBackend' b) st req
    case renderSMTResponse st req resp of
      Nothing -> return ()
      Just str -> do
        liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Blue]
        liftIO $ hPutStrLn (debugHandle b) str
    liftIO $ hSetSGR (debugHandle b) [Reset]
    return resp
