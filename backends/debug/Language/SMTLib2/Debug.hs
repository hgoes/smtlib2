module Language.SMTLib2.Debug where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe

import System.Console.ANSI
import System.IO
import Control.Monad.Trans
import Data.IORef

debugBackend :: b -> IO (DebugBackend b)
debugBackend b = do
  ref <- newIORef 0
  return $ DebugBackend b stderr (Just ref)

data DebugBackend b = DebugBackend { debugBackend' :: b
                                   , debugHandle :: Handle
                                   , debugLines :: Maybe (IORef Integer)
                                   }

instance (SMTBackend b m,MonadIO m) => SMTBackend (DebugBackend b) m where
  smtHandle b st req = do
    case debugLines b of
      Nothing -> return ()
      Just line_ref -> do
        cur_line <- liftIO $ atomicModifyIORef line_ref
                    (\cl -> (cl+1,cl))
        liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Red]
        let line_str = show cur_line
            line_str_len = length line_str
            line_str' = replicate (4-line_str_len) ' '++line_str++" "
        liftIO $ hPutStr (debugHandle b) line_str'
    case renderSMTRequest st req of
      Left l -> do
        liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Green]
        liftIO $ hPutStrLn (debugHandle b) (show l)
      Right msg -> do
        liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull White]
        liftIO $ hPutStr (debugHandle b) $ unlines $ fmap (\xs -> ';':xs) (lines msg)
    resp <- smtHandle (debugBackend' b) st req
    case renderSMTResponse st req resp of
      Nothing -> return ()
      Just str -> do
        liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Blue]
        liftIO $ hPutStrLn (debugHandle b) str
    liftIO $ hSetSGR (debugHandle b) [Reset]
    return resp
