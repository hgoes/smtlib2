module Language.SMTLib2.Debug where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe

import System.Console.ANSI
import System.IO
import Control.Monad.Trans
import Control.Monad (when)
import Data.IORef

debugBackend :: b -> IO (DebugBackend b)
debugBackend b = do
  ref <- newIORef 0
  return $ DebugBackend b stderr (Just ref) Nothing True

namedDebugBackend :: String -> b -> IO (DebugBackend b)
namedDebugBackend name b = do 
  ref <- newIORef 0
  return $ DebugBackend b stderr (Just ref) (Just name) True

data DebugBackend b = DebugBackend { debugBackend' :: b
                                   , debugHandle :: Handle
                                   , debugLines :: Maybe (IORef Integer)
                                   , debugPrefix :: Maybe String
                                   , debugUseColor :: Bool
                                   }

instance (SMTBackend b m,MonadIO m) => SMTBackend (DebugBackend b) m where
  smtHandle b st req = do
    case debugPrefix b of
      Nothing -> return ()
      Just prf -> do
        when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Cyan]
        liftIO $ hPutStr (debugHandle b) prf
    case debugLines b of
      Nothing -> return ()
      Just line_ref -> do
        cur_line <- liftIO $ atomicModifyIORef line_ref
                    (\cl -> (cl+1,cl))
        when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Red]
        let line_str = show cur_line
            line_str_len = length line_str
            line_str' = replicate (4-line_str_len) ' '++line_str++" "
        liftIO $ hPutStr (debugHandle b) line_str'
    case renderSMTRequest st req of
      Left l -> do
        when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Green]
        liftIO $ hPutStrLn (debugHandle b) (show l)
      Right msg -> do
        when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull White]
        liftIO $ hPutStr (debugHandle b) $ unlines $ fmap (\xs -> ';':xs) (lines msg)
    resp <- smtHandle (debugBackend' b) st req
    case renderSMTResponse st req resp of
      Nothing -> return ()
      Just str -> do
        when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Blue]
        liftIO $ hPutStrLn (debugHandle b) str
    when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset]
    return resp
