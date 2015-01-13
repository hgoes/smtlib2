module Language.SMTLib2.Debug where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Pipe

import System.Console.ANSI
import System.IO
import Control.Monad.Trans
import Control.Monad (when)

debugBackend :: b -> DebugBackend b
debugBackend b = DebugBackend b stderr (Just 0) Nothing True

namedDebugBackend :: String -> b -> DebugBackend b
namedDebugBackend name b = DebugBackend b stderr (Just 0) (Just name) True

data DebugBackend b = DebugBackend { debugBackend' :: b
                                   , debugHandle :: Handle
                                   , debugLines :: Maybe Integer
                                   , debugPrefix :: Maybe String
                                   , debugUseColor :: Bool
                                   }

instance (SMTBackend b m,MonadIO m) => SMTBackend (DebugBackend b) m where
  smtGetNames b = smtGetNames (debugBackend' b)
  smtNextName b = smtNextName (debugBackend' b)
  smtHandle b req = do
    getName <- smtGetNames (debugBackend' b)
    nxtName <- smtNextName (debugBackend' b)
    (dts,b1) <- smtHandle (debugBackend' b) SMTDeclaredDataTypes
    let rendering = renderSMTRequest nxtName getName dts req
    case debugPrefix b of
      Nothing -> return ()
      Just prf -> case rendering of
        Right "" -> return ()
        _ -> do
          when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Cyan]
          liftIO $ hPutStr (debugHandle b) prf
    nline <- case rendering of
     Right "" -> return (debugLines b)
     _ -> do
       nline <- case debugLines b of
         Nothing -> return Nothing
         Just line -> do
           when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Red]
           let line_str = show line
               line_str_len = length line_str
               line_str' = replicate (4-line_str_len) ' '++line_str++" "
           liftIO $ hPutStr (debugHandle b) line_str'
           return (Just (line+1))
       case rendering of
        Left l -> do
          when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Green]
          liftIO $ hPutStrLn (debugHandle b) (show l)
        Right msg -> do
          when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull White]
          liftIO $ hPutStr (debugHandle b) $ unlines $ fmap (\xs -> ';':xs) (lines msg)
       return nline
    (resp,b2) <- smtHandle b1 req
    case renderSMTResponse getName dts req resp of
      Nothing -> return ()
      Just str -> do
        when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Blue]
        liftIO $ hPutStrLn (debugHandle b) str
    when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset]
    return (resp,b { debugBackend' = b2
                   , debugLines = nline })
