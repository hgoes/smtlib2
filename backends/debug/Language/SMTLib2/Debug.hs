{-# LANGUAGE PolyKinds,DataKinds,ScopedTypeVariables #-}
module Language.SMTLib2.Debug where

import Language.SMTLib2.Internals.Backend
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Pipe

import qualified Data.AttoLisp as L
import System.Console.ANSI
import System.IO
import Control.Monad.Trans
import Control.Monad (when)
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Proxy
import Data.Typeable
import qualified Data.Text as T

import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

debugBackend :: (Backend b,MonadIO (SMTMonad b)) => b -> DebugBackend b
debugBackend b = DebugBackend b stderr (Just 0) Nothing True
                 Map.empty DMap.empty --DMap.empty

namedDebugBackend :: (Backend b,MonadIO (SMTMonad b)) => String -> b -> DebugBackend b
namedDebugBackend name b = DebugBackend b stderr (Just 0) (Just name) True
                           Map.empty DMap.empty --DMap.empty

type family Fst (a :: (p,q)) :: p where
  Fst '(x,y) = x

type family Snd (a :: (p,q)) :: q where
  Snd '(x,y) = y

newtype Fun' b x = Fun' (Fun b (Fst x) (Snd x))

data Untyped v (a :: k) = Untyped v

data DebugBackend (b :: *)
  = (Backend b,MonadIO (SMTMonad b))
    => DebugBackend { debugBackend' :: b
                    , debugHandle :: Handle
                    , debugLines :: Maybe Integer
                    , debugPrefix :: Maybe String
                    , debugUseColor :: Bool
                    , debugNames :: Map String Int
                    , debugVars :: DMap (Var b :: Type -> *) (UntypedVar T.Text :: Type -> *)
--                    , debugFuns :: DMap (Fun' b) (Untyped T.Text)
                    }

outputLisp :: DebugBackend (b:: *) -> L.Lisp -> SMTMonad b (DebugBackend b)
outputLisp b lsp
  = outputLines b False (lines $ show lsp)

outputLines :: DebugBackend b -> Bool -> [String]
            -> SMTMonad b (DebugBackend b)
outputLines b@(DebugBackend {}) isComment
  = foldlM (\b' line -> outputLine b' isComment line) b

outputLine :: DebugBackend b -> Bool -> String
           -> SMTMonad b (DebugBackend b)
outputLine b@(DebugBackend {}) isComment str = do
  case debugPrefix b of
    Nothing -> return ()
    Just prf -> do
      when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Cyan]
      liftIO $ hPutStr (debugHandle b) prf
  nline <- case debugLines b of
             Nothing -> return Nothing
             Just line -> do
               when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Red]
               let line_str = show line
                   line_str_len = length line_str
                   line_str' = replicate (4-line_str_len) ' '++line_str++" "
               liftIO $ hPutStr (debugHandle b) line_str'
               return (Just (line+1))
  if isComment
    then do
      when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull White]
      liftIO $ hPutStr (debugHandle b) $ ';':' ':str
    else do
      when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Green]
      liftIO $ hPutStrLn (debugHandle b) str
  when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset]
  return $ b { debugLines = nline }

outputResponse :: DebugBackend b -> String -> SMTMonad b ()
outputResponse b@(DebugBackend {}) str = do
  when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset,SetColor Foreground Dull Blue]
  liftIO $ hPutStrLn (debugHandle b) str
  when (debugUseColor b) $ liftIO $ hSetSGR (debugHandle b) [Reset]

instance (Backend b) => Backend (DebugBackend b) where
  type SMTMonad (DebugBackend b) = SMTMonad b
  type Expr (DebugBackend b) = Expr b
  type Var (DebugBackend b) = Var b
  type QVar (DebugBackend b) = QVar b
  type Fun (DebugBackend b) = Fun b
  type Constr (DebugBackend b) = Constr b
  type Field (DebugBackend b) = Field b
  type FunArg (DebugBackend b) = FunArg b
  type ClauseId (DebugBackend b) = ClauseId b
  setOption b opt = do
    b1 <- outputLisp b (renderSetOption opt)
    nb <- setOption (debugBackend' b1) opt
    return (b1 { debugBackend' = nb })
  declareVar b name = with $ \(pr::Proxy t) -> do
    let (sym,req,nnames) = renderDeclareVar (debugNames b) pr name
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 req
    (rvar,nb) <- declareVar (debugBackend' b2) name
    return (rvar,b2 { debugBackend' = nb
                    , debugVars = DMap.insertWith const (rvar::Var b t)
                                              (UntypedVar sym::UntypedVar T.Text t) (debugVars b2) })
    where
      with :: (Proxy (t::Type) -> SMTMonad b (Var (DebugBackend b) t,DebugBackend b))
           -> SMTMonad b (Var (DebugBackend b) t,DebugBackend b)
      with f = f Proxy
  toBackend b expr = do
    (expr',nb) <- toBackend (debugBackend' b) expr
    return (expr',b { debugBackend' = nb })
  assert b expr = do
    (l,b1) <- renderExpr b expr
    b2 <- outputLisp b1 (L.List [L.Symbol "assert",l])
    nb <- assert (debugBackend' b2) expr
    return (b2 { debugBackend' = nb })
  checkSat b tactic limits = do
    b1 <- outputLisp b (renderCheckSat tactic limits)
    (res,nb) <- checkSat (debugBackend' b) tactic limits
    outputResponse b1 $ case res of
      Sat -> "sat"
      Unsat -> "unsat"
      Unknown -> "unknown"
    return (res,b1 { debugBackend' = nb })
  getValue b expr = do
    (l,b1) <- renderExpr b expr
    b2 <- outputLisp b1 (L.List [L.Symbol "get-value"
                                ,L.List [l]])
    (res,nb) <- getValue (debugBackend' b2) expr
    outputResponse b2 (show $ valueToLisp res)
    return (res,b2 { debugBackend' = nb })
  {-declareFun b name = with $ \parg pr -> do
    let (sym,req,nnames) = renderDeclareFun (debugNames b) parg pr name
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 req
    (rvar,nb) <- declareFun (debugBackend' b2) name
    return (rvar,b2 { debugBackend' = nb
                    , debugFuns = DMap.insert rvar (UntypedFun sym) (debugFuns b2) })
        
    where
      with :: (Proxy arg -> Proxy t -> SMTMonad b (Fun b arg t,DebugBackend b))
           -> SMTMonad b (Fun b arg t,DebugBackend b)
      with f = f Proxy Proxy-}

renderExpr :: (Backend b,GetType tp) => DebugBackend b -> Expr b tp
           -> SMTMonad b (L.Lisp,DebugBackend b)
renderExpr b expr = do
  (e',nb) <- fromBackend (debugBackend' b) expr
  -- TODO: To be correct, this must be a state monad
  l <- exprToLispWith (\v -> case DMap.lookup v (debugVars b) of
                               Just (UntypedVar r) -> return $ L.Symbol r)
         undefined undefined undefined undefined undefined undefined
         (fmap fst . renderExpr b) e'
  return (l,b { debugBackend' = nb })

{-
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
-}
