{-# LANGUAGE PolyKinds,DataKinds,ScopedTypeVariables #-}
module Language.SMTLib2.Debug
       (DebugBackend(),
        debugBackend,
        namedDebugBackend) where

import Language.SMTLib2.Internals.Backend
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Expression (Expression(Let),LetBinding(..))
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
import qualified Data.Text as T
import Data.Functor.Identity
import Data.Typeable

import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

debugBackend :: (Backend b,MonadIO (SMTMonad b)) => b -> DebugBackend b
debugBackend b = DebugBackend b stderr (Just 0) Nothing True
                 Map.empty DMap.empty DMap.empty DMap.empty
                 DMap.empty DMap.empty DMap.empty DMap.empty
                 Map.empty

namedDebugBackend :: (Backend b,MonadIO (SMTMonad b)) => String -> b -> DebugBackend b
namedDebugBackend name b = DebugBackend b stderr (Just 0) (Just name) True
                           Map.empty DMap.empty DMap.empty DMap.empty
                           DMap.empty DMap.empty DMap.empty DMap.empty
                           Map.empty

data DebugBackend (b :: *)
  = (Backend b,MonadIO (SMTMonad b))
    => DebugBackend { debugBackend' :: b
                    , debugHandle :: Handle
                    , debugLines :: Maybe Integer
                    , debugPrefix :: Maybe String
                    , debugUseColor :: Bool
                    , debugNames :: Map String Int
                    , debugVars :: DMap (Var b) (UntypedVar T.Text)
                    , debugQVars :: DMap (QVar b) (UntypedVar T.Text)
                    , debugFuns :: DMap (Fun b) (UntypedFun T.Text)
                    , debugCons :: DMap (Constr b) (UntypedCon T.Text)
                    , debugFields :: DMap (Field b) (UntypedField T.Text)
                    , debugFVars :: DMap (FunArg b) (UntypedVar T.Text)
                    , debugLVars :: DMap (LVar b) (UntypedVar T.Text)
                    , debugCIds :: Map (ClauseId b) T.Text
                    }
  deriving Typeable

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
      liftIO $ hPutStrLn (debugHandle b) $ ';':' ':str
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
  type LVar (DebugBackend b) = LVar b
  type ClauseId (DebugBackend b) = ClauseId b
  type Model (DebugBackend b) = Model b
  setOption opt b = do
    b1 <- outputLisp b (renderSetOption opt)
    ((),nb) <- setOption opt (debugBackend' b1)
    return ((),b1 { debugBackend' = nb })
  getInfo info b = do
    b1 <- outputLisp b (renderGetInfo info)
    (res,nb) <- getInfo info (debugBackend' b1)
    outputResponse b1 (case info of
                        SMTSolverName -> res
                        SMTSolverVersion -> res)
    return (res,b1 { debugBackend' = nb })
  declareVar tp name b = do
    let (sym,req,nnames) = renderDeclareVar (debugNames b) tp name
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 req
    (rvar,nb) <- declareVar tp name (debugBackend' b2)
    return (rvar,b2 { debugBackend' = nb
                    , debugVars = DMap.insertWith const rvar
                                  (UntypedVar sym tp) (debugVars b2) })
  defineFun name args body b = do
    let (sym,req,nnames) = renderDefineFun
                           (\fv -> case DMap.lookup fv (debugFVars b) of
                             Just (UntypedVar n _) -> L.Symbol n)
                           (renderExpr b)
                           (debugNames b) name args body
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 req
    (rvar,nb) <- defineFun name args body (debugBackend' b2)
    let (argtp,rtp) = getFunType rvar
    return (rvar,b2 { debugBackend' = nb
                    , debugFuns = DMap.insertWith const rvar
                                  (UntypedFun sym argtp rtp) (debugFuns b2) }) 
  createFunArg tp name b = do
    let name' = case name of
          Just n -> n
          Nothing -> "fv"
        (name'',nnames) = genName' (debugNames b) name'
    (fv,nb) <- createFunArg tp name (debugBackend' b)
    return (fv,b { debugBackend' = nb
                 , debugNames = nnames
                 , debugFVars = DMap.insert fv (UntypedVar name'' tp) (debugFVars b) })
  toBackend expr b = do
    (expr',nb) <- toBackend expr (debugBackend' b)
    return (expr',b { debugBackend' = nb })
  fromBackend b = fromBackend (debugBackend' b)
  assert expr b = do
    let l = renderExpr b expr
    b1 <- outputLisp b (L.List [L.Symbol "assert",l])
    ((),nb) <- assert expr (debugBackend' b1)
    return ((),b1 { debugBackend' = nb })
  assertPartition expr part b = do
    let l = renderExpr b expr
    b1 <- outputLisp b (L.List [L.Symbol "assert"
                               ,L.List [L.Symbol "!"
                                  ,l
                                  ,L.Symbol ":interpolation-group"
                                  ,L.Symbol (case part of
                                               PartitionA -> "partA"
                                               PartitionB -> "partB")]])
    ((),nb) <- assertPartition expr part (debugBackend' b1)
    return ((),b1 { debugBackend' = nb })
  assertId expr b = do
    let l = renderExpr b expr
        (name,nnames) = genName' (debugNames b) "cid"
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 (L.List [L.Symbol "assert"
                                ,L.List [L.Symbol "!",l
                                        ,L.Symbol ":named"
                                        ,L.Symbol name]])
    (cid,nb) <- assertId expr (debugBackend' b2)
    return (cid,b2 { debugBackend' = nb
                   , debugCIds = Map.insert cid name (debugCIds b2) })
  interpolate b = do
    b1 <- outputLisp b (L.List [L.Symbol "get-interpolant",L.List [L.Symbol "partA"]])
    (res,nb) <- interpolate (debugBackend' b)
    outputResponse b1 (show $ renderExpr b1 res)
    return (res,b1 { debugBackend' = nb })
  checkSat tactic limits b = do
    b1 <- outputLisp b (renderCheckSat tactic limits)
    (res,nb) <- checkSat tactic limits (debugBackend' b)
    outputResponse b1 $ case res of
      Sat -> "sat"
      Unsat -> "unsat"
      Unknown -> "unknown"
    return (res,b1 { debugBackend' = nb })
  getValue expr b = do
    let l = renderExpr b expr
    b1 <- outputLisp b (L.List [L.Symbol "get-value"
                               ,L.List [l]])
    (res,nb) <- getValue expr (debugBackend' b1)
    str <- valueToLisp (\con -> case DMap.lookup con (debugCons b1) of
                                  Just (UntypedCon name _ _) -> return (L.Symbol name)
                       ) res
    outputResponse b1 (show str)
    return (res,b1 { debugBackend' = nb })
  declareFun argtp rtp name b = do
    let (sym,req,nnames) = renderDeclareFun (debugNames b) argtp rtp name
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 req
    (rvar,nb) <- declareFun argtp rtp name (debugBackend' b2)
    return (rvar,b2 { debugBackend' = nb
                    , debugFuns = DMap.insert rvar (UntypedFun sym argtp rtp) (debugFuns b2) })
  declareDatatypes coll b = do
    b1 <- outputLisp b (renderDeclareDatatype coll)
    (res,nb) <- declareDatatypes coll (debugBackend' b1)
    return (res,getVars res (b1 { debugBackend' = nb }))
    where
      getVars :: Datatypes (BackendDatatype (Constr b) (Field b)) sigs
              -> DebugBackend b
              -> DebugBackend b
      getVars NoDts b = b
      getVars (ConsDts dt dts) b = getVars dts (getConsVars (bconstructors dt) b)

      getConsVars :: IsDatatype dt
                  => Constrs (BackendConstr (Constr b) (Field b)) sigs dt
                  -> DebugBackend b
                  -> DebugBackend b
      getConsVars NoCon b = b
      getConsVars (ConsCon con cons) b
        = getConsVars cons $
          getFieldVars (bconFields con) $
          b { debugCons = DMap.insert (bconRepr con)
                                      (UntypedCon (T.pack $ bconName con)
                                       (runIdentity $ List.mapM (return . bfieldType) (bconFields con))
                                       Proxy)
                                      (debugCons b) }

      getFieldVars :: IsDatatype dt
                   => List (BackendField (Field b) dt) sig
                   -> DebugBackend b
                   -> DebugBackend b
      getFieldVars Nil b = b
      getFieldVars (f ::: fs) b
        = getFieldVars fs $
          b { debugFields = DMap.insert (bfieldRepr f)
                                        (UntypedField (T.pack $ bfieldName f)
                                         Proxy (bfieldType f))
                                        (debugFields b) }
  createQVar tp name b = do
    let name' = case name of
          Just n -> n
          Nothing -> "qv"
        (name'',nnames) = genName' (debugNames b) name'
    (rvar,nb) <- createQVar tp name (debugBackend' b)
    return (rvar,b { debugBackend' = nb
                   , debugNames = nnames
                   , debugQVars = DMap.insert rvar
                                  (UntypedVar name'' tp)
                                  (debugQVars b) })
  exit b = do
    b1 <- outputLisp b (L.List [L.Symbol "exit"])
    ((),nb) <- exit (debugBackend' b1)
    return ((),b1 { debugBackend' = nb })
  push b = do
    b1 <- outputLisp b (L.List [L.Symbol "push"])
    ((),nb) <- push (debugBackend' b1)
    return ((),b1 { debugBackend' = nb })
  pop b = do
    b1 <- outputLisp b (L.List [L.Symbol "pop"])
    ((),nb) <- pop (debugBackend' b1)
    return ((),b1 { debugBackend' = nb })
  defineVar name expr b = do
    let l = renderExpr b expr
        tp = getType expr
        (sym,req,nnames) = renderDefineVar (debugNames b) tp name l
        b1 = b { debugNames = nnames }
    b2 <- outputLisp b1 req
    (res,nb) <- defineVar name expr (debugBackend' b2)
    return (res,b2 { debugBackend' = nb
                   , debugVars = DMap.insert res (UntypedVar sym tp)
                                 (debugVars b2) })
  getUnsatCore b = do
    b1 <- outputLisp b (L.List [L.Symbol "get-unsat-core"])
    (res,nb) <- getUnsatCore (debugBackend' b1)
    let b2 = b1 { debugBackend' = nb }
    outputResponse b2 (show $ L.List [ L.Symbol ((debugCIds b2) Map.! cid)
                                     | cid <- res ])
    return (res,b2)
  getModel b = do
    b1 <- outputLisp b (L.List [L.Symbol "get-model"])
    (mdl,nb) <- getModel (debugBackend' b1)
    let b2 = b1 { debugBackend' = nb }
    outputResponse b2 (show mdl)
    return (mdl,b2)
  modelEvaluate mdl e b = do
    (res,nb) <- modelEvaluate mdl e (debugBackend' b)
    return (res,b { debugBackend' = nb })
  getProof b = do
    b1 <- outputLisp b (L.List [L.Symbol "get-proof"])
    (proof,nb) <- getProof (debugBackend' b1)
    let b2 = b1 { debugBackend' = nb }
    outputResponse b2 (show $ renderExpr b2 proof)
    return (proof,b2)
  simplify expr b = do
    let l = renderExpr b expr
    b1 <- outputLisp b (L.List [L.Symbol "simplify",l])
    (res,nb) <- simplify expr (debugBackend' b1)
    let b2 = b1 { debugBackend' = nb }
    outputResponse b2 (show $ renderExpr b2 res)
    return (res,b2)
  comment msg b = do
    b1 <- outputLine b True msg
    return ((),b1)
    
renderExpr :: (Backend b) => DebugBackend b -> Expr b tp
           -> L.Lisp
renderExpr b expr
  = runIdentity $ exprToLispWith
    (\v -> case DMap.lookup v (debugVars nb) of
             Just (UntypedVar r _) -> return $ L.Symbol r)
    (\v -> case DMap.lookup v (debugQVars nb) of
             Just (UntypedVar r _) -> return $ L.Symbol r)
    (\v -> case DMap.lookup v (debugFuns nb) of
             Just (UntypedFun r _ _) -> return $ L.Symbol r)
    (\v -> case DMap.lookup v (debugCons nb) of
             Just (UntypedCon r _ _) -> return $ L.Symbol r)
    (\v -> case DMap.lookup v (debugCons nb) of
             Just (UntypedCon r _ _) -> return $ L.Symbol $ T.append "is-" r)
    (\v -> case DMap.lookup v (debugFields nb) of
             Just (UntypedField r _ _) -> return $ L.Symbol r)
    (\v -> case DMap.lookup v (debugFVars nb) of
             Just (UntypedVar r _) -> return $ L.Symbol r)
    (\v -> case DMap.lookup v (debugLVars nb) of
             Just (UntypedVar r _) -> return $ L.Symbol r)
    (return . renderExpr nb) expr'
  where
    expr' = fromBackend (debugBackend' b) expr
    nb = case expr' of
      Let args _ -> runIdentity $ List.foldM (\cb var -> do
                                                 let (name,nnames) = genName' (debugNames cb) "var"
                                                 return cb { debugNames = nnames
                                                           , debugLVars = DMap.insert (letVar var)
                                                                          (UntypedVar name (getType $ letVar var))
                                                                          (debugLVars cb)
                                                           }
                                             ) b args
      _ -> b
