{-# LANGUAGE ViewPatterns, ImpredicativeTypes #-}
module Language.SMTLib2.Pipe
       (SMTPipe(),
        FunctionParser(..),
        createSMTPipe,
        withPipe,
        exprToLisp,
        exprToLispWith,
        lispToExpr,lispToExprWith,
        sortToLisp,lispToSort,
        renderExpr,
        renderExpr',
        renderSMTRequest,
        renderSMTResponse,
        commonFunctions,
        commonTheorems,
        simpleParser,
        FunctionParser'(..)) where

import Language.SMTLib2.Internals as SMT
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Strategy as Strat
import Data.Unit

import Data.Monoid
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Attoparsec
import System.Process
import qualified Data.Text as T

import System.IO as IO
import qualified Data.ByteString as BS hiding (reverse)
import qualified Data.ByteString.Char8 as BS8
import Blaze.ByteString.Builder
import Data.Typeable
import qualified Data.Map as Map
import Data.Fix
import Data.Proxy
#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
#endif
import Data.List (genericLength,genericIndex,find)
import Numeric (readInt,readHex)
import Data.Ratio
import Control.Monad.Trans (MonadIO,liftIO)
import Control.Monad.Identity
import Data.Char (isDigit)

{- | An SMT backend which uses process pipes to communicate with an SMT solver
     process. -}
data SMTPipe = SMTPipe { channelIn :: Handle
                       , channelOut :: Handle
                       , processHandle :: ProcessHandle
                       , smtState :: SMTState }

renderExpr :: (SMTType t,Monad m) => SMTExpr t -> SMT' m String
renderExpr expr = smtBackend $ \b -> do
  getName <- smtGetNames b
  (dts,nb) <- smtHandle b SMTDeclaredDataTypes
  return (renderExpr' getName dts expr,nb)

renderExpr' :: SMTType t => (Integer -> String) -> DataTypeInfo -> SMTExpr t -> String
renderExpr' getName dts expr
  = let lexpr = exprToLisp expr getName dts
    in show lexpr

instance MonadIO m => SMTBackend SMTPipe m where
  smtHandle pipe req@(SMTGetValue (expr::SMTExpr t))
    = case unmangle :: Unmangling t of
       PrimitiveUnmangling _ -> handleNormal pipe req
       ComplexUnmangling f -> do
         (res,npipe) <- f (\pipe expr' ann -> smtHandle pipe (SMTGetValue expr')
                          ) pipe expr (extractAnnotation expr)
         case res of
          Just x -> return (x,npipe)
          Nothing -> error $ "smtlib2: Error while unmangling expression "++show expr++" to type "++show (typeOf (undefined::t))
  smtHandle pipe req = handleNormal pipe req
  --smtGetState pipe = return $ smtState pipe
  smtGetNames pipe = return (\idx -> case Map.lookup idx (allVars (smtState pipe)) of
                              Just (info,nc) -> case funInfoName info of
                                Nothing -> escapeName (Right idx)
                                Just name -> escapeName (Left (name,nc)))
  smtNextName pipe = return (\name -> case name of
                              Nothing -> let nxt = nextVar (smtState pipe)
                                         in escapeName (Right nxt)
                              Just name' -> case Map.lookup name' (nameCount (smtState pipe)) of
                                Just nc -> escapeName (Left (name',nc))
                                Nothing -> escapeName (Left (name',0)))

handleNormal :: (MonadIO m,Typeable a) => SMTPipe -> SMTRequest a -> m (a,SMTPipe)
handleNormal pipe req = do
  case cast req of
   Just (_::SMTRequest ()) -> return ()
   _ -> clearInput pipe
  getName <- smtGetNames pipe
  nxtName <- smtNextName pipe
  case renderSMTRequest nxtName getName (declaredDataTypes $ smtState pipe) req of
   Left l -> putRequest pipe l
   Right "" -> return ()
   Right msg -> liftIO $ IO.hPutStr (channelIn pipe) $ Prelude.unlines (fmap (';':) (Prelude.lines msg))
  handleRequest pipe req

renderSMTRequest :: (Maybe String -> String) -> (Integer -> String) -> DataTypeInfo
                 -> SMTRequest r -> Either L.Lisp String
renderSMTRequest _ _ _ (SMTGetInfo SMTSolverName)
  = Left $ L.List [L.Symbol "get-info",L.Symbol ":name"]
renderSMTRequest _ _ _ (SMTGetInfo SMTSolverVersion)
  = Left $ L.List [L.Symbol "get-info",L.Symbol ":version"]
renderSMTRequest _ getName dts (SMTAssert expr interp cid)
  = let expr1 = exprToLisp expr getName dts
        expr2 = case interp of
          Nothing -> expr1
          Just (InterpolationGroup gr)
            -> L.List [L.Symbol "!"
                      ,expr1
                      ,L.Symbol ":interpolation-group"
                      ,L.Symbol (T.pack $ "i"++show gr)]
        expr3 = case cid of
          Nothing -> expr2
          Just (ClauseId cid)
            -> L.List [L.Symbol "!"
                      ,expr2
                      ,L.Symbol ":named"
                      ,L.Symbol (T.pack $ "_cid"++show cid)]
    in Left $ L.List [L.Symbol "assert",expr3]
renderSMTRequest _ _ _ (SMTCheckSat tactic limits)
  = Left $ L.List (if extendedCheckSat
                   then [L.Symbol "check-sat-using"
                        ,case tactic of
                          Just t -> tacticToLisp t
                          Nothing -> L.Symbol "smt"]++
                        (case limitTime limits of
                          Just t -> [L.Symbol ":timeout"
                                    ,L.Number (L.I t)]
                          Nothing -> [])++
                        (case limitMemory limits of
                          Just m -> [L.Symbol ":max-memory"
                                    ,L.Number (L.I m)]
                          Nothing -> [])
                   else [L.Symbol "check-sat"])
  where
    extendedCheckSat = case tactic of
      Just _ -> True
      _ -> case limitTime limits of
        Just _ -> True
        _ -> case limitMemory limits of
          Just _ -> True
          _ -> False
renderSMTRequest _ _ _ SMTDeclaredDataTypes = Right ""
renderSMTRequest _ _ _ (SMTDeclareDataTypes dts)
  = let param x = L.Symbol $ T.pack $ "arg"++show x
    in Left $
       L.List [L.Symbol "declare-datatypes"
              ,args [ param i | i <- [0..(argCount dts)-1] ]
              ,L.List
               [ L.List $ [L.Symbol $ T.pack $ dataTypeName dt]
                 ++ [ L.List $ [L.Symbol $ T.pack $ conName con]
                      ++ [ L.List [L.Symbol $ T.pack $ fieldName field
                                  ,case fieldSort field of
                                    Fix (NormalSort (NamedSort fTpName _)) -> case find (\dt -> (dataTypeName dt)==fTpName) (dataTypes dts) of
                                      Nothing -> argumentSortToLisp param (fieldSort field)
                                      Just _ -> L.Symbol (T.pack fTpName)
                                    _ -> argumentSortToLisp param (fieldSort field)]
                         | field <- conFields con ]
                    | con <- dataTypeConstructors dt ]
               | dt <- dataTypes dts ]
              ]
renderSMTRequest _ _ _ (SMTDeclareSort name arity)
  = Left $ L.List [L.Symbol "declare-sort",L.Symbol $ T.pack name,L.toLisp arity]
renderSMTRequest nextName _ _ (SMTDeclareFun finfo)
  = let tps = funInfoArgSorts finfo
        rtp = funInfoSort finfo
    in Left $ L.List [L.Symbol "declare-fun"
                     ,L.Symbol $ T.pack (nextName (funInfoName finfo))
                     ,args (fmap sortToLisp tps)
                     ,sortToLisp rtp
                     ]
renderSMTRequest nextName getName dts (SMTDefineFun name (_::Proxy arg) argAnn (body::SMTExpr res))
  = let tpLst = zip [0..] (getTypes (undefined::arg) argAnn)
        annRes = extractAnnotation body
        name' = nextName name
        retSort = getSort (undefined::res) annRes
    in Left $ L.List [L.Symbol "define-fun"
                     ,L.Symbol $ T.pack name'
                     ,args [ L.List [ L.Symbol $ T.pack $ "farg_"++show (j::Integer)
                                    , sortToLisp $ getSort u ann ]
                           | (j,ProxyArg u ann) <- tpLst ]
                     ,sortToLisp retSort
                     ,exprToLisp body getName dts]
renderSMTRequest _ _ _ (SMTComment msg) = Right msg
renderSMTRequest _ _ _ SMTExit = Left $ L.List [L.Symbol "exit"]
renderSMTRequest _ _ _ (SMTGetInterpolant grps)
  = Left $ L.List [L.Symbol "get-interpolant"
                  ,L.List [ L.Symbol $ T.pack ("i"++show g) | InterpolationGroup g <- grps ]
                  ]
renderSMTRequest _ getName dts (SMTInterpolate exprs)
  = Left $ L.List $ (L.Symbol "get-interpolant"):
    [ exprToLisp expr getName dts
    | expr <- exprs ]
renderSMTRequest _ _ _ (SMTSetOption opt)
  = Left $ L.List $ [L.Symbol "set-option"]
    ++(case opt of
        PrintSuccess v -> [L.Symbol ":print-success"
                          ,L.Symbol $ if v then "true" else "false"]
        ProduceModels v -> [L.Symbol ":produce-models"
                           ,L.Symbol $ if v then "true" else "false"]
        SMT.ProduceProofs v -> [L.Symbol ":produce-proofs"
                               ,L.Symbol $ if v then "true" else "false"]
        SMT.ProduceUnsatCores v -> [L.Symbol ":produce-unsat-cores"
                                   ,L.Symbol $ if v then "true" else "false"]
        ProduceInterpolants v -> [L.Symbol ":produce-interpolants"
                                 ,L.Symbol $ if v then "true" else "false"]
      )
renderSMTRequest _ _ _ (SMTSetLogic name)
  = Left $ L.List [L.Symbol "set-logic"
                  ,L.Symbol $ T.pack name]
renderSMTRequest _ _ _ SMTGetProof
  = Left $ L.List [L.Symbol "get-proof"]
renderSMTRequest _ _ _ SMTGetUnsatCore
  = Left $ L.List [L.Symbol "get-unsat-core"]
renderSMTRequest _ getName dts (SMTSimplify expr)
  = let lexpr = exprToLisp expr getName dts
    in Left $ L.List [L.Symbol "simplify"
                     ,lexpr]
renderSMTRequest _ _ _ SMTPush = Left $ L.List [L.Symbol "push",L.toLisp (1::Integer)]
renderSMTRequest _ _ _ SMTPop = Left $ L.List [L.Symbol "pop",L.toLisp (1::Integer)]
renderSMTRequest _ getName dts (SMTGetValue expr)
  = let lexpr = exprToLisp expr getName dts
    in Left $ L.List [L.Symbol "get-value"
                     ,L.List [lexpr]]
renderSMTRequest _ _ _ SMTGetModel = Left $ L.List [L.Symbol "get-model"]
renderSMTRequest _ _ _ (SMTApply tactic)
  = Left $ L.List [L.Symbol "apply"
                  ,tacticToLisp tactic]
renderSMTRequest _ _ _ (SMTNameExpr _ _) = Right ""
renderSMTRequest _ _ _ SMTNewInterpolationGroup = Right ""
renderSMTRequest _ _ _ SMTNewClauseId = Right ""

handleRequest :: MonadIO m => SMTPipe -> SMTRequest response -> m (response,SMTPipe)
handleRequest pipe (SMTGetInfo SMTSolverName) = do
  res <- parseResponse pipe
  case res of
    L.List [L.Symbol ":name",L.String name] -> return (T.unpack name,pipe)
    _ -> error "Invalid solver response to 'get-info' name query"
handleRequest pipe (SMTGetInfo SMTSolverVersion) = do
  res <- parseResponse pipe
  case res of
    L.List [L.Symbol ":version",L.String name] -> return (T.unpack name,pipe)
    _ -> error "Invalid solver response to 'get-info' version query"
handleRequest pipe (SMTAssert _ _ _) = return ((),pipe)
handleRequest pipe (SMTCheckSat tactic limits) = do
  res <- liftIO $ BS.hGetLine (channelOut pipe)
  return (case res of
           "sat" -> Sat
           "sat\r" -> Sat
           "unsat" -> Unsat
           "unsat\r" -> Unsat
           "unknown" -> Unknown
           "unknown\r" -> Unknown
           _ -> error $ "smtlib2: unknown check-sat response: "++show res,pipe)
handleRequest pipe SMTDeclaredDataTypes = return (declaredDataTypes $ smtState pipe,pipe)
handleRequest pipe (SMTDeclareDataTypes dts) = do
  let ndts = addDataTypeStructure dts (declaredDataTypes $ smtState pipe)
  return ((),pipe { smtState = (smtState pipe) { declaredDataTypes = ndts } })
handleRequest pipe (SMTDeclareSort name arity) = return ((),pipe)
handleRequest pipe (SMTDeclareFun info)
  = let (v,_,nst) = smtStateAddFun info (smtState pipe)
    in return (v,pipe { smtState = nst })
handleRequest pipe (SMTDefineFun name (_::Proxy arg) argAnn (body::SMTExpr res)) = do
  let finfo = FunInfo { funInfoProxy = Proxy::Proxy (arg,res)
                      , funInfoArgAnn = argAnn
                      , funInfoResAnn = extractAnnotation body
                      , funInfoName = name }
      (i,_,nst) = smtStateAddFun finfo (smtState pipe)
  return (i,pipe { smtState = nst })
handleRequest pipe (SMTComment msg) = return ((),pipe)
handleRequest pipe SMTExit = do
  liftIO $ hClose (channelIn pipe)
  liftIO $ hClose (channelOut pipe)
  liftIO $ terminateProcess (processHandle pipe)
  _ <- liftIO $ waitForProcess (processHandle pipe)
  return ((),pipe)
handleRequest pipe (SMTGetInterpolant grps) = do
  val <- parseResponse pipe
  case lispToExpr commonFunctions
       (findName $ smtState pipe) (declaredDataTypes $ smtState pipe)
       gcast (Just $ Fix BoolSort) 0 val of
    Just (Just x) -> return (x,pipe)
    _ -> error $ "smtlib2: Failed to parse get-interpolant result: "++show val
handleRequest pipe (SMTInterpolate exprs) = case exprs of
  [] -> return ([],pipe)
  e:es -> do
    resp <- mapM (\_ -> do
                     val <- parseResponse pipe
                     case lispToExpr commonFunctions
                          (findName $ smtState pipe)
                          (declaredDataTypes $ smtState pipe)
                          gcast (Just $ Fix BoolSort) 0 val of
                      Just (Just x) -> return x
                      _ -> error $ "smtlib2: Failed to parse get-interpolant result: "++show val
                 ) es
    return (resp,pipe)
handleRequest pipe (SMTSetOption opt) = return ((),pipe)
handleRequest pipe (SMTSetLogic name) = return ((),pipe)
handleRequest pipe SMTGetProof = do
  res <- parseResponse pipe
  let proof = case res of
        L.List items -> case findProof items of
          Nothing -> res
          Just p -> p
        _ -> res
  case lispToExpr (commonFunctions `mappend` commonTheorems)
       (findName $ smtState pipe)
       (declaredDataTypes $ smtState pipe) gcast (Just $ Fix BoolSort) 0 proof of
    Just (Just x) -> return (x,pipe)
    _ -> error $ "smtlib2: Couldn't parse proof "++show res
  where
    findProof [] = Nothing :: Maybe L.Lisp
    findProof ((L.List [L.Symbol "proof",proof]):_) = Just proof
    findProof (x:xs) = findProof xs
handleRequest pipe SMTGetUnsatCore = do
  res <- parseResponse pipe
  case res of
    L.List names -> return
                    (fmap (\name -> case name of
                            L.Symbol s -> case T.unpack s of
                              '_':'c':'i':'d':cid
                                | all isDigit cid -> ClauseId (read cid)
                              str -> error $ "Language.SMTLib2.getUnsatCore: Unknown clause id "++str
                            _ -> error $ "Language.SMTLib2.getUnsatCore: Unknown expression "
                                 ++show name++" in core list."
                          ) names,pipe)
    _ -> error $ "Language.SMTLib2.getUnsatCore: Unknown response "++show res++" to query."
handleRequest pipe (SMTSimplify (expr::SMTExpr t)) = do
  val <- parseResponse pipe
  case lispToExpr commonFunctions
       (findName $ smtState pipe) (declaredDataTypes $ smtState pipe)
       gcast (Just $ getSort (undefined::t) (extractAnnotation expr)) 0 val of
    Just (Just x) -> return (x,pipe)
    _ -> error $ "smtlib2: Failed to parse simplify result: "++show val
handleRequest pipe SMTPush = return ((),pipe)
handleRequest pipe SMTPop = return ((),pipe)
handleRequest pipe (SMTGetValue (expr::SMTExpr t)) = do
  let ann = extractAnnotation expr
      sort = getSort (undefined::t) ann
      PrimitiveUnmangling unm = unmangle :: Unmangling t
  val <- parseResponse pipe
  case val of
    L.List [L.List [_,res]]
      -> let res' = removeLets res
         in case lispToValue' (declaredDataTypes $ smtState pipe) (Just sort) res' of
           Just val' -> case unm val' ann of
             Just val'' -> return (val'',pipe)
             Nothing -> error $ "smtlib2: Failed to unmangle value "++show val'++" to type "++show (typeOf (undefined::t))
           Nothing -> error $ "smtlib2: Failed to parse value from "++show res
    _ -> error $ "smtlib2: Unexpected get-value response: "++show val
handleRequest pipe SMTGetModel = do
  val <- parseResponse pipe
  case val of
   L.List (L.Symbol "model":mdl) -> return (foldl parseModel (SMTModel Map.empty) mdl,pipe)
   _ -> error $ "smtlib2: Unexpected get-model response: "++show val
  where
    parseModel cur (L.List [L.Symbol "define-fun",
                            L.Symbol fname,
                            L.List args,
                            rtp,
                            fun]) = case mapM (\arg -> case arg of
                                                L.List [L.Symbol argName,
                                                        argTp] -> case lispToSort argTp of
                                                  Just argTp' -> withSort (declaredDataTypes $ smtState pipe ) argTp' $
                                                                 \u ann -> Just (argName,ProxyArg u ann)
                                                  _ -> Nothing
                                                _ -> Nothing
                                              ) args of
      Just args' -> case lispToSort rtp of
        Just rtp' -> let argMp = Map.fromList [ (name,(i,sort))
                                              | (i,(name,sort)) <- zip [0..] args' ]
                         funId = case unescapeName (T.unpack fname) of
                           Nothing -> Nothing :: Maybe Integer
                           Just (Right idx) -> Just idx
                           Just (Left name) -> case Map.lookup name (namedVars $ smtState pipe) of
                             Just idx -> Just idx
                             Nothing -> Nothing
                     in case lispToExpr commonFunctions (\n -> do
                                                            (i,tp) <- Map.lookup n argMp
                                                            return $ QVar 0 i tp)
                             (declaredDataTypes $ smtState pipe)
                             UntypedExpr
                             (Just rtp')
                             1
                             fun of
                         Just res -> case funId of
                           Nothing -> error $ "smtlib2: Model defines unknown function "++show fname
                           Just fid -> cur { modelFunctions = Map.insert fid (0,fmap snd args',res)
                                                              (modelFunctions cur)
                                           }
        Nothing -> error $ "smtlib2: Failed to parse return type: "++show rtp
      Nothing -> error $ "smtlib2: Failed to parse argument specification "++show args
    parseModel _ def = error $ "smtlib2: Failed to parse model entry: "++show def
handleRequest pipe (SMTApply tactic) = do
  val <- parseResponse pipe
  case val of
    L.List (L.Symbol "goals":goals)
      -> return
         (fmap (\goal -> case goal of
                 L.List ((L.Symbol "goal"):expr:_)
                   -> case lispToExpr (commonFunctions `mappend` commonTheorems)
                           (findName $ smtState pipe)
                           (declaredDataTypes $ smtState pipe) gcast (Just $ Fix BoolSort) 0 expr of
                       Just (Just x) -> x
                       _ -> error $ "smtlib2: Couldn't parse goal "++show expr
                 _ -> error $ "smtlib2: Couldn't parse goal description "++show val
               ) goals,pipe)
handleRequest pipe (SMTNameExpr name (expr::SMTExpr t)) = do
  return (i,pipe { smtState = nst })
  where
    finfo = FunInfo { funInfoProxy = Proxy::Proxy ((),t)
                    , funInfoArgAnn = ()
                    , funInfoResAnn = extractAnnotation expr
                    , funInfoName = Just name }
    (i,_,nst) = smtStateAddFun finfo (smtState pipe)
handleRequest pipe SMTNewInterpolationGroup = do
  return (InterpolationGroup igrp,pipe { smtState = nst })
  where
    igrp = nextInterpolationGroup (smtState pipe)
    nst = (smtState pipe) { nextInterpolationGroup = igrp+1 }
handleRequest pipe SMTNewClauseId = do
  return (ClauseId icl,pipe { smtState = nst })
  where
    icl = nextClauseId (smtState pipe)
    nst = (smtState pipe) { nextClauseId = icl+1 }

renderSMTResponse :: (Integer -> String) -> DataTypeInfo -> SMTRequest response -> response -> Maybe String
renderSMTResponse _ _ (SMTGetInfo SMTSolverName) name
  = Just $ show $ L.List [L.Symbol ":name",L.String $ T.pack name]
renderSMTResponse _ _ (SMTGetInfo SMTSolverVersion) vers
  = Just $ show $ L.List [L.Symbol ":version",L.String $ T.pack vers]
renderSMTResponse _ _ (SMTCheckSat _ _) res = case res of
  Sat -> Just "sat"
  Unsat -> Just "unsat"
  Unknown -> Just "unknown"
renderSMTResponse getName dts (SMTGetInterpolant grps) expr
  = Just $ renderExpr' getName dts expr
renderSMTResponse getName dts (SMTInterpolate _) exprs
  = Just $ unwords [ renderExpr' getName dts expr
                   | expr <- exprs ]
renderSMTResponse getName dts SMTGetProof proof
  = Just $ renderExpr' getName dts proof
renderSMTResponse getName dts (SMTSimplify _) expr
  = Just $ renderExpr' getName dts expr
renderSMTResponse _ _ (SMTGetValue _) v = Just $ show v
renderSMTResponse getName dts (SMTApply _) goals
  = Just $ show $
    L.List $ [L.Symbol "goals"]++
    [exprToLisp goal getName dts
    | goal <- goals ]
renderSMTResponse _ _ SMTGetUnsatCore core = Just (show core)
renderSMTResponse getName dts SMTGetModel mdl
  = Just $ "(model"++concat assignments++")"
  where
    assignments = [ "\n  ("++getName fun++" "++
                    renderExpr' getName dts expr++")"
                  | (fun,(_,_,expr)) <- Map.toList $ modelFunctions mdl ]
renderSMTResponse _ _ _ _ = Nothing

-- | Spawn a new SMT solver process and create a pipe to communicate with it.
createSMTPipe :: String -- ^ Path to the binary of the SMT solver
              -> [String] -- ^ Command line arguments to be passed to the SMT solver
              -> IO SMTPipe
createSMTPipe solver args = do
  let cmd = CreateProcess { cmdspec = RawCommand solver args
                          , cwd = Nothing
                          , env = Nothing
                          , std_in = CreatePipe
                          , std_out = CreatePipe
                          , std_err = Inherit
                          , close_fds = False
                          , create_group = True
#if MIN_VERSION_process(1,2,0)
                          , delegate_ctlc = False
#endif
                          }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  return $ SMTPipe { channelIn = hin
                   , channelOut = hout
                   , processHandle = handle
                   , smtState = emptySMTState }

sortToLisp :: Sort -> L.Lisp
sortToLisp s = sortToLisp' sortToLisp (unFix s)

argumentSortToLisp :: (Integer -> L.Lisp) -> ArgumentSort -> L.Lisp
argumentSortToLisp f sort = case unFix sort of
  ArgumentSort i -> f i
  NormalSort s -> sortToLisp' (argumentSortToLisp f) s

sortToLisp' :: (a -> L.Lisp) -> Sort' a -> L.Lisp
sortToLisp' _ BoolSort = L.Symbol "Bool"
sortToLisp' _ IntSort = L.Symbol "Int"
sortToLisp' _ RealSort = L.Symbol "Real"
sortToLisp' _ (BVSort { bvSortWidth = w })
  = L.List [L.Symbol "_",
            L.Symbol "BitVec",
            L.toLisp w]
sortToLisp' f (ArraySort args' val)
  = L.List ((L.Symbol "Array"):(fmap f args')++[f val])
sortToLisp' _ (NamedSort name []) = L.Symbol (T.pack name)
sortToLisp' f (NamedSort name args)
  = L.List $ (L.Symbol $ T.pack name):fmap f args

-- | Parse a lisp expression into an SMT sort.
lispToSort :: L.Lisp -> Maybe Sort
lispToSort (L.Symbol "Bool") = Just $ Fix BoolSort
lispToSort (L.Symbol "Int") = Just $ Fix IntSort
lispToSort (L.Symbol "Real") = Just $ Fix RealSort
lispToSort (L.List [L.Symbol "_",
                    L.Symbol "BitVec",
                    L.Number (L.I n)])
  = Just $ Fix $ BVSort { bvSortWidth = n
                        , bvSortUntyped = False }
lispToSort (L.List (L.Symbol "Array":args)) = do
  argSorts <- mapM lispToSort args'
  resSort <- lispToSort res
  return $ Fix $ ArraySort argSorts resSort
  where
    (args',res) = splitLast args
    splitLast [s] = ([],s)
    splitLast (x:xs) = let (xs',l) = splitLast xs
                       in (x:xs',l)
lispToSort (L.Symbol x) = Just $ Fix $ NamedSort (T.unpack x) []
lispToSort (L.List ((L.Symbol x):args)) = do
  argSorts <- mapM lispToSort args
  return $ Fix $ NamedSort (T.unpack x) argSorts
lispToSort _ = Nothing

{-getSMTName :: FunInfo -> String
getSMTName info = escapeName (case funInfoName info of
  Nothing -> Right (funInfoId info)
  Just name -> Left name)-}

findName :: SMTState -> T.Text -> Maybe (SMTExpr Untyped)
findName st name = case unescapeName (T.unpack name) of
  Nothing -> Nothing
  Just (Right idx) -> case Map.lookup idx (allVars st) of
    Nothing -> Nothing
    Just (FunInfo { funInfoProxy = _::Proxy (a,t)
                  , funInfoResAnn = ann
                  },nc) -> let expr :: SMTExpr t
                               expr = Var idx ann
                           in Just $ mkUntyped expr
  Just (Left name') -> case Map.lookup name' (namedVars st) of
    Nothing -> Nothing
    Just idx -> case Map.lookup idx (allVars st) of
      Nothing -> Nothing
      Just (FunInfo { funInfoProxy = _::Proxy (a,t)
                    , funInfoResAnn = ann
                    },_) -> let expr :: SMTExpr t
                                expr = Var idx ann
                            in Just $ mkUntyped expr

mkUntyped :: SMTType t => SMTExpr t -> SMTExpr Untyped
mkUntyped e = case cast e of
  Just e' -> e'
  Nothing -> case cast e of
    Just e' -> entypeValue UntypedExpr e'
    Nothing -> UntypedExpr e

exprToLisp :: SMTExpr t -> (Integer -> String) -> DataTypeInfo -> L.Lisp
exprToLisp
  = exprToLispWith
    (\obj -> error $ "smtlib2: Can't translate internal object "++
             show obj++" to s-expression.")

exprToLispWith :: (forall a. (Typeable a,Ord a,Show a) => a -> L.Lisp) -> SMTExpr t
                  -> (Integer -> String)
                  -> DataTypeInfo -> L.Lisp
exprToLispWith _ (Var idx _) mp _ = L.Symbol $ T.pack $ mp idx
exprToLispWith _ (QVar lvl idx _) _ _ = L.Symbol $ T.pack $ "q_"++show lvl++"_"++show idx
exprToLispWith _ (FunArg i _) _ _ = L.Symbol $ T.pack $ "farg_"++show i
exprToLispWith objs (Const x ann) mp dts = case mangle of
  PrimitiveMangling f -> valueToLisp dts $ f x ann
  ComplexMangling f -> exprToLispWith objs (f x ann) mp dts
exprToLispWith _ (AsArray f arg) mp _
  = let f' = functionGetSymbol mp f arg
        (sargs,sres) = functionSignature f arg
    in L.List [L.Symbol "_",L.Symbol "as-array",if isOverloaded f
                                                then L.List [f'
                                                            ,L.List $ fmap sortToLisp sargs
                                                            ,sortToLisp sres]
                                                else f']
exprToLispWith objs (Forall lvl tps body) mp dts
  = L.List [L.Symbol "forall"
           ,L.List [L.List [L.Symbol $ T.pack $ "q_"++show lvl++"_"++show (i::Integer),sortToLisp sort]
                   | (i,tp) <- Prelude.zip [0..] tps
                   , let sort = withProxyArg tp getSort ]
           ,exprToLispWith objs body mp dts]
exprToLispWith objs (Exists lvl tps body) mp dts
  = L.List [L.Symbol "exists"
           ,L.List [L.List [L.Symbol $ T.pack $ "q_"++show lvl++"_"++show (i::Integer),sortToLisp sort]
                   | (i,tp) <- Prelude.zip [0..] tps
                   , let sort = withProxyArg tp getSort ]
           ,exprToLispWith objs body mp dts]
exprToLispWith objs (Let lvl args body) mp dts
  = L.List [L.Symbol "let"
           ,L.List [L.List [L.Symbol $ T.pack $ "q_"++show lvl++"_"++show (i::Integer),
                            exprToLispWith objs def mp dts]
                   | (i,def) <- Prelude.zip [0..] args ]
           ,exprToLispWith objs body mp dts]
exprToLispWith objs (App fun x) mp dts
  = let arg_ann = extractArgAnnotation x
        l = functionGetSymbol mp fun arg_ann
        x' = fmap (\e -> exprToLispWith objs e mp dts) (fromArgs x)
    in if Prelude.null x'
       then l
       else L.List $ l:x'
exprToLispWith objs (Named expr idx) mp dts
  = let expr' = exprToLispWith objs expr mp dts
        name = mp idx
    in L.List [L.Symbol "!",expr'
              ,L.Symbol ":named"
              ,L.Symbol $ T.pack name]
exprToLispWith objs (InternalObj obj ann) _ _ = objs obj
exprToLispWith objs (UntypedExpr expr) mp dts
  = exprToLispWith objs expr mp dts
exprToLispWith objs (UntypedExprValue expr) mp dts
  = exprToLispWith objs expr mp dts

isOverloaded :: SMTFunction a b -> Bool
isOverloaded SMTEq = True
isOverloaded (SMTMap _) = True
isOverloaded (SMTOrd _) = True
isOverloaded (SMTArith _) = True
isOverloaded SMTMinus = True
isOverloaded SMTNeg = True
isOverloaded SMTAbs = True
isOverloaded SMTDistinct = True
isOverloaded SMTITE = True
isOverloaded (SMTBVComp _) = True
isOverloaded (SMTBVBin _) = True
isOverloaded (SMTBVUn _) = True
isOverloaded SMTSelect = True
isOverloaded SMTStore = True
isOverloaded (SMTConstArray _) = True
isOverloaded SMTConcat = True
isOverloaded (SMTExtract _ _) = True
isOverloaded _ = False

functionSignature :: (Args a,SMTType b) => SMTFunction a b -> ArgAnnotation a -> ([Sort],Sort)
functionSignature f argAnn = withUndef f $
                             \ua ur -> (getSorts ua argAnn,
                                        getSort ur resAnn)
  where
    resAnn = inferResAnnotation f argAnn
    withUndef :: SMTFunction a b -> (a -> b -> r) -> r
    withUndef _ f = f undefined undefined

functionGetSymbol :: (Integer -> String) -> SMTFunction a b -> ArgAnnotation a -> L.Lisp
functionGetSymbol _ SMTEq _ = L.Symbol "="
functionGetSymbol mp fun@(SMTMap f) ann
  = L.List [L.Symbol "_",
            L.Symbol "map",
            sym]
  where
    getUndefI :: SMTFunction p (SMTArray i res) -> i
    getUndefI _ = undefined
    getUndefA :: SMTFunction arg res -> arg
    getUndefA _ = undefined
    ui = getUndefI fun
    ua = getUndefA f
    (ann_i,ann_v) = inferLiftedAnnotation ua ui ann
    sym' = functionGetSymbol mp f ann_v
    (sigArg,sigRes) = functionSignature f ann_v
    sym = if isOverloaded f
          then L.List [sym',
                       L.List (fmap sortToLisp sigArg),
                       sortToLisp sigRes]
          else sym'     
functionGetSymbol mp (SMTFun i _) _ = L.Symbol (T.pack $ mp i)
functionGetSymbol _ (SMTBuiltIn name _) _ = L.Symbol $ T.pack name
functionGetSymbol _ (SMTOrd op) _ = L.Symbol $ case op of
  Ge -> ">="
  Gt -> ">"
  Le -> "<="
  Lt -> "<"
functionGetSymbol _ (SMTArith op) _ = L.Symbol $ case op of
  Plus -> "+"
  Mult -> "*"
functionGetSymbol _ SMTMinus _ = L.Symbol "-"
functionGetSymbol _ (SMTIntArith op) _ = L.Symbol $ case op of
  Div -> "div"
  Mod -> "mod"
  Rem -> "rem"
functionGetSymbol _ SMTDivide _ = L.Symbol "/"
functionGetSymbol _ SMTNeg _ = L.Symbol "-"
functionGetSymbol _ SMTAbs _ = L.Symbol "abs"
functionGetSymbol _ SMTNot _ = L.Symbol "not"
functionGetSymbol _ (SMTLogic op) _ = case op of
  And -> L.Symbol "and"
  Or -> L.Symbol "or"
  XOr -> L.Symbol "xor"
  Implies -> L.Symbol "=>"
functionGetSymbol _ SMTDistinct _ = L.Symbol "distinct"
functionGetSymbol _ SMTToReal _ = L.Symbol "to_real"
functionGetSymbol _ SMTToInt _ = L.Symbol "to_int"
functionGetSymbol _ SMTITE _ = L.Symbol "ite"
functionGetSymbol _ (SMTBVComp op) _ = L.Symbol $ case op of
  BVULE -> "bvule"
  BVULT -> "bvult"
  BVUGE -> "bvuge"
  BVUGT -> "bvugt"
  BVSLE -> "bvsle"
  BVSLT -> "bvslt"
  BVSGE -> "bvsge"
  BVSGT -> "bvsgt"
functionGetSymbol _ (SMTBVBin op) _ = L.Symbol $ case op of
  BVAdd -> "bvadd"
  BVSub -> "bvsub"
  BVMul -> "bvmul"
  BVURem -> "bvurem"
  BVSRem -> "bvsrem"
  BVUDiv -> "bvudiv"
  BVSDiv -> "bvsdiv"
  BVSHL -> "bvshl"
  BVLSHR -> "bvlshr"
  BVASHR -> "bvashr"
  BVXor -> "bvxor"
  BVAnd -> "bvand"
  BVOr -> "bvor"
functionGetSymbol _ (SMTBVUn op) _ = case op of
  BVNot -> L.Symbol "bvnot"
  BVNeg -> L.Symbol "bvneg"
functionGetSymbol _ SMTSelect _ = L.Symbol "select"
functionGetSymbol _ SMTStore _ = L.Symbol "store"
functionGetSymbol _ f@(SMTConstArray i_ann) v_ann
  = withUndef f $
    \u_arr -> L.List [L.Symbol "as"
                     ,L.Symbol "const"
                     ,sortToLisp $ getSort u_arr (i_ann,v_ann)]
  where
    withUndef :: SMTFunction (SMTExpr v) (SMTArray i v)
                 -> (SMTArray i v -> a) -> a
    withUndef _ f' = f' undefined
functionGetSymbol _ SMTConcat _ = L.Symbol "concat"
functionGetSymbol _ f@(SMTExtract prStart prLen) ann
  = L.List [L.Symbol "_"
           ,L.Symbol "extract"
           ,L.Number $ L.I (start+len-1)
           ,L.Number $ L.I start]
  where
    start = reflectNat prStart 0
    len = reflectNat prLen 0
functionGetSymbol _ (SMTConstructor (Constructor _ _ con)) _ = L.Symbol $ T.pack (conName con)
functionGetSymbol _ (SMTConTest (Constructor _ _ con)) _ = L.Symbol $ T.pack $ "is-"++(conName con)
functionGetSymbol _ (SMTFieldSel (Field _ _ _ f)) _ = L.Symbol $ T.pack (fieldName f)
functionGetSymbol _ (SMTDivisible n) _ = L.List [L.Symbol "_",L.Symbol "divisible",L.Number $ L.I n]

clearInput :: MonadIO m => SMTPipe -> m ()
clearInput pipe = do
  r <- liftIO $ hReady (channelOut pipe)
  if r
    then (do
             _ <- liftIO $ BS.hGetSome (channelOut pipe) 1024
             clearInput pipe)
    else return ()

putRequest :: MonadIO m => SMTPipe -> L.Lisp -> m ()
putRequest pipe expr = do
  clearInput pipe
  liftIO $ toByteStringIO (BS.hPutStr $ channelIn pipe) (mappend (L.fromLispExpr expr) flush)
  liftIO $ BS8.hPutStrLn (channelIn pipe) ""
  liftIO $ hFlush (channelIn pipe)

parseResponse :: MonadIO m => SMTPipe -> m L.Lisp
parseResponse pipe = do
  str <- liftIO $ BS.hGetLine (channelOut pipe)
  let continue (Done _ r) = return r
      continue res@(Partial _) = do
        line <- liftIO $ BS.hGetLine (channelOut pipe)
        continue (feed (feed res line) (BS8.singleton '\n'))
      continue (Fail str' ctx msg) = error $ "Error parsing "++show str'++" response in "++show ctx++": "++msg
  continue $ parse L.lisp (BS8.snoc str '\n')

args :: [L.Lisp] -> L.Lisp
args [] = L.Symbol "()"
args xs = L.List xs

removeLets :: L.Lisp -> L.Lisp
removeLets = removeLets' Map.empty
  where
    removeLets' mp (L.List [L.Symbol "let",L.List decls,body])
      = let nmp = Map.union mp
                  (Map.fromList
                   [ (name,removeLets' nmp expr)
                   | L.List [L.Symbol name,expr] <- decls ])
        in removeLets' nmp body
    removeLets' mp (L.Symbol sym) = case Map.lookup sym mp of
      Nothing -> L.Symbol sym
      Just r -> r
    removeLets' mp (L.List entrs) = L.List $ fmap (removeLets' mp) entrs
    removeLets' _ x = x

newtype FunctionParser = FunctionParser { parseFun :: L.Lisp
                                                      -> FunctionParser
                                                      -> DataTypeInfo
                                                      -> Maybe FunctionParser' }

instance Monoid FunctionParser where
  mempty = FunctionParser $ \_ _ _ -> Nothing
  mappend p1 p2 = FunctionParser $ \l fun dts -> case parseFun p1 l fun dts of
    Nothing -> parseFun p2 l fun dts
    Just r -> Just r

data FunctionParser'
  = OverloadedParser { sortConstraint :: [Sort] -> Bool
                     , deriveRetSort :: [Sort] -> Maybe Sort
                     , parseOverloaded :: forall a. [Sort] -> Sort
                                          -> (forall arg res. (Liftable arg,SMTType res) => SMTFunction arg res -> a)
                                          -> Maybe a }
  | DefinedParser { definedArgSig :: [Sort]
                  , definedRetSig :: Sort
                  , parseDefined :: forall a. (forall arg res. (Liftable arg,SMTType res) => SMTFunction arg res -> a)
                                     -> Maybe a }

-- | A map which contains signatures for a few common theorems which can be used in the proofs which 'getProof' returns.
commonTheorems :: FunctionParser
commonTheorems = mconcat
                 [nameParser (L.Symbol "|unit-resolution|")
                  (OverloadedParser (const True)
                   (const $ Just $ Fix BoolSort)
                   $ \_ _ f -> Just $ f (SMTBuiltIn "|unit-resolution|" () :: SMTFunction [SMTExpr Bool] Bool))
                 ,simpleParser (SMTBuiltIn "asserted" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTBuiltIn "hypothesis" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTBuiltIn "lemma" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTBuiltIn "monotonicity" () :: SMTFunction (SMTExpr Bool,SMTExpr Bool) Bool)
                 ,simpleParser (SMTBuiltIn "trans" () :: SMTFunction (SMTExpr Bool,SMTExpr Bool,SMTExpr Bool) Bool)
                 ,simpleParser (SMTBuiltIn "rewrite" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTBuiltIn "mp" () :: SMTFunction (SMTExpr Bool,SMTExpr Bool,SMTExpr Bool) Bool)]

lispToValue :: DataTypeInfo -> Maybe Sort -> L.Lisp -> Maybe Value
lispToValue _ sort (L.Symbol "true") = case sort of
  Nothing -> Just $ BoolValue True
  Just (Fix BoolSort) -> Just $ BoolValue True
  Just _ -> Nothing
lispToValue _ sort (L.Symbol "false") = case sort of
  Nothing -> Just $ BoolValue False
  Just (Fix BoolSort) -> Just $ BoolValue False
  Just _ -> Nothing
lispToValue _ sort (L.Number (L.I x)) = case sort of
  Nothing -> Just $ IntValue x
  Just (Fix RealSort) -> Just $ RealValue (fromInteger x)
  Just (Fix IntSort) -> Just $ IntValue x
  Just (Fix (BVSort { bvSortWidth = w })) -> Just $ BVValue { bvValueWidth = w
                                                            , bvValueValue = x }
  Just _ -> Nothing
lispToValue dts sort (L.List [L.Symbol "-",v])
  = case lispToValue dts sort v of
  Just (RealValue x) -> Just $ RealValue (-x)
  Just (IntValue x) -> Just $ IntValue (-x)
  _ -> Nothing
lispToValue _ sort (L.Number (L.D x)) = case sort of
  Nothing -> Just $ RealValue (realToFrac x)
  Just (Fix RealSort) -> Just $ RealValue (realToFrac x)
  Just _ -> Nothing
lispToValue dts sort (L.List [L.Symbol "/",x,y]) = case sort of
  Nothing -> result
  Just (Fix RealSort) -> result
  Just _ -> Nothing
  where
    result = do
      RealValue x' <- lispToValue dts (Just $ Fix RealSort) x
      RealValue y' <- lispToValue dts (Just $ Fix RealSort) y
      return $ RealValue $ x' / y'
lispToValue _ sort (L.Symbol s) = case sort of
  Nothing -> result
  Just (Fix (BVSort {})) -> result
  Just _ -> Nothing
  where
    result = case T.unpack s of
      '#':'b':rest -> let len = genericLength rest
                      in case readInt 2
                              (\x -> x=='0' || x=='1')
                              (\x -> if x=='0' then 0 else 1)
                              rest of
                           [(v,_)] -> Just $ BVValue { bvValueWidth = len
                                                     , bvValueValue = v }
                           _ -> Nothing
      '#':'x':rest -> let len = (genericLength rest)*4
                      in case readHex rest of
                        [(v,_)] -> Just $ BVValue { bvValueWidth = len
                                                  , bvValueValue = v }
                        _ -> Nothing
      _ -> Nothing
lispToValue _ sort (L.List [L.Symbol "_",L.Symbol val,L.Number (L.I bits)])
  = case sort of
  Nothing -> result
  Just (Fix (BVSort {})) -> result
  Just _ -> Nothing
  where
    result = case T.unpack val of
      'b':'v':num -> Just $ BVValue { bvValueWidth = fromIntegral bits
                                    , bvValueValue = read num }
      _ -> Nothing
lispToValue _ _ _ = Nothing

lispToValue' :: DataTypeInfo -> Maybe Sort -> L.Lisp -> Maybe Value
lispToValue' dts sort l = case lispToValue dts sort l of
  Just res -> Just res
  Nothing -> case sort of
    Just (Fix (NamedSort name argSorts)) -> lispToConstr dts (Just (name,argSorts)) l
    _ -> error $ "smtlib2: Cannot translate "++show l++" to value"

lispToConstr :: DataTypeInfo -> Maybe (String,[Sort]) -> L.Lisp -> Maybe Value
lispToConstr dts sort (L.List [L.Symbol "as",
                               expr,
                               dt]) = do
  sort' <- lispToSort dt
  case sort' of
   Fix (NamedSort name args) -> lispToConstr dts (Just (name,args)) expr
lispToConstr dts sort (L.Symbol n)
  = let rn = T.unpack n
    in case Map.lookup rn (constructors dts) of
      Just (constr,dt,coll)
        -> Just (ConstrValue rn [] (case sort of
                                       Just s -> Just s
                                       Nothing -> Nothing))
lispToConstr dts sort (L.List ((L.Symbol name):args)) = do
  let (constr,dt,coll) = case Map.lookup (T.unpack name) (constructors dts) of
        Just r -> r
        Nothing -> error $ "smtlib2: Can't find constructor for "++(T.unpack name)
      argSorts = fmap (\field -> getArgSort (fieldSort field)
                      ) (conFields constr)
  args' <- mapM (\(l,s) -> lispToValue' dts s l) (zip args argSorts)
  return $ ConstrValue (T.unpack name) args'
    (case sort of
        Just sort' -> Just sort'
        Nothing -> Nothing)
  where
    getArgSort (Fix (ArgumentSort n)) = case sort of
      Just (_,args) -> Just $ args `genericIndex` n
      _ -> Nothing
    getArgSort (Fix (NormalSort s)) = case s of
      BoolSort -> Just $ Fix BoolSort
      IntSort -> Just $ Fix IntSort
      RealSort -> Just $ Fix RealSort
      BVSort w u -> Just $ Fix (BVSort w u)
      ArraySort idx v -> do
        idx' <- mapM getArgSort idx
        v' <- getArgSort v
        return $ Fix $ ArraySort idx' v'
      NamedSort name args -> do
        args' <- mapM getArgSort args
        return $ Fix $ NamedSort name args'
lispToConstr _ _ _ = Nothing

valueToLisp :: DataTypeInfo -> Value -> L.Lisp
valueToLisp _ (BoolValue False) = L.Symbol "false"
valueToLisp _ (BoolValue True) = L.Symbol "true"
valueToLisp _ (IntValue i) = if i<0
                             then L.List [L.Symbol "-"
                                         ,L.Number $ L.I (abs i)]
                             else L.Number $ L.I i
valueToLisp _ (RealValue i)
  = let res = L.List [L.Symbol "/"
                     ,L.Number $ L.I (abs $ numerator i)
                     ,L.Number $ L.I $ denominator i]
    in if i<0
       then L.List [L.Symbol "-"
                   ,res]
       else res
valueToLisp _ (BVValue { bvValueWidth = w
                       , bvValueValue = v })
  = L.List [L.Symbol "_"
           ,L.Symbol $ T.pack $ "bv"++(if v>=0
                                       then show v
                                       else show (2^w + v))
           ,L.Number $ L.I w]
valueToLisp dts (ConstrValue name vals sort)
  = let constr = case sort of
          Just (tp,sort') ->  L.List [L.Symbol "as"
                                     ,L.Symbol $ T.pack name
                                     ,if null sort'
                                      then L.Symbol $ T.pack tp
                                      else L.List $ [L.Symbol $ T.pack tp]++(fmap sortToLisp sort')]
          Nothing -> L.Symbol $ T.pack name
    in case vals of
      [] -> constr
      _ -> L.List (constr:(fmap (valueToLisp dts) vals))

-- | Parse a lisp expression into an SMT expression.
--   Since we cannot know what type the expression might have, we pass a
--   general function which may take any SMT expression and produce the desired
--   result.
lispToExpr :: FunctionParser -- ^ The parser to use for function symbols
           -> (T.Text -> Maybe (SMTExpr Untyped)) -- ^ How to handle variable names
              -> DataTypeInfo -- ^ Information about declared data types
              -> (forall a. SMTType a => SMTExpr a -> b) -- ^ A function to apply to the resulting SMT expression
              -> Maybe Sort -- ^ If you know the sort of the expression, you can pass it here.
              -> Integer -- ^ The current quantification level
              -> L.Lisp -- ^ The lisp expression to parse
              -> Maybe b
lispToExpr = lispToExprWith lispToExpr

lispToExprWith :: (forall b. FunctionParser
                   -> (T.Text -> Maybe (SMTExpr Untyped))
                   -> DataTypeInfo
                   -> (forall a. SMTType a => SMTExpr a -> b)
                   -> Maybe Sort
                   -> Integer
                   -> L.Lisp -> Maybe b) -- ^ Recursive descend function
                  -> FunctionParser -- ^ The parser to use for function symbols
                  -> (T.Text -> Maybe (SMTExpr Untyped)) -- ^ How to handle variable names
                  -> DataTypeInfo -- ^ Information about declared data types
                  -> (forall a. SMTType a => SMTExpr a -> b) -- ^ A function to apply to the resulting SMT expression
                  -> Maybe Sort -- ^ If you know the sort of the expression, you can pass it here.
                  -> Integer -- ^ The current quantification level
                  -> L.Lisp -- ^ The lisp expression to parse
                  -> Maybe b
lispToExprWith recp fun bound dts f expected lvl l = case lispToValue dts expected l of
  Just val -> valueToHaskell dts
              (\_ (val'::t) ann
               -> asValueType (undefined::t) ann $
                  \(_::tv) ann' -> case cast (val',ann') of
                    Just (rval::tv,rann::SMTAnnotation tv) -> f $ Const rval rann
              ) expected val
  Nothing -> case preprocessHack l of
    L.Symbol name -> case bound name of
      Nothing -> Nothing
      Just subst -> entype (\expr -> Just $ f expr) subst
    L.List [L.Symbol "forall",L.List args',body]
      -> fmap f $ quantToExpr recp Forall fun bound dts args' lvl body
    L.List [L.Symbol "exists",L.List args',body]
      -> fmap f $ quantToExpr recp Exists fun bound dts args' lvl body
    L.List [L.Symbol "let",L.List args',body]
      -> parseLet recp fun bound dts f expected args' lvl body
    L.List [L.Symbol "_",L.Symbol "as-array",fsym]
      -> case parseFun fun fsym fun dts of
      Nothing -> Nothing
      Just (DefinedParser arg_sort _ parse)
        -> parse $ \(rfun :: SMTFunction arg res) -> case getArgAnnotation (undefined::arg) arg_sort of
        (ann,[]) -> f (AsArray rfun ann)
        (_,_) -> error "smtlib2: Arguments not wholy parsed."
      Just _ -> error "smtlib2: as-array can't handle overloaded functions."
    L.List (fsym:args') -> case parseFun fun fsym fun dts of
      Nothing -> Nothing
      Just (OverloadedParser constr derive parse)
        -> do
        nargs <- lispToExprs constr args'
        let arg_tps = fmap (entype $ \(expr::SMTExpr t)
                                     -> getSort (undefined::t) (extractAnnotation expr)
                           ) nargs
        parse arg_tps
          (case derive arg_tps of
              Nothing -> case expected of
                Nothing -> error $ "smtlib2: Couldn't infer return type of "++show l
                Just s -> s
              Just s -> s) $
          \(rfun :: SMTFunction arg res)
          -> case (do
                      let (ann,[]) = getArgAnnotation (undefined::arg) arg_tps
                      (rargs,rest) <- toArgs ann nargs
                      case rest of
                        [] -> Just $ App rfun rargs
                        _ -> Nothing) of
               Just e -> f e
               Nothing -> error $ "smtlib2: Wrong arguments for function "++show fsym++": "++show arg_tps++" (Expected: "++show args'++")."
      Just (DefinedParser arg_tps _ parse) -> do
        nargs <- mapM (\(el,tp) -> recp fun bound dts mkUntyped (Just tp) lvl el)
                 (zip args' arg_tps)
        parse $ \(rfun :: SMTFunction arg res)
                -> case (do
                            let (ann,[]) = getArgAnnotation (undefined::arg) arg_tps
                            (rargs,rest) <- toArgs ann nargs
                            case rest of
                              [] -> Just $ App rfun rargs
                              _ -> Nothing) of
                     Just e -> f e
                     Nothing -> error $ "smtlib2: Wrong arguments for function "++show fsym++" (Expected: "++show arg_tps++")"
    _ -> Nothing
  where
    lispToExprs constr exprs = do
      res <- mapM (\arg -> recp fun bound dts mkUntyped Nothing lvl arg) exprs
      let sorts = fmap (entype exprSort) res
      if constr sorts
        then return res
        else (case generalizeSorts sorts of
                 Just sorts' -> mapM (\(arg,sort') -> recp fun bound dts mkUntyped (Just sort') lvl arg) (zip exprs sorts')
                 Nothing -> return res)
    preprocessHack (L.List ((L.Symbol "concat"):args)) = foldl1 (\expr arg -> L.List [L.Symbol "concat",expr,arg]) args
    preprocessHack x = x

generalizeSort :: Sort -> Maybe Sort
generalizeSort (Fix (BVSort i False)) = Just $ Fix $ BVSort i True
generalizeSort (Fix (ArraySort idx cont)) = case generalizeSorts idx of
  Just idx' -> case generalizeSort cont of
    Just cont' -> Just $ Fix $ ArraySort idx' cont'
    Nothing -> Just $ Fix $ ArraySort idx' cont
  Nothing -> case generalizeSort cont of
    Just cont' -> Just $ Fix $ ArraySort idx cont'
    Nothing -> Nothing
generalizeSort (Fix (NamedSort n args)) = case generalizeSorts args of
  Nothing -> Nothing
  Just args' -> Just $ Fix $ NamedSort n args'
generalizeSort _ = Nothing

generalizeSorts :: [Sort] -> Maybe [Sort]
generalizeSorts [] = Nothing
generalizeSorts (x:xs) = case generalizeSort x of
  Nothing -> case generalizeSorts xs of
    Just xs' -> Just $ x:xs'
    Nothing -> Nothing
  Just x' -> case generalizeSorts xs of
    Nothing -> Just $ x':xs
    Just xs' -> Just $ x':xs'

exprSort :: SMTType a => SMTExpr a -> Sort
exprSort (expr::SMTExpr a) = getSort (undefined::a) (extractAnnotation expr)

quantToExpr :: (forall b. FunctionParser
                -> (T.Text -> Maybe (SMTExpr Untyped))
                -> DataTypeInfo
                -> (forall a. SMTType a => SMTExpr a -> b)
                -> Maybe Sort
                -> Integer
                -> L.Lisp -> Maybe b) -- ^ Recursive descend function
            -> (Integer -> [ProxyArg] -> SMTExpr Bool -> SMTExpr Bool)
            -> FunctionParser
            -> (T.Text -> Maybe (SMTExpr Untyped))
            -> DataTypeInfo
            -> [L.Lisp] -> Integer -> L.Lisp -> Maybe (SMTExpr Bool)
quantToExpr recp con fun bound dts args lvl body = do
  argLst <- mapM (\el -> case el of
                   L.List [L.Symbol name,tp] -> do
                     sort <- lispToSort tp
                     return (name,withSort dts sort ProxyArg)
                   _ -> Nothing
                 ) args
  let argMp = Map.fromList [ (name,(i,tp))
                           | (i,(name,tp)) <- Prelude.zip [0..] argLst ]
      bound' name = case Map.lookup name argMp of
        Just (idx,tp) -> Just (QVar lvl idx tp)
        Nothing -> bound name
  recp fun bound' dts
    (\body' -> case cast body' of
      Just body'' -> con lvl (fmap snd argLst) body''
    ) (Just $ Fix BoolSort) (lvl+1) body

parseLet :: (forall b. FunctionParser
             -> (T.Text -> Maybe (SMTExpr Untyped))
             -> DataTypeInfo
             -> (forall a. SMTType a => SMTExpr a -> b)
             -> Maybe Sort
             -> Integer
             -> L.Lisp -> Maybe b) -- ^ Recursive descend function
         -> FunctionParser
         -> (T.Text -> Maybe (SMTExpr Untyped))
         -> DataTypeInfo
         -> (forall a. SMTType a => SMTExpr a -> b)
         -> Maybe Sort
         -> [L.Lisp] -> Integer -> L.Lisp -> Maybe b
parseLet recp fun bound dts app expected args lvl body = do
  argLst <- mapM (\el -> case el of
                   L.List [L.Symbol name,expr] -> do
                     expr' <- recp fun bound dts UntypedExpr Nothing (lvl+1) expr
                     return (name,expr')
                   _ -> Nothing
                 ) args
  let argMp = Map.fromList [ (name,(i,extractAnnotation expr))
                           | (i,(name,expr)) <- Prelude.zip [0..] argLst ]
      bound' name = case Map.lookup name argMp of
        Just (idx,tp) -> Just (QVar lvl idx tp)
        Nothing -> bound name
  recp fun bound' dts
    (\body' -> app (Let lvl (fmap snd argLst) body')
    ) expected (lvl+1) body

withFirstArgSort :: DataTypeInfo -> L.Lisp -> [Sort] -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withFirstArgSort dts _ (s:rest) f = case s of
  Fix (BVSort i False) -> if any (\sort -> case sort of
                                     Fix (BVSort _ True) -> True
                                     _ -> False) rest
                          then withSort dts (Fix $ BVSort i True) f
                          else withSort dts s f
  _ -> withSort dts s f
withFirstArgSort _ sym [] _ = error $ "smtlib2: Function "++show sym++" needs at least one argument."

nameParser :: L.Lisp -> FunctionParser' -> FunctionParser
nameParser name sub = FunctionParser (\sym _ _ -> if sym==name
                                                  then Just sub
                                                  else Nothing)

allEqConstraint :: [Sort] -> Bool
allEqConstraint (x:xs) = all (==x) xs
allEqConstraint [] = True

simpleParser :: (Liftable arg,SMTType res,Unit (ArgAnnotation arg),Unit (SMTAnnotation res))
                => SMTFunction arg res -> FunctionParser
simpleParser fun
  = let fsym = functionGetSymbol (error "smtlib2: Don't lookup names in simpleParser") fun unit
        (uargs,ures) = getFunUndef fun
    in nameParser fsym (DefinedParser
                        (getSorts uargs unit)
                        (getSort ures unit)
                        $ \f -> Just $ f fun)

-- | A parser for all available SMT logics.
commonFunctions :: FunctionParser
commonFunctions = mconcat
                  [fieldParser
                  ,constructorParser
                  ,eqParser
                  ,mapParser
                  ,ordOpParser
                  ,arithOpParser
                  ,minusParser
                  ,intArithParser
                  ,divideParser
                  ,absParser
                  ,logicParser
                  ,iteParser
                  ,distinctParser
                  ,toRealParser
                  ,toIntParser
                  ,bvCompParser
                  ,bvBinOpParser
                  ,bvUnOpParser
                  ,selectParser
                  ,storeParser
                  ,constArrayParser
                  ,concatParser
                  ,extractParser
                  ,sigParser
                  ,divisibleParser]

eqParser,
  mapParser,
  ordOpParser,
  arithOpParser,
  minusParser,
  intArithParser,
  divideParser,
  absParser,
  logicParser,
  iteParser,
  distinctParser,
  toRealParser,
  toIntParser,
  bvCompParser,
  bvBinOpParser,
  bvUnOpParser,
  selectParser,
  storeParser,
  constArrayParser,
  concatParser,
  extractParser,
  sigParser,
  divisibleParser :: FunctionParser
eqParser = FunctionParser v
  where
    v (L.Symbol "=") rec dts = Just $ OverloadedParser allEqConstraint
                               (const $ Just $ getSort (undefined::Bool) ()) $
                         \sort_arg _ f
                           -> withFirstArgSort dts "=" sort_arg $
                              \(_::t) _ -> Just $ f (SMTEq :: SMTFunction [SMTExpr t] Bool)
    v _ _ _ = Nothing

mapParser = FunctionParser v
  where
    v (L.List [L.Symbol "_"
              ,L.Symbol "map"
              ,fun]) rec dts
#ifdef SMTLIB2_WITH_CONSTRAINTS
      = case parseFun rec fun rec dts of
        Nothing -> Nothing :: Maybe FunctionParser'
        Just (DefinedParser _ ret_sig parse)
          -> Just $ OverloadedParser
            { sortConstraint = const True
            , deriveRetSort = \arg -> case arg of
                 Fix (ArraySort i _):_ -> Just (Fix $ ArraySort i ret_sig)
                 _ -> error "smtlib2: map function must have arrays as arguments."
            , parseOverloaded = \_ ret f
                                 -> let idx_sort = case ret of
                                          Fix (ArraySort i _) -> i
                                          _ -> error "smtlib2: map function must have arrays as return type."
                                    in parse $ \(fun' :: SMTFunction arg res)
                                               -> withSorts dts idx_sort $
                                                  \(_::i) _
                                                  -> let res = SMTMap fun' :: SMTFunction (Lifted arg i) (SMTArray i res)
                                                     in case getConstraint (Proxy :: Proxy (arg,i)) of
                                                       Dict -> f res
            }
        Just _ -> error "smtlib2: map function can't handle overloaded functions."
#else
      = Just $ error "smtlib2: Compile smtlib2 with -fWithConstraints to enable parsing of map functions"
#endif
    v _ _ _ = Nothing

ordOpParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol ">=" -> p sym Ge dts
  L.Symbol ">" -> p sym Gt dts
  L.Symbol "<=" -> p sym Le dts
  L.Symbol "<" -> p sym Lt dts
  _ -> Nothing
  where
    p :: L.Lisp -> SMTOrdOp -> DataTypeInfo -> Maybe FunctionParser'
    p sym op dts = Just $ OverloadedParser allEqConstraint (const $ Just $ getSort (undefined::Bool) ()) $
                   \[sort_arg,_] _ f -> withNumSort dts sort_arg $
                                        \(_::t) _
                                         -> f (SMTOrd op :: SMTFunction (SMTExpr t,SMTExpr t) Bool)

arithOpParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "+" -> Just $ OverloadedParser allEqConstraint (\sorts -> Just (head sorts)) $
                  \_ sort_ret f
                  -> withNumSort dts sort_ret $
                     \(_::t) _
                     -> f (SMTArith Plus::SMTFunction [SMTExpr t] t)
  L.Symbol "*" -> Just $ OverloadedParser allEqConstraint (\sorts -> Just (head sorts)) $
                  \_ sort_ret f
                  -> withNumSort dts sort_ret $
                     \(_::t) _
                     -> f (SMTArith Mult::SMTFunction [SMTExpr t] t)
  _ -> Nothing

minusParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "-" -> Just $ OverloadedParser allEqConstraint (\sorts -> Just (head sorts)) $
                  \sort_arg _ f -> case sort_arg of
                    [] -> error "smtlib2: minus function needs at least one argument"
                    [s] -> withNumSort dts s $ \(_::t) _ -> f (SMTNeg::SMTFunction (SMTExpr t) t)
                    (s:_) -> withNumSort dts s $ \(_::t) _ -> f (SMTMinus::SMTFunction (SMTExpr t,SMTExpr t) t)
  _ -> Nothing

intArithParser = mconcat [simpleParser (SMTIntArith Div)
                         ,simpleParser (SMTIntArith Mod)
                         ,simpleParser (SMTIntArith Rem)]

divideParser = simpleParser SMTDivide

absParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "abs" -> Just $ OverloadedParser (const True) (\sorts -> Just $ head sorts) $
                    \_ sort_ret f
                    -> withNumSort dts sort_ret $ \(_::t) _ -> f (SMTAbs::SMTFunction (SMTExpr t) t)
  _ -> Nothing

logicParser = mconcat $
              (simpleParser SMTNot)
              :[ nameParser (L.Symbol name)
                 (OverloadedParser (const True)
                  (const $ Just $ getSort (undefined::Bool) ())
                  $ \_ _ f -> Just $ f (SMTLogic p))
               | (name,p) <- [("and",And),("or",Or),("xor",XOr),("=>",Implies)]]

distinctParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "distinct" -> Just $ OverloadedParser allEqConstraint
                         (const $ Just $ getSort (undefined::Bool) ()) $
                         \sort_arg _ f
                         -> withFirstArgSort dts "distinct" sort_arg $
                            \(_::t) _ -> Just $ f (SMTDistinct::SMTFunction [SMTExpr t] Bool)
  _ -> Nothing

toRealParser = simpleParser SMTToReal
toIntParser = simpleParser SMTToInt

iteParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "ite" -> Just $ OverloadedParser (\sorts -> case sorts of
                                                [_,s1,s2] -> s1==s2
                                                _ -> False)
                    (\sorts -> case sorts of
                        [_,s,_] -> Just s
                        _ -> error $ "smtlib2: Wrong number of arguments to ite (expected 3, got "++show (length sorts)++".") $
                    \_ sort_ret f
                    -> withSort dts sort_ret $
                       \(_::t) _ -> Just $ f (SMTITE :: SMTFunction (SMTExpr Bool,SMTExpr t,SMTExpr t) t)
  _ -> Nothing

bvCompParser = FunctionParser $ \sym _ _ -> case sym of
  L.Symbol "bvule" -> p BVULE
  L.Symbol "bvult" -> p BVULT
  L.Symbol "bvuge" -> p BVUGE
  L.Symbol "bvugt" -> p BVSLE
  L.Symbol "bvsle" -> p BVSLE
  L.Symbol "bvslt" -> p BVSLT
  L.Symbol "bvsge" -> p BVSGE
  L.Symbol "bvsgt" -> p BVSGT
  _ -> Nothing
  where
    p :: SMTBVCompOp -> Maybe FunctionParser'
    p op = Just $ OverloadedParser allEqConstraint (const $ Just $ getSort (undefined::Bool) ()) $
           \sort_arg _ f -> case sort_arg of
             (Fix (BVSort i False):_)
               -> reifyNat i $ \(_::Proxy n)
                               -> Just $ f (SMTBVComp op::SMTFunction (SMTExpr (BitVector (BVTyped n)),
                                                                       SMTExpr (BitVector (BVTyped n))) Bool)
             (Fix (BVSort _ True):_)
               -> Just $ f (SMTBVComp op::SMTFunction (SMTExpr (BitVector BVUntyped),
                                                       SMTExpr (BitVector BVUntyped)) Bool)
             _ -> error "smtlib2: Bitvector comparision needs bitvector arguments."

bvBinOpParser = FunctionParser $ \sym _ _ -> case sym of
  L.Symbol "bvadd" -> p BVAdd
  L.Symbol "bvsub" -> p BVSub
  L.Symbol "bvmul" -> p BVMul
  L.Symbol "bvurem" -> p BVURem
  L.Symbol "bvsrem" -> p BVSRem
  L.Symbol "bvudiv" -> p BVUDiv
  L.Symbol "bvsdiv" -> p BVSDiv
  L.Symbol "bvshl" -> p BVSHL
  L.Symbol "bvlshr" -> p BVLSHR
  L.Symbol "bvashr" -> p BVASHR
  L.Symbol "bvxor" -> p BVXor
  L.Symbol "bvand" -> p BVAnd
  L.Symbol "bvor" -> p BVOr
  _ -> Nothing
  where
    p :: SMTBVBinOp -> Maybe FunctionParser'
    p op = Just $ OverloadedParser allEqConstraint (Just . head) $
           \_ sort_ret f -> case sort_ret of
              Fix (BVSort i False)
                -> reifyNat i (\(_::Proxy n)
                               -> Just $ f (SMTBVBin op::SMTFunction (SMTExpr (BitVector (BVTyped n)),
                                                                      SMTExpr (BitVector (BVTyped n)))
                                                         (BitVector (BVTyped n))))
              Fix (BVSort _ True)
                -> Just $ f (SMTBVBin op::SMTFunction (SMTExpr (BitVector BVUntyped),
                                                       SMTExpr (BitVector BVUntyped))
                                          (BitVector BVUntyped))
              _ -> Nothing

bvUnOpParser = FunctionParser $ \sym _ _ -> case sym of
  L.Symbol "bvnot"
    -> Just $ OverloadedParser (const True) (Just . head) $
       \_ sort_ret f -> case sort_ret of
        Fix (BVSort i False)
          -> reifyNat i $ \(_::Proxy n)
                          -> Just $ f (SMTBVUn BVNot::SMTFunction (SMTExpr (BitVector (BVTyped n)))
                                                      (BitVector (BVTyped n)))
        Fix (BVSort _ True) -> Just $ f (SMTBVUn BVNot::SMTFunction (SMTExpr (BitVector BVUntyped))
                                                                     (BitVector BVUntyped))
        _ -> Nothing
  L.Symbol "bvneg"
    -> Just $ OverloadedParser (const True) (Just . head) $
      \_ sort_ret f -> case sort_ret of
        Fix (BVSort i False)
          -> reifyNat i $ \(_::Proxy n)
                          -> Just $ f (SMTBVUn BVNeg::SMTFunction (SMTExpr (BitVector (BVTyped n)))
                                                      (BitVector (BVTyped n)))
        Fix (BVSort _ True) -> Just $ f (SMTBVUn BVNeg::SMTFunction (SMTExpr (BitVector BVUntyped))
                                                        (BitVector BVUntyped))
        _ -> Nothing
  _ -> Nothing

selectParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "select"
    -> Just $ OverloadedParser (const True)
       (\sort_arg -> case sort_arg of
           (Fix (ArraySort _ vsort):_) -> Just vsort
           _ -> error $ "smtlib2: Wrong arguments for select function ("++show sort_arg++").") $
       \sort_arg sort_ret f -> case sort_arg of
         (Fix (ArraySort isort1 _):_)
           -> withSorts dts isort1 $
              \(_::i) _ -> withSort dts sort_ret $
                           \(_::v) _ -> Just $ f (SMTSelect::SMTFunction (SMTExpr (SMTArray i v),i) v)
         _ -> error $ "smtlib2: Wrong arguments for select function ("++show sort_arg++")."
  _ -> Nothing

storeParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "store"
    -> Just $ OverloadedParser (\tps -> case tps of
                                   (Fix (ArraySort idx res)):tps' -> checkArraySort idx res tps'
                                   _ -> False)
       (\sort_arg -> case sort_arg of
           s:_ -> Just s
           _ -> error "smtlib2: Wrong arguments for store function.") $
       \_ sort_ret f -> case sort_ret of
         Fix (ArraySort idx val)
           -> withArraySort dts idx val $
              \(_::SMTArray i v) _
              -> Just $ f (SMTStore::SMTFunction (SMTExpr (SMTArray i v),i,SMTExpr v) (SMTArray i v))
         _ -> error "smtlib2: Wrong return type for store function."
  _ -> Nothing
  where
    checkArraySort [] cont [tp] = cont==tp
    checkArraySort (arg:args) cont (tp:tps) = arg==tp && checkArraySort args cont tps
    checkArraySort _ _ _ = False

constArrayParser = FunctionParser g
  where
    g (L.List [L.Symbol "as"
              ,L.Symbol "const"
              ,s]) _ dts
      = case lispToSort s of
        Just rsort@(Fix (ArraySort idx val))
          -> Just $ DefinedParser [val] rsort $
             \f -> withArraySort dts idx val $
                   \(_::SMTArray i v) (i_ann,_)
                   -> Just $ f (SMTConstArray i_ann::SMTFunction (SMTExpr v) (SMTArray i v))
        _ -> Nothing
    g _ _ _ = Nothing

concatParser = nameParser (L.Symbol "concat")
               (OverloadedParser (const True)
                (\args' -> let lenSum = sum $ fmap (\(Fix (BVSort i _)) -> i) args'
                               untypedRes = any (\(Fix (BVSort _ isUntyped)) -> isUntyped) args'
                           in Just $ Fix $ BVSort lenSum untypedRes)
                (\sort_arg _ f -> case sort_arg of
                    [Fix (BVSort i1 False),Fix (BVSort i2 False)]
                      -> reifySum i1 i2 $
                         \(_::Proxy n1) (_::Proxy n2) _
                         -> Just $ f (SMTConcat::SMTFunction (SMTExpr (BitVector (BVTyped n1)),
                                                              SMTExpr (BitVector (BVTyped n2)))
                                                 (BitVector (ConcatResult (BVTyped n1) (BVTyped n2))))
                    [Fix (BVSort _ True),Fix (BVSort i2 False)]
                      -> reifyNat i2 $
                        \(_::Proxy n2)
                          -> Just $ f (SMTConcat::SMTFunction (SMTExpr (BitVector BVUntyped),
                                                               SMTExpr (BitVector (BVTyped n2)))
                                                  (BitVector BVUntyped))
                    [Fix (BVSort i1 False),Fix (BVSort _ True)]
                      -> reifyNat i1 $
                        \(_::Proxy n1)
                          -> Just $ f (SMTConcat::SMTFunction (SMTExpr (BitVector (BVTyped n1)),
                                                               SMTExpr (BitVector BVUntyped))
                                                  (BitVector BVUntyped))
                    [Fix (BVSort _ True),Fix (BVSort _ True)]
                      -> Just $ f (SMTConcat::SMTFunction (SMTExpr (BitVector BVUntyped),SMTExpr (BitVector BVUntyped)) (BitVector BVUntyped))
                    _ -> Nothing))

extractParser = FunctionParser g
  where
    g (L.List [L.Symbol "_"
              ,L.Symbol "extract"
              ,L.Number (L.I u)
              ,L.Number (L.I l)]) _ _
      = Just $ OverloadedParser (const True)
        (\args' -> case args' of
            [Fix (BVSort t untyped)] -> if u < t && l >= 0 && l <= u
                                        then Just $ Fix (BVSort (u-l+1) untyped)
                                        else error "smtlib2: Invalid parameters for extract."
            _ -> error "smtlib2: Invalid parameters for extract.")
        (\sort_arg sort_ret f -> case sort_arg of
            [Fix (BVSort t untA)] -> case sort_ret of
              Fix (BVSort r untR)
                -> if r+l == u+1 && (untR == untA)
                   then reifyNat l $
                        \(_::Proxy start)
                        -> reifyNat (u-l+1) $
                           \(_::Proxy len)
                           -> if not untR
                              then reifyNat t $
                                   \(_::Proxy tp)
                                   -> Just $ f (SMTExtract (Proxy::Proxy start) (Proxy::Proxy len)
                                                ::SMTFunction (SMTExpr (BitVector (BVTyped tp)))
                                                  (BitVector (BVTyped len)))
                              else Just $ f (SMTExtract (Proxy::Proxy start) (Proxy::Proxy len)
                                             ::SMTFunction (SMTExpr (BitVector BVUntyped))
                                               (BitVector (BVTyped len)))
                   else error "smtlib2: Invalid parameters for extract."
              _ -> error "smtlib2: Wrong return type for extract."
            _ -> error "smtlib2: Wrong argument type for extract.")
    g _ _ _ = Nothing

sigParser = FunctionParser g
  where
    g (L.List [fsym,L.List sig,ret]) r dts = do
      rsig <- mapM lispToSort sig
      rret <- lispToSort ret
      parser <- parseFun r fsym r dts
      return $ DefinedParser rsig rret $
        \f -> case parser of
          OverloadedParser _ _ parse -> parse rsig rret f
          DefinedParser _ _ parse -> parse f
    g _ _ _ = Nothing

divisibleParser = FunctionParser g
  where
    g (L.List [L.Symbol "_",L.Symbol "divisible",L.Number (L.I n)]) _ _
      = Just $ DefinedParser { definedArgSig = [Fix IntSort]
                             , definedRetSig = Fix BoolSort
                             , parseDefined = \f -> Just $ f (SMTDivisible n) }
    g _ _ _ = Nothing

constructorParser :: FunctionParser
constructorParser
  = FunctionParser $
    \sym _ dts -> case sym of
        L.Symbol name -> case Map.lookup (T.unpack name) (constructors dts) of
          Nothing -> Nothing
          Just (con,dt,struc) -> case argCount struc of
            0 -> let argSorts = [ runIdentity $
                                  argumentSortToSort
                                  (error $ "smtlib2: Internal error: Constructor "++conName con
                                   ++" of data type "++dataTypeName dt
                                   ++" is declared as having no arguments, but it uses them")
                                  (fieldSort field)
                                | field <- conFields con ]
                     resSort = Fix $ NamedSort (dataTypeName dt) []
                 in Just $ DefinedParser { definedArgSig = argSorts
                                         , definedRetSig = resSort
                                         , parseDefined = \f -> withSort dts resSort
                                                                (\(uret::ret) ann_ret
                                                                 -> withSorts dts argSorts
                                                                    (\(_::arg) ann
                                                                     -> Just $ f (SMTConstructor (Constructor (getProxyArgs uret ann_ret) dt con::Constructor arg ret))))
                                         }
            _ -> Just $ OverloadedParser { sortConstraint = \_ -> True
                                         , deriveRetSort = infer
                                         , parseOverloaded = parse
                                         }
              where
                infer tps = let inf = foldl (\cinf (x,y) -> inferSorts x y cinf)
                                      Map.empty (zip (fmap fieldSort (conFields con)) tps)
                            in argumentSortToSort (\i -> Map.lookup i inf)
                               (Fix $ NormalSort (NamedSort (dataTypeName dt)
                                                  [Fix $ ArgumentSort i
                                                  | i <- [0..(argCount struc)-1]]))
                parse :: [Sort] -> Sort
                      -> (forall arg res.
                          (Liftable arg,SMTType res)
                          => SMTFunction arg res -> a) -> Maybe a
                parse tps rtp app
                  = withSorts dts tps $
                    \(_::arg') _
                    -> withSort dts rtp $
                       \(_::res') _
                        -> Just $ app (SMTConstructor
                                       (Constructor proxies dt con
                                        ::Constructor arg' res'))
                  where
                    proxies = case rtp of
                      Fix (NamedSort _ tps) -> fmap (\tp -> withSort dts tp ProxyArg) tps
        _ -> Nothing

fieldParser :: FunctionParser
fieldParser
  = FunctionParser $
    \sym _ dts -> case sym of
    L.Symbol name -> case Map.lookup (T.unpack name) (fields dts) of
      Nothing -> Nothing
      Just (field,constr,dt,struc)
        -> Just $ OverloadedParser { sortConstraint = \_ -> True
                                   , deriveRetSort = infer
                                   , parseOverloaded = parse }
        where
          infer [Fix (NamedSort _ tps)]
            = let mp = Map.fromList (zip [0..] tps)
              in argumentSortToSort (\i -> Map.lookup i mp) (fieldSort field)
          parse :: [Sort] -> Sort
                -> (forall arg res.
                    (Liftable arg,SMTType res)
                    => SMTFunction arg res -> a) -> Maybe a
          parse [Fix (NamedSort _ tps)] rtp app
            = dataTypeGetUndefined dt proxies $
              \(u::t) _ -> withSort dts rtp $
                           \(_::f) _
                           -> Just $ app (SMTFieldSel
                                          (Field proxies dt constr field
                                           :: Field t f))
            where
              proxies = fmap (\tp -> withSort dts tp ProxyArg) tps
    _ -> Nothing

withPipe :: MonadIO m => String -> [String] -> SMT' m a -> m a
withPipe prog args act = do
  pipe <- liftIO $ createSMTPipe prog args
  withSMTBackend' pipe True act

tacticToLisp :: Tactic -> L.Lisp
tacticToLisp Skip = L.Symbol "skip"
tacticToLisp (AndThen ts) = L.List ((L.Symbol "and-then"):fmap tacticToLisp ts)
tacticToLisp (OrElse ts) = L.List ((L.Symbol "or-else"):fmap tacticToLisp ts)
tacticToLisp (ParOr ts) = L.List ((L.Symbol "par-or"):fmap tacticToLisp ts)
tacticToLisp (ParThen t1 t2) = L.List [L.Symbol "par-then"
                                      ,tacticToLisp t1
                                      ,tacticToLisp t2]
tacticToLisp (TryFor t n) = L.List [L.Symbol "try-for"
                                   ,tacticToLisp t
                                   ,L.Number $ L.I n]
tacticToLisp (If c t1 t2) = L.List [L.Symbol "if"
                                   ,probeToLisp c
                                   ,tacticToLisp t1
                                   ,tacticToLisp t2]
tacticToLisp (FailIf c) = L.List [L.Symbol "fail-if"
                                 ,probeToLisp c]
tacticToLisp (UsingParams (CustomTactic name) []) = L.Symbol (T.pack name)
tacticToLisp (UsingParams (CustomTactic name) pars)
  = L.List ([L.Symbol "using-params"
            ,L.Symbol $ T.pack name]++
            concat [ [L.Symbol (T.pack $ ':':pname)
                     ,case par of
                         ParBool True -> L.Symbol "true"
                         ParBool False -> L.Symbol "false"
                         ParInt i -> L.Number $ L.I i
                         ParDouble i -> L.Number $ L.D i]
                     | (pname,par) <- pars ])

probeToLisp :: Probe a -> L.Lisp
probeToLisp (ProbeBoolConst b)
  = L.Symbol $ if b then "true" else "false"
probeToLisp (ProbeIntConst i)
  = L.Number $ L.I i
probeToLisp (ProbeAnd ps)
  = L.List ((L.Symbol "and"):
            fmap probeToLisp ps)
probeToLisp (ProbeOr ps)
  = L.List ((L.Symbol "or"):
            fmap probeToLisp ps)
probeToLisp (ProbeNot p)
  = L.List [L.Symbol "not"
           ,probeToLisp p]
probeToLisp (ProbeEq p1 p2)
  = L.List [L.Symbol "="
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp (ProbeCompare cmp p1 p2)
  = L.List [L.Symbol $ case cmp of
               Ge -> ">="
               Gt -> ">"
               Le -> "<="
               Lt -> "<"
           ,probeToLisp p1
           ,probeToLisp p2]
probeToLisp IsPB = L.Symbol "is-pb"
probeToLisp ArithMaxDeg = L.Symbol "arith-max-deg"
probeToLisp ArithAvgDeg = L.Symbol "arith-avg-deg"
probeToLisp ArithMaxBW = L.Symbol "arith-max-bw"
probeToLisp ArithAvgBW = L.Symbol "arith-avg-bw"
probeToLisp IsQFLIA = L.Symbol "is-qflia"
probeToLisp IsQFLRA = L.Symbol "is-qflra"
probeToLisp IsQFLIRA = L.Symbol "is-qflira"
probeToLisp IsILP = L.Symbol "is-ilp"
probeToLisp IsQFNIA = L.Symbol "is-qfnia"
probeToLisp IsQFNRA = L.Symbol "is-qfnra"
probeToLisp IsNIA = L.Symbol "is-nia"
probeToLisp IsNRA = L.Symbol "is-nra"
probeToLisp IsUnbounded = L.Symbol "is-unbounded"
probeToLisp Memory = L.Symbol "memory"
probeToLisp Depth = L.Symbol "depth"
probeToLisp Size = L.Symbol "size"
probeToLisp NumExprs = L.Symbol "num-exprs"
probeToLisp NumConsts = L.Symbol "num-consts"
probeToLisp NumBoolConsts = L.Symbol "num-bool-consts"
probeToLisp NumArithConsts = L.Symbol "num-arith-consts"
probeToLisp NumBVConsts = L.Symbol "num-bv-consts"
probeToLisp Strat.ProduceProofs = L.Symbol "produce-proofs"
probeToLisp ProduceModel = L.Symbol "produce-model"
probeToLisp Strat.ProduceUnsatCores = L.Symbol "produce-unsat-cores"
probeToLisp HasPatterns = L.Symbol "has-patterns"
probeToLisp IsPropositional = L.Symbol "is-propositional"
probeToLisp IsQFBV = L.Symbol "is-qfbv"
probeToLisp IsQFBVEQ = L.Symbol "is-qfbv-eq"

