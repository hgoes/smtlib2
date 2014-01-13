module Language.SMTLib2.Pipe (SMTPipe(),createSMTPipe,withPipe,exprToLisp,lispToExpr,commonFunctions,commonTheorems) where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
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

data SMTPipe = SMTPipe { channelIn :: Handle
                       , channelOut :: Handle
                       , processHandle :: ProcessHandle }

instance MonadIO m => SMTBackend SMTPipe m where
  smtGetInfo pipe SMTSolverName = do
    putRequest pipe $
      L.List [L.Symbol "get-info",L.Symbol ":name"]
    res <- parseResponse pipe
    case res of
      L.List [L.Symbol ":name",L.String name] -> return $ T.unpack name
      _ -> error "Invalid solver response to 'get-info' name query"
  smtGetInfo pipe SMTSolverVersion = do
    putRequest pipe $
      L.List [L.Symbol "get-info",L.Symbol ":version"]
    res <- parseResponse pipe
    case res of
      L.List [L.Symbol ":version",L.String name] -> return $ T.unpack name
      _ -> error "Invalid solver response to 'get-info' version query"

  smtAssert pipe expr interp = do
    let (lexpr,_) = exprToLisp expr 0
    case interp of
      Nothing -> putRequest pipe $
                 L.List [L.Symbol "assert"
                        ,lexpr]
      Just (InterpolationGroup gr)
        -> putRequest pipe $
           L.List [L.Symbol "assert"
                  ,L.List [L.Symbol "!"
                          ,lexpr
                          ,L.Symbol ":interpolation-group"
                          ,L.Symbol (T.pack gr)]]
  smtCheckSat pipe = do
    putRequest pipe $
      L.List [L.Symbol "check-sat"]
    res <- liftIO $ BS.hGetLine (channelOut pipe)
    case res of
      "sat" -> return True
      "sat\r" -> return True
      "unsat" -> return False
      "unsat\r" -> return False
      _ -> error $ "unknown check-sat response: "++show res
  smtDeclareDataTypes pipe dts = do
    let param x = L.Symbol $ T.pack $ "arg"++show x
    putRequest pipe $
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
  smtDeclareSort pipe name arity = putRequest pipe (L.List [L.Symbol "declare-sort",L.Symbol $ T.pack name,L.toLisp arity])
  smtDeclareFun pipe name tps rtp = do
    putRequest pipe $
      L.List [L.Symbol "declare-fun"
             ,L.Symbol $ T.pack name
             ,args (fmap sortToLisp tps)
             ,sortToLisp rtp
             ]
  smtDefineFun pipe name arg definition = do
    let ann = extractAnnotation definition
        retSort = getSort (getUndef definition) ann
    putRequest pipe $
      L.List [L.Symbol "define-fun"
             ,L.Symbol $ T.pack name
             ,args [ L.List [ L.Symbol $ T.pack n, sortToLisp tp ]
                   | (n,tp) <- arg ]
             ,sortToLisp retSort
             ,fst $ exprToLisp definition 0]
  smtComment pipe msg = do
    liftIO $ IO.hPutStr (channelIn pipe) $ Prelude.unlines (fmap (';':) (Prelude.lines msg))
  smtExit pipe = do
    putRequest pipe (L.List [L.Symbol "exit"])
    liftIO $ hClose (channelIn pipe)
    liftIO $ hClose (channelOut pipe)
    liftIO $ terminateProcess (processHandle pipe)
    _ <- liftIO $ waitForProcess (processHandle pipe)
    return ()
  smtGetInterpolant pipe mp dts grps = do
    putRequest pipe $ L.List [L.Symbol "get-interpolant"
                             ,L.List [ L.Symbol $ T.pack g | InterpolationGroup g <- grps ]
                             ]
    val <- parseResponse pipe
    case lispToExpr commonFunctions
         (\n -> Map.lookup (T.unpack n) mp) dts gcast (Just $ Fix BoolSort) val of
      Just (Just x) -> return x
      _ -> error $ "smtlib2: Failed to parse get-interpolant result: "++show val
  smtSetOption pipe opt = do
    putRequest pipe $ L.List $ [L.Symbol "set-option"]
      ++(case opt of
            PrintSuccess v -> [L.Symbol ":print-success"
                              ,L.Symbol $ if v then "true" else "false"]
            ProduceModels v -> [L.Symbol ":produce-models"
                               ,L.Symbol $ if v then "true" else "false"]
            ProduceProofs v -> [L.Symbol ":produce-proofs"
                               ,L.Symbol $ if v then "true" else "false"]
            ProduceUnsatCores v -> [L.Symbol ":produce-unsat-cores"
                                   ,L.Symbol $ if v then "true" else "false"]
            ProduceInterpolants v -> [L.Symbol ":produce-interpolants"
                                     ,L.Symbol $ if v then "true" else "false"]
        )
  smtSetLogic pipe name = do
    putRequest pipe $ L.List [L.Symbol "set-logic"
                             ,L.Symbol $ T.pack name]
  smtGetProof pipe mp dts = do
    putRequest pipe (L.List [L.Symbol "get-proof"])
    res <- parseResponse pipe
    let proof = case res of
          L.List items -> case findProof items of
            Nothing -> res
            Just p -> p
          _ -> res
    case lispToExpr (commonFunctions `mappend` commonTheorems)
         (\n -> Map.lookup (T.unpack n) mp)
         dts gcast (Just $ Fix BoolSort) proof of
      Just (Just x) -> return x
      _ -> error $ "smtlib2: Couldn't parse proof "++show res
    where
      findProof [] = Nothing
      findProof ((L.List [L.Symbol "proof",proof]):_) = Just proof
      findProof (x:xs) = findProof xs
  smtGetUnsatCore pipe = do
    putRequest pipe $
      L.List [L.Symbol "get-unsat-core"]
    res <- parseResponse pipe
    case res of
      L.List names -> return $
                      fmap (\name -> case name of
                               L.Symbol s -> T.unpack s
                               _ -> error $ "Language.SMTLib2.getUnsatCore: Unknown expression "
                                    ++show name++" in core list."
                           ) names
      _ -> error $ "Language.SMTLib2.getUnsatCore: Unknown response "++show res++" to query."
  smtSimplify pipe mp dts (expr::SMTExpr t) = do
    clearInput pipe
    let (lexpr,_) = exprToLisp expr 0
    putRequest pipe $ L.List [L.Symbol "simplify"
                             ,lexpr]
    val <- parseResponse pipe
    case lispToExpr commonFunctions
         (\n -> Map.lookup (T.unpack n) mp) dts gcast (Just $ getSort (undefined::t) (extractAnnotation expr)) val of
      Just (Just x) -> return x
      _ -> error $ "smtlib2: Failed to parse simplify result: "++show val
  smtPush pipe = putRequest pipe $ L.List [L.Symbol "push",L.toLisp (1::Integer)]
  smtPop pipe = putRequest pipe $ L.List [L.Symbol "pop",L.toLisp (1::Integer)]
  smtGetValue pipe mp dts (expr::SMTExpr t) = do
    let ann = extractAnnotation expr
        sort = getSort (undefined::t) ann
    clearInput pipe
    let (lexpr,_) = exprToLisp expr 0
    putRequest pipe $ L.List [L.Symbol "get-value"
                             ,L.List [lexpr]]
    val <- parseResponse pipe
    case val of
      L.List [L.List [_,res]]
        -> let res' = removeLets res
           in case lispToValue' dts (Just sort) res' of
             Just val' -> case unmangle val' ann of
               Just val'' -> return val''
               Nothing -> error $ "smtlib2: Failed to unmangle value "++show val'++" to type "++show (typeOf (undefined::t))
             Nothing -> error $ "smtlib2: Failed to parse value from "++show res
      _ -> error $ "smtlib2: Unexpected get-value response: "++show val

createSMTPipe :: String -> IO SMTPipe
createSMTPipe solver = do
  let cmd = CreateProcess { cmdspec = ShellCommand solver
                          , cwd = Nothing
                          , env = Nothing
                          , std_in = CreatePipe
                          , std_out = CreatePipe
                          , std_err = Inherit
                          , close_fds = False
                          , create_group = False
                          }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  return $ SMTPipe { channelIn = hin
                   , channelOut = hout
                   , processHandle = handle }

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

lispToSort :: L.Lisp -> Sort
lispToSort (L.Symbol "Bool") = Fix BoolSort
lispToSort (L.Symbol "Int") = Fix IntSort
lispToSort (L.Symbol "Real") = Fix RealSort
lispToSort (L.List [L.Symbol "_",
                    L.Symbol "BitVec",
                    L.Number (L.I n)])
  = Fix $ BVSort { bvSortWidth = n
                 , bvSortUntyped = False }
lispToSort (L.List (L.Symbol "Array":args))
  = Fix $ ArraySort (fmap lispToSort args') (lispToSort res)
  where
    (args',res) = splitLast args
    splitLast [s] = ([],s)
    splitLast (x:xs) = let (xs',l) = splitLast xs
                       in (x:xs',l)
lispToSort (L.Symbol x) = Fix $ NamedSort (T.unpack x) []
lispToSort (L.List ((L.Symbol x):args)) = Fix $ NamedSort (T.unpack x) (fmap lispToSort args)

exprToLisp :: SMTExpr t -> Integer -> (L.Lisp,Integer)
exprToLisp (Var name _) c = (L.Symbol $ T.pack name,c)
exprToLisp (Const x ann) c = (valueToLisp $ mangle x ann,c)
exprToLisp (AsArray f arg) c
  = let f' = functionGetSymbol f arg
        (sargs,sres) = functionSignature f arg
    in (L.List [L.Symbol "_",L.Symbol "as-array",if isOverloaded f
                                                 then L.List [f'
                                                             ,L.List $ fmap sortToLisp sargs
                                                             ,sortToLisp sres]
                                                 else f'],c)
exprToLisp (Forall ann f) c = let (arg,tps,nc) = createArgs ann c
                                  (arg',nc') = exprToLisp (f arg) nc
                              in (L.List [L.Symbol "forall"
                                         ,L.List [L.List [L.Symbol $ T.pack name,sortToLisp tp]
                                                  | (name,tp) <- tps]
                                         ,arg'],nc')
exprToLisp (Exists ann f) c = let (arg,tps,nc) = createArgs ann c
                                  (arg',nc') = exprToLisp (f arg) nc
                              in (L.List [L.Symbol "exists"
                                         ,L.List [L.List [L.Symbol $ T.pack name,sortToLisp tp]
                                                  | (name,tp) <- tps ]
                                         ,arg'],nc')
exprToLisp (Let ann x f) c = let (arg,tps,nc) = createArgs ann c
                                 (arg',nc') = unpackArgs (\e _ cc -> exprToLisp e cc
                                                         ) x ann nc
                                 (arg'',nc'') = exprToLisp (f arg) nc'
                             in (L.List [L.Symbol "let"
                                        ,L.List [L.List [L.Symbol $ T.pack name,lisp]
                                                | ((name,_),lisp) <- Prelude.zip tps arg' ]
                                        ,arg''],nc'')
exprToLisp (App fun x) c
  = let arg_ann = extractArgAnnotation x
        l = functionGetSymbol fun arg_ann
        ~(x',c1) = unpackArgs (\e _ i -> exprToLisp e i) x
                   arg_ann c
    in if Prelude.null x'
       then (l,c1)
       else (L.List $ l:x',c1)
exprToLisp (Named expr name) c = let (expr',c') = exprToLisp expr c
                                 in (L.List [L.Symbol "!",expr'
                                            ,L.Symbol ":named"
                                            ,L.Symbol $ T.pack name],c')

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

functionGetSymbol :: SMTFunction a b -> ArgAnnotation a -> L.Lisp
functionGetSymbol SMTEq _ = L.Symbol "="
functionGetSymbol fun@(SMTMap f) ann
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
    sym' = functionGetSymbol f ann_v
    (sigArg,sigRes) = functionSignature f ann_v
    sym = if isOverloaded f
          then L.List [sym',
                       L.List (fmap sortToLisp sigArg),
                       sortToLisp sigRes]
          else sym'     
functionGetSymbol (SMTFun name _) _ = L.Symbol (T.pack name)
functionGetSymbol (SMTOrd op) _ = L.Symbol $ case op of
  Ge -> ">="
  Gt -> ">"
  Le -> "<="
  Lt -> "<"
functionGetSymbol (SMTArith op) _ = L.Symbol $ case op of
  Plus -> "+"
  Mult -> "*"
functionGetSymbol SMTMinus _ = L.Symbol "-"
functionGetSymbol (SMTIntArith op) _ = L.Symbol $ case op of
  Div -> "div"
  Mod -> "mod"
  Rem -> "rem"
functionGetSymbol SMTDivide _ = L.Symbol "/"
functionGetSymbol SMTNeg _ = L.Symbol "-"
functionGetSymbol SMTAbs _ = L.Symbol "abs"
functionGetSymbol SMTNot _ = L.Symbol "not"
functionGetSymbol (SMTLogic op) _ = case op of
  And -> L.Symbol "and"
  Or -> L.Symbol "or"
  XOr -> L.Symbol "xor"
  Implies -> L.Symbol "=>"
functionGetSymbol SMTDistinct _ = L.Symbol "distinct"
functionGetSymbol SMTToReal _ = L.Symbol "to-real"
functionGetSymbol SMTToInt _ = L.Symbol "to-int"
functionGetSymbol SMTITE _ = L.Symbol "ite"
functionGetSymbol (SMTBVComp op) _ = L.Symbol $ case op of
  BVULE -> "bvule"
  BVULT -> "bvult"
  BVUGE -> "bvuge"
  BVUGT -> "bvugt"
  BVSLE -> "bvsle"
  BVSLT -> "bvslt"
  BVSGE -> "bvsge"
  BVSGT -> "bvsgt"
functionGetSymbol (SMTBVBin op) _ = L.Symbol $ case op of
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
functionGetSymbol (SMTBVUn op) _ = case op of
  BVNot -> L.Symbol "bvnot"
  BVNeg -> L.Symbol "bvneg"
functionGetSymbol SMTSelect _ = L.Symbol "select"
functionGetSymbol SMTStore _ = L.Symbol "store"
functionGetSymbol f@(SMTConstArray i_ann) v_ann
  = withUndef f $
    \u_arr -> L.List [L.Symbol "as"
                     ,L.Symbol "const"
                     ,sortToLisp $ getSort u_arr (i_ann,v_ann)]
  where
    withUndef :: SMTFunction (SMTExpr v) (SMTArray i v)
                 -> (SMTArray i v -> a) -> a
    withUndef _ f' = f' undefined
functionGetSymbol SMTConcat _ = L.Symbol "concat"
functionGetSymbol f@(SMTExtract prStart prLen) ann
  = L.List [L.Symbol "_"
           ,L.Symbol "extract"
           ,L.Number $ L.I (start+len-1)
           ,L.Number $ L.I start]
  where
    start = reflectNat prStart 0
    len = reflectNat prLen 0
functionGetSymbol (SMTConstructor (Constructor name)) _ = L.Symbol $ T.pack name
functionGetSymbol (SMTConTest (Constructor name)) _ = L.Symbol $ T.pack $ "is-"++name
functionGetSymbol (SMTFieldSel (Field name)) _ = L.Symbol $ T.pack name

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
  liftIO $ BS.hPutStrLn (channelIn pipe) ""
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
                   $ \_ _ f -> Just $ f (SMTFun "|unit-resolution|" () :: SMTFunction [SMTExpr Bool] Bool))
                 ,simpleParser (SMTFun "asserted" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "hypothesis" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "lemma" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "monotonicity" () :: SMTFunction (SMTExpr Bool,SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "trans" () :: SMTFunction (SMTExpr Bool,SMTExpr Bool,SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "rewrite" () :: SMTFunction (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "mp" () :: SMTFunction (SMTExpr Bool,SMTExpr Bool,SMTExpr Bool) Bool)]

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
  Nothing -> lispToConstr dts sort l

lispToConstr :: DataTypeInfo -> Maybe Sort -> L.Lisp -> Maybe Value
lispToConstr _ sort (L.Symbol n) = Just (ConstrValue (T.unpack n) [] sort)
lispToConstr dts sort (L.List ((L.Symbol name):args)) = do
  let argSorts = case Map.lookup (T.unpack name) (constructors dts) of
        Nothing -> Nothing
        Just (constr,dt,_) -> Just $ fmap (\field -> getArgSort (fieldSort field)) (conFields constr)
  args' <- case argSorts of
    Nothing -> mapM (lispToValue' dts Nothing) args
    Just sorts -> mapM (\(l,s) -> lispToValue' dts s l) (zip args sorts)
  return $ ConstrValue (T.unpack name) args' sort
  where
    getArgSort (Fix (ArgumentSort n)) = case sort of
      Just (Fix (NamedSort _ args)) -> Just $ args `genericIndex` n
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

valueToLisp :: Value -> L.Lisp
valueToLisp (BoolValue False) = L.Symbol "false"
valueToLisp (BoolValue True) = L.Symbol "true"
valueToLisp (IntValue i) = if i<0
                           then L.List [L.Symbol "-"
                                       ,L.Number $ L.I (abs i)]
                           else L.Number $ L.I i
valueToLisp (RealValue i)
  = let res = L.List [L.Symbol "/"
                     ,L.Number $ L.I (abs $ numerator i)
                     ,L.Number $ L.I $ denominator i]
    in if i<0
       then L.List [L.Symbol "-"
                   ,res]
       else res
valueToLisp (BVValue { bvValueWidth = w
                     , bvValueValue = v })
  = L.List [L.Symbol "_"
           ,L.Symbol $ T.pack $ "bv"++(if v>=0
                                       then show v
                                       else show (2^w + v))
           ,L.Number $ L.I w]
valueToLisp (ConstrValue name vals sort)
  = let constr = case sort of
          Just sort' -> L.List [L.Symbol "as"
                               ,L.Symbol $ T.pack name
                               ,sortToLisp sort']
          Nothing -> L.Symbol $ T.pack name
    in case vals of
      [] -> constr
      _ -> L.List (constr:(fmap valueToLisp vals))

lispToExpr :: FunctionParser -> (T.Text -> Maybe UntypedExpr)
              -> DataTypeInfo
              -> (forall a. SMTType a => SMTExpr a -> b) -> Maybe Sort -> L.Lisp -> Maybe b
lispToExpr fun bound dts f expected l = case lispToValue dts expected l of
  Just val -> valueToHaskell dts
              (\(val'::t) ann
               -> asValueType (undefined::t) $
                  \(_::tv) -> case cast (val',ann) of
                    Just (rval::tv,rann::SMTAnnotation tv) -> f $ Const rval rann
              ) expected val
  Nothing -> case preprocessHack l of
    L.Symbol name -> case bound name of
      Nothing -> Nothing
      Just subst -> entype (\subst' -> Just $ f subst') subst
    L.List [L.Symbol "forall",L.List args',body]
      -> fmap f $ quantToExpr Forall fun bound dts args' body
    L.List [L.Symbol "exists",L.List args',body]
      -> fmap f $ quantToExpr Exists fun bound dts args' body
    L.List [L.Symbol "let",L.List args',body]
      -> let struct = parseLetStruct fun bound dts expected args' body
         in Just $ convertLetStruct f struct
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
          \rfun -> case (do
                            (rargs,rest) <- toArgs nargs
                            case rest of
                              [] -> Just $ App rfun rargs
                              _ -> Nothing) of
                     Just e -> f e
                     Nothing -> error $ "smtlib2: Wrong arguments for function "++show fsym++": "++show arg_tps
      Just (DefinedParser arg_tps _ parse) -> do
        nargs <- mapM (\(el,tp) -> lispToExpr fun bound dts UntypedExpr (Just tp) el)
                 (zip args' arg_tps)
        parse $ \rfun -> case (do
                                  (rargs,rest) <- toArgs nargs
                                  case rest of
                                    [] -> Just $ App rfun rargs
                                    _ -> Nothing) of
                           Just e -> f e
                           Nothing -> error $ "smtlib2: Wrong arguments for function "++show fsym
    _ -> Nothing
  where
    lispToExprs constr exprs = do
      res <- mapM (\arg -> lispToExpr fun bound dts (UntypedExpr) Nothing arg) exprs
      let sorts = fmap (entype exprSort) res
      if constr sorts
        then return res
        else (case generalizeSorts sorts of
                 Just sorts' -> mapM (\(arg,sort') -> lispToExpr fun bound dts UntypedExpr (Just sort') arg) (zip exprs sorts')
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

quantToExpr :: (forall a. Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool)
               -> FunctionParser
               -> (T.Text -> Maybe UntypedExpr)
               -> DataTypeInfo
               -> [L.Lisp] -> L.Lisp -> Maybe (SMTExpr Bool)
quantToExpr q fun bound dts (L.List [L.Symbol var,tp]:rest) body
  = let sort = lispToSort tp
        getForall :: Typeable a => a -> SMTExpr a -> SMTExpr a
        getForall = const id
    in Just $ withSort dts sort
       (\u ann ->
         q ann $ \subst -> case quantToExpr q fun
                                (\txt -> if txt==var
                                         then Just $ UntypedExpr $ getForall u subst
                                         else bound txt)
                                dts rest body of
                             Just r -> r
                             Nothing -> error $ "smtlib2: Failed to parse quantifier construct "++show rest
       )
quantToExpr _ fun bound dts [] body
  = lispToExpr fun bound dts (\expr -> case gcast expr of
                                 Nothing -> error "smtlib2: Body of existential quantification isn't bool."
                                 Just r -> r
                             ) (Just $ getSort (undefined::Bool) ()) body
quantToExpr _ _ _ _ (el:_) _ = error $ "smtlib2: Invalid element "++show el++" in quantifier construct."

data LetStruct where
  LetStruct :: SMTType a => SMTAnnotation a -> SMTExpr a -> (SMTExpr a -> LetStruct) -> LetStruct
  EndLet :: SMTType a => SMTExpr a -> LetStruct

parseLetStruct :: FunctionParser
                  -> (T.Text -> Maybe UntypedExpr)
                  -> DataTypeInfo
                  -> Maybe Sort
                  -> [L.Lisp] -> L.Lisp -> LetStruct
parseLetStruct fun bound tps expected (L.List [L.Symbol name,expr]:rest) arg
  = case lispToExpr fun bound tps
         (\expr' -> LetStruct (extractAnnotation expr') expr' $
                    \sym -> parseLetStruct fun
                            (\txt -> if txt==name
                                     then Just $ UntypedExpr sym
                                     else bound txt) tps expected rest arg
         ) Nothing expr of
      Nothing -> error $ "smtlib2: Failed to parse argument in let-expression "++show expr
      Just x -> x
parseLetStruct fun bound tps expected [] arg
  = case lispToExpr fun bound tps EndLet expected arg of
    Nothing -> error $ "smtlib2: Failed to parse body of let-expression: "++show arg
    Just x -> x
parseLetStruct _ _ _ _ (el:_) _ = error $ "smtlib2: Invalid entry "++show el++" in let construct."

extractType :: (forall a. SMTType a => a -> b) -> LetStruct -> b
extractType f (EndLet x) = f (getUndef x)
extractType f (LetStruct _ expr g) = extractType f (g expr)

convertLetStructT :: SMTType a => LetStruct -> SMTExpr a
convertLetStructT (EndLet x) = case gcast x of
  Just x' -> x'
  Nothing -> error "smtlib2: Type error while converting let structure."
convertLetStructT (LetStruct ann x g) = Let ann x (\sym -> convertLetStructT (g sym))

convertLetStruct :: (forall a. SMTType a => SMTExpr a -> b) -> LetStruct -> b
convertLetStruct f x
  = extractType
    (\(_::t) -> f (convertLetStructT x :: SMTExpr t)) x

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
  = let fsym = functionGetSymbol fun unit
        (uargs,ures) = getFunUndef fun
    in nameParser fsym (DefinedParser
                        (getSorts uargs unit)
                        (getSort ures unit)
                        $ \f -> Just $ f fun)

commonFunctions :: FunctionParser
commonFunctions = mconcat
                  [eqParser
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
                  ,sigParser]

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
  sigParser :: FunctionParser
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
        Nothing -> Nothing
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
                   \sort_arg _ f -> withFirstArgSort dts sym sort_arg $
                                    \(_::t) _
                                    -> Just $ f (SMTOrd op :: SMTFunction (SMTExpr t,SMTExpr t) Bool)

arithOpParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "+" -> Just $ OverloadedParser allEqConstraint (\sorts -> Just (head sorts)) $
                  \_ sort_ret f
                  -> withSort dts sort_ret $
                     \(_::t) _
                     -> Just $ f (SMTArith Plus::SMTFunction [SMTExpr t] t)
  L.Symbol "*" -> Just $ OverloadedParser allEqConstraint (\sorts -> Just (head sorts)) $
                  \_ sort_ret f
                  -> withSort dts sort_ret $
                     \(_::t) _
                     -> Just $ f (SMTArith Mult::SMTFunction [SMTExpr t] t)
  _ -> Nothing

minusParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "-" -> Just $ OverloadedParser allEqConstraint (\sorts -> Just (head sorts)) $
                  \sort_arg _ f -> case sort_arg of
                    [] -> error "smtlib2: minus function needs at least one argument"
                    [s] -> withSort dts s $ \(_::t) _ -> Just $ f (SMTNeg::SMTFunction (SMTExpr t) t)
                    (s:_) -> withSort dts s $ \(_::t) _ -> Just $ f (SMTMinus::SMTFunction (SMTExpr t,SMTExpr t) t)
  _ -> Nothing

intArithParser = mconcat [simpleParser (SMTIntArith Div)
                         ,simpleParser (SMTIntArith Mod)
                         ,simpleParser (SMTIntArith Rem)]

divideParser = simpleParser SMTDivide

absParser = FunctionParser $ \sym _ dts -> case sym of
  L.Symbol "abs" -> Just $ OverloadedParser (const True) (\sorts -> Just $ head sorts) $
                    \_ sort_ret f
                    -> withSort dts sort_ret $ \(_::t) _ -> Just $ f (SMTAbs::SMTFunction (SMTExpr t) t)
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
  L.Symbol "ite" -> Just $ OverloadedParser allEqConstraint
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
           _ -> error "smtlib2: Wrong arguments for select function.") $
       \sort_arg sort_ret f -> case sort_arg of
         (Fix (ArraySort isort1 _):_)
           -> withSorts dts isort1 $
              \(_::i) _ -> withSort dts sort_ret $
                           \(_::v) _ -> Just $ f (SMTSelect::SMTFunction (SMTExpr (SMTArray i v),i) v)
         _ -> error "smtlib2: Wrong arguments for select function."
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
        rsort@(Fix (ArraySort idx val))
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
      let rsig = fmap lispToSort sig
          rret = lispToSort ret
      parser <- parseFun r fsym r dts
      return $ DefinedParser rsig rret $
        \f -> case parser of
          OverloadedParser _ _ parse -> parse rsig rret f
          DefinedParser _ _ parse -> parse f
    g _ _ _ = Nothing

constructorParser :: DataTypeInfo -> FunctionParser
constructorParser dts
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
                                                                (\(_::ret) _
                                                                 -> withSorts dts argSorts
                                                                    (\(_::arg) ann
                                                                     -> Just $ f (SMTConstructor (Constructor (conName con)::Constructor arg ret))))
                                         }
        _ -> Nothing

withPipe :: MonadIO m => String -> SMT' m a -> m a
withPipe prog act = do
  pipe <- liftIO $ createSMTPipe prog
  withSMTBackend pipe act
