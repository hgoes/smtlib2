{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,RankNTypes,DeriveDataTypeable,TypeSynonymInstances,TypeFamilies,FlexibleContexts,CPP,ScopedTypeVariables #-}
module Language.SMTLib2.Internals where

import Data.Attoparsec
import qualified Data.AttoLisp as L
import Data.ByteString as BS hiding (reverse)
import qualified Data.ByteString.Char8 as BS8
import Blaze.ByteString.Builder
import System.Process
import System.IO as IO
import Data.Monoid
import Control.Monad.Reader
import Control.Monad.State
import Data.Text as T hiding (reverse)
import Data.Typeable
import Data.Map as Map hiding (assocs)
import Data.Set as Set
import Data.List as List (mapAccumL,find,genericReplicate)
#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
import Data.Proxy
#endif
#ifdef SMTLIB2_WITH_DATAKINDS
import Data.Tagged
#endif
    
-- Monad stuff
import Control.Applicative (Applicative(..))
import Control.Monad.State.Lazy as Lazy (StateT)
import Control.Monad.Cont (ContT)
import Control.Monad.Error (ErrorT, Error)
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.List (ListT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.State.Strict as Strict (StateT)
import Control.Monad.Writer.Lazy as Lazy (WriterT)
import Control.Monad.Writer.Strict as Strict (WriterT)

-- | Haskell types which can be represented in SMT
class (Eq t,Typeable t,Eq (SMTAnnotation t),Typeable (SMTAnnotation t)) 
      => SMTType t where
  type SMTAnnotation t
  getSort :: t -> SMTAnnotation t -> L.Lisp
  getSort u _ = getSortBase u
  getSortBase :: t -> L.Lisp
  declareType :: t -> SMTAnnotation t -> SMT ()
  additionalConstraints :: t -> SMTAnnotation t -> SMTExpr t -> [SMTExpr Bool]
  additionalConstraints _ _ _ = []
  toSort :: t -> SMTAnnotation t -> Sort
  toSort = Sort
  fromSort :: t -> SortParser
  fromSort _ = mempty

-- | Haskell values which can be represented as SMT constants
class SMTType t => SMTValue t where
  unmangle :: L.Lisp -> SMTAnnotation t -> Maybe t
  mangle :: t -> SMTAnnotation t -> L.Lisp

-- | All records which can be expressed in SMT
class SMTType t => SMTRecordType t where
  getFieldAnn :: (SMTType f,Typeable (SMTAnnotation f)) => Field t f -> SMTAnnotation t -> SMTAnnotation f

-- | A type class for all types which support arithmetic operations in SMT
class (SMTValue t,Num t) => SMTArith t

-- | Lifts the 'Ord' class into SMT
class (SMTType t) => SMTOrd t where
  (.<.) :: SMTExpr t -> SMTExpr t -> SMTExpr Bool
  (.>=.) :: SMTExpr t -> SMTExpr t -> SMTExpr Bool
  (.>.) :: SMTExpr t -> SMTExpr t -> SMTExpr Bool
  (.<=.) :: SMTExpr t -> SMTExpr t -> SMTExpr Bool

infix 4 .<., .<=., .>=., .>.

-- | An array which maps indices of type /i/ to elements of type /v/.
data SMTArray (i :: *) (v :: *) = SMTArray deriving (Eq,Typeable)

type SMTRead = (Handle, Handle)
type SMTState = (Map String Integer,Map TyCon DeclaredType,Map T.Text UntypedExpr)

-- | The SMT monad used for communating with the SMT solver
newtype SMT a = SMT { runSMT :: ReaderT SMTRead (Lazy.StateT SMTState IO) a }

instance Functor SMT where
  fmap f = SMT . fmap f . runSMT

instance Monad SMT where
  return = SMT . return
  m >>= f = SMT $ (runSMT m) >>= runSMT . f

instance MonadIO SMT where
  liftIO = SMT . liftIO

instance MonadFix SMT where
  mfix f = SMT $ mfix (runSMT . f)

instance Applicative SMT where
  pure = return
  (<*>) = ap

askSMT :: SMT SMTRead
askSMT = SMT ask

getSMT :: SMT SMTState
getSMT = SMT get

putSMT :: SMTState -> SMT ()
putSMT = SMT . put

modifySMT :: (SMTState -> SMTState) -> SMT ()
modifySMT f = SMT $ modify f

-- | Lift an SMT action into an arbitrary monad (like liftIO).
class Monad m => MonadSMT m where
  liftSMT :: SMT a -> m a

instance MonadSMT SMT where
  liftSMT = id

instance MonadSMT m => MonadSMT (ContT r m) where
  liftSMT = lift . liftSMT

instance (Error e, MonadSMT m) => MonadSMT (ErrorT e m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (IdentityT m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (ListT m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (MaybeT m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (ReaderT r m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (Lazy.StateT s m) where
  liftSMT = lift . liftSMT

instance MonadSMT m => MonadSMT (Strict.StateT s m) where
  liftSMT = lift . liftSMT

instance (Monoid w, MonadSMT m) => MonadSMT (Lazy.WriterT w m) where
  liftSMT = lift . liftSMT

instance (Monoid w, MonadSMT m) => MonadSMT (Strict.WriterT w m) where
  liftSMT = lift . liftSMT

-- | An abstract SMT expression
data SMTExpr t where
  Var :: SMTType t => Text -> SMTAnnotation t -> SMTExpr t
  Const :: SMTValue t => t -> SMTAnnotation t -> SMTExpr t
  AsArray :: (SMTFunction f) 
             => f -> ArgAnnotation (SMTFunArg f)
             -> SMTExpr (SMTArray (SMTFunArg f) (SMTFunRes f))
  Forall :: Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool
  Exists :: Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool
  Let :: (Args a) => ArgAnnotation a -> a -> (a -> SMTExpr b) -> SMTExpr b
  App :: SMTFunction a => a -> SMTFunArg a -> SMTExpr (SMTFunRes a)
  Named :: SMTExpr a -> Text -> SMTExpr a
  deriving Typeable

data UntypedExpr where
  UntypedExpr :: SMTType a => SMTExpr a -> UntypedExpr

entype :: (forall a. SMTType a => SMTExpr a -> b) -> UntypedExpr -> b
entype f (UntypedExpr x) = f x

data Sort where
  Sort :: SMTType t => t -> SMTAnnotation t -> Sort
  ArraySort :: [Sort] -> Sort -> Sort
  BVSort :: Integer -> Sort

newtype SortParser = SortParser { parseSort :: L.Lisp -> SortParser -> Maybe Sort }

instance Monoid SortParser where
  mempty = SortParser $ \_ _ -> Nothing
  mappend p1 p2 = SortParser $ \sym rec -> case parseSort p1 sym rec of
    Nothing -> parseSort p2 sym rec
    Just r -> Just r

class (Args (SMTFunArg a),
       SMTType (SMTFunRes a),
       Liftable (SMTFunArg a),
       Typeable a,Eq a)
      => SMTFunction a where
  type SMTFunArg a
  type SMTFunRes a
  isOverloaded :: a -> Bool
  getFunctionSymbol :: a -> ArgAnnotation (SMTFunArg a) -> L.Lisp
  inferResAnnotation :: a -> ArgAnnotation (SMTFunArg a)
                        -> SMTAnnotation (SMTFunRes a)
  
instance Eq a => Eq (SMTExpr a) where
  (==) = eqExpr 0

eqExpr :: Integer -> SMTExpr a -> SMTExpr a -> Bool
eqExpr n lhs rhs = case (lhs,rhs) of
  (Var v1 _,Var v2 _) -> v1 == v2
  (Const v1 _,Const v2 _) -> v1 == v2
  (AsArray f1 arg1,AsArray f2 arg2) -> case cast f2 of
    Nothing -> False
    Just f2' -> case cast arg2 of
      Nothing -> False 
      Just arg2' -> f1 == f2' && arg1 == arg2'
  (Forall a1 f1,Forall a2 f2) -> let name i = T.pack $ "internal_eq_check"++show i
                                     (n',v) = foldExprs (\i _ ann -> (i+1,Var (name i) ann)) n undefined a1
                                 in case cast f2 of
                                   Nothing -> False
                                   Just f2' -> eqExpr n' (f1 v) (f2' v)
  (Exists a1 f1,Exists a2 f2) -> let name i = T.pack $ "internal_eq_check"++show i
                                     (n',v) = foldExprs (\i _ ann -> (i+1,Var (name i) ann)) n undefined a1
                                 in case cast f2 of
                                   Nothing -> False
                                   Just f2' -> eqExpr n' (f1 v) (f2' v)
  (Let a1 x1 f1,Let a2 x2 f2) -> eqExpr n (f1 x1) (f2 x2)
  (Named e1 n1,Named e2 n2) -> eqExpr n e1 e2 && n1==n2
  (App f1 arg1,App f2 arg2) -> case cast f2 of
      Nothing -> False
      Just f2' -> case cast arg2 of
        Nothing -> False
        Just arg2' -> f1 == f2' && arg1 == arg2'
  where
    eqExpr' :: (Typeable a,Typeable b) => Integer -> SMTExpr a -> SMTExpr b -> Bool
    eqExpr' n lhs rhs = case gcast rhs of
      Nothing -> False
      Just rhs' -> eqExpr n lhs rhs'

    eqExprs' :: (Eq a,Typeable a,Typeable b) => Integer -> [SMTExpr a] -> [SMTExpr b] -> Bool
    eqExprs' n xs ys = case cast ys of
      Nothing -> False
      Just ys' -> eqExprs n xs ys'

    eqExprs :: (Eq a) => Integer -> [SMTExpr a] -> [SMTExpr a] -> Bool
    eqExprs n (x:xs) (y:ys) = eqExpr n x y && eqExprs n xs ys
    eqExprs _ [] [] = True
    eqExprs _ _ _ = False

-- | Represents a constructor of a datatype /a/
--   Can be obtained by using the template haskell extension module
data Constructor a = Constructor Text deriving (Eq,Show)

-- | Represents a field of the datatype /a/ of the type /f/
data Field a f = Field Text deriving (Eq,Show)

newtype InterpolationGroup = InterpolationGroup Text

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print \"success\" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     | ProduceProofs Bool -- ^ Produce a proof of unsatisfiability after each failed checkSat
     | ProduceUnsatCores Bool -- ^ Enable the querying of unsatisfiable cores after a failed checkSat
     deriving (Show,Eq,Ord)

-- | A piece of information of type /r/ that can be obtained by the SMT solver
class SMTInfo i where
  type SMTInfoResult i
  getInfo :: i -> SMT (SMTInfoResult i)

-- | The name of the SMT solver
data SMTSolverName = SMTSolverName deriving (Show,Eq,Ord)

instance SMTInfo SMTSolverName where
  type SMTInfoResult SMTSolverName = String
  getInfo _ = do
    putRequest (L.List [L.Symbol "get-info",L.Symbol ":name"])
    res <- parseResponse
    case res of
      L.List [L.Symbol ":name",L.String name] -> return $ T.unpack name
      _ -> error "Invalid solver response to 'get-info' name query"

-- | The version of the SMT solver
data SMTSolverVersion = SMTSolverVersion deriving (Show,Eq,Ord)

instance SMTInfo SMTSolverVersion where
  type SMTInfoResult SMTSolverVersion = String
  getInfo _ = do
    putRequest (L.List [L.Symbol "get-info",L.Symbol ":version"])
    res <- parseResponse
    case res of
      L.List [L.Symbol ":version",L.String name] -> return $ T.unpack name
      _ -> error "Invalid solver response to 'get-info' version query"

-- | Instances of this class may be used as arguments for constructed functions and quantifiers.
class (Eq a,Typeable a,Eq (ArgAnnotation a),Typeable (ArgAnnotation a)) 
      => Args a where
  type ArgAnnotation a
  foldExprs :: (forall t. SMTType t => s -> SMTExpr t -> SMTAnnotation t -> (s,SMTExpr t)) 
               -> s -> a -> ArgAnnotation a -> (s,a)
  extractArgAnnotation :: a -> ArgAnnotation a
  toArgs :: [UntypedExpr] -> Maybe (a,[UntypedExpr])
  toSorts :: a -> ArgAnnotation a -> [Sort]
  getArgAnnotation :: a -> [Sort] -> (ArgAnnotation a,[Sort])

class (Args a) => Liftable a where
  type Lifted a i
  getLiftedArgumentAnn :: a -> i -> ArgAnnotation a -> ArgAnnotation i -> ArgAnnotation (Lifted a i)
  inferLiftedAnnotation :: a -> i -> ArgAnnotation (Lifted a i) -> (ArgAnnotation i,ArgAnnotation a)
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint :: Args i => p (a,i) -> Dict (Liftable (Lifted a i))
#endif

data DeclaredType where
  DeclaredType :: SMTType a => a -> SMTAnnotation a -> DeclaredType
  DeclaredValueType :: SMTValue a => a -> SMTAnnotation a -> DeclaredType

withDeclaredType :: (forall a. SMTType a => a -> SMTAnnotation a -> b) -> DeclaredType -> b
withDeclaredType f (DeclaredType u ann) = f u ann
withDeclaredType f (DeclaredValueType u ann) = f u ann

withDeclaredValueType :: (forall a. SMTValue a => a -> SMTAnnotation a -> b) -> DeclaredType -> Maybe b
withDeclaredValueType f (DeclaredValueType u ann) = Just $ f u ann
withDeclaredValueType _ _ = Nothing

declaredTypeCon :: DeclaredType -> TyCon
declaredTypeCon d = fst $ splitTyConApp $ declaredTypeRep d

declaredTypeRep :: DeclaredType -> TypeRep
declaredTypeRep = withDeclaredType (\u _ -> typeOf u)

declForSMTType :: L.Lisp -> Map TyCon DeclaredType -> DeclaredType
declForSMTType l mp = case List.find (\(_,d) -> withDeclaredType (\u ann -> (getSort u ann) == l) d) (Map.toList mp) of
  Nothing -> error $ "smtlib2: Can't convert type "++show l++" to haskell."
  Just (_,d) -> d

argSorts :: Args a => a -> ArgAnnotation a -> [L.Lisp]
argSorts arg ann = Prelude.reverse res
    where
      (res,_) = foldExprs (\tps e ann' -> ((getSort (getUndef e) ann'):tps,e)) [] arg ann

allOf :: Args a => (forall t. SMTExpr t) -> a
allOf x = snd $ foldExprs (\_ _ _ -> ((),x)) () undefined undefined

unpackArgs :: Args a => (forall t. SMTType t => SMTExpr t -> SMTAnnotation t -> Integer -> (c,Integer)) -> a -> ArgAnnotation a -> Integer -> ([c],Integer)
unpackArgs f x ann i = fst $ foldExprs (\(res,ci) e ann' -> let (p,ni) = f e ann' ci
                                                            in ((res++[p],ni),e)
                                       ) ([],i) x ann

declareArgTypes :: Args a => a -> ArgAnnotation a -> SMT ()
declareArgTypes arg ann
  = fst $ foldExprs (\act e ann' -> (act >> declareType (getUndef e) ann',e)) (return ()) arg ann

declareType' :: DeclaredType -> SMT () -> SMT ()
declareType' decl act = do
  let con = declaredTypeCon decl
  (c,decls,mp) <- getSMT
  if Map.member con decls
    then return ()
    else (do
             putSMT (c,Map.insert con decl decls,mp)
             act)

defaultDeclareValue :: SMTValue a => a -> SMTAnnotation a -> SMT ()
defaultDeclareValue u ann = declareType' (DeclaredValueType u ann) (return ())

defaultDeclareType :: SMTType a => a -> SMTAnnotation a -> SMT ()
defaultDeclareType u ann = declareType' (DeclaredType u ann) (return ())

createArgs :: Args a => ArgAnnotation a -> Integer -> (a,[(Text,L.Lisp)],Integer)
createArgs ann i = let ((tps,ni),res) = foldExprs (\(tps',ci) e ann' -> let name = T.pack $ "arg_"++show ci
                                                                            sort' = getSort (getUndef e) ann'
                                                                        in ((tps'++[(name,sort')],ci+1),Var name ann')
                                                  ) ([],i) (error "Evaluated the argument to createArgs") ann
                   in (res,tps,ni)

-- | An extension of the `Args` class: Instances of this class can be represented as native haskell data types.
class Args a => LiftArgs a where
  type Unpacked a
  -- | Converts a haskell value into its SMT representation.
  liftArgs :: Unpacked a -> ArgAnnotation a -> a
  -- | Converts a SMT representation back into a haskell value.
  unliftArgs :: a -> SMT (Unpacked a)

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust ((Just x):_) = Just x
firstJust (Nothing:xs) = firstJust xs

getUndef :: SMTExpr t -> t
getUndef _ = error "Don't evaluate the result of 'getUndef'"

getFunUndef :: (SMTFunction f) => f -> (SMTFunArg f,SMTFunRes f)
getFunUndef _ = (error "Don't evaluate the first result of 'getFunUndef'",
                 error "Don't evaluate the second result of 'getFunUndef'")

getArrayUndef :: Args i => SMTExpr (SMTArray i v) -> (i,Unpacked i,v)
getArrayUndef _ = (undefined,undefined,undefined)

declareFun :: Text -> [L.Lisp] -> L.Lisp -> SMT ()
declareFun name tps rtp
  = putRequest $ L.List [L.Symbol "declare-fun"
                        ,L.Symbol name
                        ,args tps
                        ,rtp
                        ]

defineFun :: Text -> [(Text,L.Lisp)] -> L.Lisp -> L.Lisp -> SMT ()
defineFun name arg rtp body = putRequest $ L.List [L.Symbol "define-fun"
                                                  ,L.Symbol name
                                                  ,args [ L.List [ L.Symbol n, tp ]
                                                        | (n,tp) <- arg ]
                                                  ,rtp
                                                  ,body ]

declareDatatypes :: [Text] -> [(Text,[(Text,[(Text,L.Lisp)])])] -> SMT ()
declareDatatypes params dts
  = putRequest $ L.List [L.Symbol "declare-datatypes"
                        ,args (fmap L.Symbol params)
                        ,L.List
                         [ L.List $ [L.Symbol name] 
                           ++ [ L.List $ [L.Symbol conName] 
                                ++ [ L.List [L.Symbol fieldName,tp]
                                   | (fieldName,tp) <- fields ]
                              | (conName,fields) <- constructor ]
                         | (name,constructor) <- dts ]
                        ]

args :: [L.Lisp] -> L.Lisp
args [] = L.Symbol "()"
args xs = L.List xs

-- | Check if the model is satisfiable (e.g. if there is a value for each variable so that every assertion holds)
checkSat :: SMT Bool
checkSat = do
  (_,hout) <- askSMT
  clearInput
  putRequest (L.List [L.Symbol "check-sat"])
  res <- liftIO $ BS.hGetLine hout
  case res of
    "sat" -> return True
    "sat\r" -> return True
    "unsat" -> return False
    "unsat\r" -> return False
    _ -> error $ "unknown check-sat response: "++show res

-- | Perform a stacked operation, meaning that every assertion and declaration made in it will be undone after the operation.
stack :: SMT a -> SMT a
stack act = do
  putRequest (L.List [L.Symbol "push",L.toLisp (1::Integer)])
  res <- act
  putRequest (L.List [L.Symbol "pop",L.toLisp (1::Integer)])
  return res

-- | Insert a comment into the SMTLib2 command stream.
--   If you aren't looking at the command stream for debugging, this will do nothing.
comment :: String -> SMT ()
comment msg = do
  (hin,_) <- askSMT
  liftIO $ IO.hPutStr hin $ Prelude.unlines (fmap (';':) (Prelude.lines msg))

-- | Spawn a shell command that is used as a SMT solver via stdin/-out to process the given SMT operation.
withSMTSolver :: String -- ^ The shell command to execute
                 -> SMT a -- ^ The SMT operation to perform
                 -> IO a
withSMTSolver solver f = do
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
  res <- evalStateT (runReaderT (runSMT $ do
                                 res <- f
                                 putRequest (L.List [L.Symbol "exit"])
                                 return res
                                ) (hin,hout)) (Map.empty,Map.empty,Map.empty)
  hClose hin
  hClose hout
  terminateProcess handle
  _ <- waitForProcess handle
  return res

clearInput :: SMT ()
clearInput = do
  (_,hout) <- askSMT
  r <- liftIO $ hReady hout
  if r
    then (do
             _ <- liftIO $ BS.hGetSome hout 1024
             clearInput)
    else return ()

putRequest :: L.Lisp -> SMT ()
putRequest e = do
  clearInput
  (hin,_) <- askSMT
  liftIO $ toByteStringIO (BS.hPutStr hin) (mappend (L.fromLispExpr e) flush)
  liftIO $ BS.hPutStrLn hin ""
  liftIO $ hFlush hin

parseResponse :: SMT L.Lisp
parseResponse = do
  (_,hout) <- askSMT
  str <- liftIO $ BS.hGetLine hout
  let continue (Done _ r) = return r
      continue res@(Partial _) = do
        line <- BS.hGetLine hout
        continue (feed (feed res line) (BS8.singleton '\n'))
      continue (Fail str' ctx msg) = error $ "Error parsing "++show str'++" response in "++show ctx++": "++msg
  liftIO $ continue $ parse L.lisp (BS8.snoc str '\n')

-- | Declare a new sort with a specified arity
declareSort :: T.Text -> Integer -> SMT ()
declareSort name arity = putRequest (L.List [L.Symbol "declare-sort",L.Symbol name,L.toLisp arity])

escapeName :: String -> String
escapeName [] = []
escapeName ('_':xs) = '_':'_':escapeName xs
escapeName (x:xs) = x:escapeName xs

freeName :: String -> SMT Text
freeName name = do
  (names,decl,mp) <- getSMT
  let c = case Map.lookup name names of
        Nothing -> 0
        Just c' -> c'
  putSMT (Map.insert name (c+1) names,decl,mp)
  return $ T.pack $ (escapeName name)++(case c of
                                           0 -> ""
                                           _ -> "_"++show c)

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

argsSignature :: Args a => a -> ArgAnnotation a -> [L.Lisp]
argsSignature arg ann 
  = reverse $ fst $ 
    foldExprs (\sigs e ann -> ((getSort (getUndef e) ann):sigs,e))
    [] arg ann

functionGetSignature :: (SMTFunction f) 
                        => f
                        -> ArgAnnotation (SMTFunArg f) 
                        -> SMTAnnotation (SMTFunRes f) 
                        -> ([L.Lisp],L.Lisp)
functionGetSignature fun arg_ann res_ann 
  = let ~(uarg,ures) = getFunUndef fun
    in (argsSignature uarg arg_ann,getSort ures res_ann)

getSortParser :: SMT SortParser
getSortParser = do
  (_,tps,_) <- getSMT
  return $ mconcat $ fmap (withDeclaredType (\u _ -> fromSort u)) (Map.elems tps)

-- BitVectors

#ifdef SMTLIB2_WITH_DATAKINDS
data Nat = Z | S Nat deriving Typeable

data BVKind = BVUntyped
            | BVTyped Nat

class TypeableNat n where
  typeOfNat :: Proxy n -> TypeRep
  typeOfNat p = Prelude.foldl
                (\c _ -> mkTyConApp (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "'S") [c])
                (mkTyConApp (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "'Z") [])
                (genericReplicate (reflectNat p 0) ())
  reflectNat :: Proxy n -> Integer -> Integer

instance TypeableNat Z where
  typeOfNat _ = mkTyConApp 
                (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "'Z")
                []
  reflectNat _ x = x

instance TypeableNat n => TypeableNat (S n) where
  typeOfNat _ = mkTyConApp 
                (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "'S")
                [typeOfNat (Proxy::Proxy n)]
  reflectNat _ x = reflectNat (Proxy::Proxy n) (x+1)

class TypeableBVKind n where
  typeOfBVKind :: Proxy n -> TypeRep

instance TypeableBVKind BVUntyped where
  typeOfBVKind _ = mkTyConApp 
                   (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "'BVUntyped")
                   []

instance TypeableNat n => TypeableBVKind (BVTyped n) where
  typeOfBVKind _ = mkTyConApp 
                   (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "'BVTyped")
                   [typeOfNat (Proxy::Proxy n)]

type family Add (n1 :: Nat) (n2 :: Nat) :: Nat
type instance Add Z n = n
type instance Add (S n1) n2 = S (Add n1 n2)

reifySum :: (Num a,Ord a) => a -> a -> (forall n1 n2. (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2)) 
                                        => Proxy (n1::Nat) -> Proxy (n2::Nat) -> Proxy (Add n1 n2) -> r) -> r
reifySum n1 n2 f
  | n1 < 0 || n2 < 0 = error "smtlib2: Cann only reify numbers >= 0."
  | otherwise = reifySum' n1 n2 f
  where
    reifySum' :: (Num a,Ord a) => a -> a 
                 -> (forall n1 n2. (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2)) 
                     => Proxy (n1::Nat) -> Proxy (n2::Nat) -> Proxy (Add n1 n2) -> r) -> r
    reifySum' 0 n2 f = reifyNat n2 $ \(_::Proxy i) -> f (Proxy::Proxy Z) (Proxy::Proxy i) (Proxy::Proxy i)
    reifySum' n1 n2 f = reifySum' (n1-1) n2 $ \(_::Proxy i1) (_::Proxy i2) (_::Proxy i3)
                                               -> f (Proxy::Proxy (S i1)) (Proxy::Proxy i2) (Proxy::Proxy (S i3))

reifyExtract :: (Num a,Ord a) => a -> a -> a
                -> (forall n1 n2 n3 n4. (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4,Add n4 n2 ~ S n3)
                    => Proxy (n1::Nat) -> Proxy (n2::Nat) -> Proxy (n3::Nat) -> Proxy (n4::Nat) -> r) -> r
reifyExtract t l u f
  | t <= u || l > u || l < 0 = error "smtlib2: Invalid extract parameters."
  | otherwise = reifyExtract' t l u (u - l + 1) f
  where
    reifyExtract' :: (Num a,Ord a) => a -> a -> a -> a
                     -> (forall n1 n2 n3 n4. (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4,Add n4 n2 ~ S n3)
                         => Proxy (n1::Nat) -> Proxy (n2::Nat) -> Proxy (n3::Nat) -> Proxy (n4::Nat) -> r) -> r
    reifyExtract' t l u 0 f = reifyNat t $ 
                              \(_::Proxy n1) 
                              -> reifyNat u $
                                 \(_::Proxy n3)
                                  -> f (Proxy::Proxy n1) (Proxy::Proxy (S n3)) (Proxy::Proxy n3) (Proxy::Proxy Z)
    reifyExtract' t l u r f = reifyExtract' t l (u-1) (r-1) $
                              \(_::Proxy n1) (_::Proxy n2) (_::Proxy n3) (_::Proxy n4)
                               -> f (Proxy::Proxy n1) (Proxy::Proxy n2) (Proxy::Proxy (S n3)) (Proxy::Proxy (S n4))
    

reifyNat :: (Num a,Ord a) => a -> (forall n. TypeableNat n => Proxy (n::Nat) -> r) -> r
reifyNat x f
  | x < 0 = error "smtlib2: Can only reify numbers >= 0."
  | otherwise = reifyNat' x f
  where
    reifyNat' :: (Num a,Ord a) => a -> (forall n. TypeableNat n => Proxy (n::Nat) -> r) -> r
    reifyNat' 0 f = f (Proxy :: Proxy Z)
    reifyNat' n f = reifyNat' (n-1) (\(_::Proxy n) -> f (Proxy::Proxy (S n)))

data BitVector (b :: BVKind) = BitVector Integer deriving (Eq,Ord)

instance TypeableBVKind k => Typeable (BitVector k) where
  typeOf _ = mkTyConApp 
             (mkTyCon3 "smtlib2" "Language.SMTLib2.Internals" "BitVector")
             [typeOfBVKind (Proxy::Proxy k)]
#else
data Z = Z deriving (Typeable)
data S a = S deriving (Typeable)

class Typeable a => TypeableNat a where
  reflectNat :: a -> Integer -> Integer

instance TypeableNat Z where
  reflectNat _ = id

instance TypeableNat n => TypeableNat (S n) where
  reflectNat _ x = reflectNat (undefined::n) (x+1)

type family Add n1 n2
type instance Add Z n = n
type instance Add (S n1) n2 = S (Add n1 n2)

data BVUntyped = BVUntyped deriving (Eq,Ord,Show,Typeable)
data BVTyped n = BVTyped deriving (Eq,Ord,Show,Typeable)

reifyNat :: (Num a,Ord a) => a -> (forall n. TypeableNat n => n -> r) -> r
reifyNat n f
  | n < 0 = error "smtlib2: Can only reify numbers >= 0."
  | otherwise = reifyNat' n f
  where
    reifyNat' :: (Num a,Eq a) => a -> (forall n. TypeableNat n => n -> r) -> r
    reifyNat' 0 f = f (undefined::Z)
    reifyNat' n f = reifyNat' (n-1) (f.g)

    g :: n -> S n
    g _ = undefined

reifySum :: (Num a,Ord a) => a -> a -> (forall n1 n2. (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2)) 
                                        => n1 -> n2 -> Add n1 n2 -> r) -> r
reifySum n1 n2 f
  | n1 < 0 || n2 < 0 = error "smtlib2: Cann only reify numbers >= 0."
  | otherwise = reifySum' n1 n2 f
  where
    reifySum' :: (Num a,Ord a) => a -> a 
                 -> (forall n1 n2. (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2)) 
                     => n1 -> n2 -> Add n1 n2 -> r) -> r
    reifySum' 0 n2 f = reifyNat n2 $ \(_::i) -> f (undefined::Z) (undefined::i) (undefined::i)
    reifySum' n1 n2 f = reifySum' (n1-1) n2 $ \(_::i1) (_::i2) (_::i3)
                                               -> f (undefined::S i1) (undefined::i2) (undefined::S i3)

reifyExtract :: (Num a,Ord a) => a -> a -> a
                -> (forall n1 n2 n3 n4. (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4,Add n4 n2 ~ S n3)
                    => n1 -> n2 -> n3 -> n4 -> r) -> r
reifyExtract t l u f
  | t <= u || l > u || l < 0 = error "smtlib2: Invalid extract parameters."
  | otherwise = reifyExtract' t l u (u - l + 1) f
  where
    reifyExtract' :: (Num a,Ord a) => a -> a -> a -> a
                     -> (forall n1 n2 n3 n4. (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4,Add n4 n2 ~ S n3)
                         => n1 -> n2 -> n3 -> n4 -> r) -> r
    reifyExtract' t l u 0 f = reifyNat t $ 
                              \(_::n1) 
                              -> reifyNat u $
                                 \(_::n3)
                                  -> f (undefined::n1) (undefined::S n3) (undefined::n3) (undefined::Z)
    reifyExtract' t l u r f = reifyExtract' t l (u-1) (r-1) $
                              \(_::n1) (_::n2) (_::n3) (_::n4)
                               -> f (undefined::n1) (undefined::n2) (undefined::S n3) (undefined::S n4)

data BitVector (b :: *) = BitVector Integer deriving (Eq,Ord,Typeable)
#endif

instance Show (BitVector a) where
  show (BitVector x) = show x

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2
type N4 = S N3
type N5 = S N4
type N6 = S N5
type N7 = S N6
type N8 = S N7
type N9 = S N8
type N10 = S N9
type N11 = S N10
type N12 = S N11
type N13 = S N12
type N14 = S N13
type N15 = S N14
type N16 = S N15
type N17 = S N16
type N18 = S N17
type N19 = S N18
type N20 = S N19
type N21 = S N20
type N22 = S N21
type N23 = S N22
type N24 = S N23
type N25 = S N24
type N26 = S N25
type N27 = S N26
type N28 = S N27
type N29 = S N28
type N30 = S N29
type N31 = S N30
type N32 = S N31
type N33 = S N32
type N34 = S N33
type N35 = S N34
type N36 = S N35
type N37 = S N36
type N38 = S N37
type N39 = S N38
type N40 = S N39
type N41 = S N40
type N42 = S N41
type N43 = S N42
type N44 = S N43
type N45 = S N44
type N46 = S N45
type N47 = S N46
type N48 = S N47
type N49 = S N48
type N50 = S N49
type N51 = S N50
type N52 = S N51
type N53 = S N52
type N54 = S N53
type N55 = S N54
type N56 = S N55
type N57 = S N56
type N58 = S N57
type N59 = S N58
type N60 = S N59
type N61 = S N60
type N62 = S N61
type N63 = S N62
type N64 = S N63

type BV8 = BitVector (BVTyped N8)
type BV16 = BitVector (BVTyped N16)
type BV32 = BitVector (BVTyped N32)
type BV64 = BitVector (BVTyped N64)
