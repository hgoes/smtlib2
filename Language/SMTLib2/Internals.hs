{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,RankNTypes,DeriveDataTypeable,TypeSynonymInstances,TypeFamilies,FlexibleContexts,CPP,ScopedTypeVariables #-}
module Language.SMTLib2.Internals where

import Control.Monad.Reader hiding (mapM,mapM_)
import Control.Monad.State hiding (mapM,mapM_)
import Data.Typeable
import Data.Map as Map hiding (assocs,foldl)
import Data.Char (isDigit)
import Data.Ratio
import Data.Proxy
#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
#endif
#ifdef SMTLIB2_WITH_DATAKINDS
import Data.Tagged
import Data.List as List (genericReplicate)
#endif
import Data.Fix
import Prelude hiding (mapM,mapM_,foldl)
import Data.Foldable
import Data.Traversable

-- Monad stuff
import Control.Applicative (Applicative(..))
import Control.Monad.State.Lazy as Lazy (StateT)

class Monad m => SMTBackend a m where
  smtSetLogic :: a -> String -> m ()
  smtGetInfo :: a -> SMTInfo i -> m i
  smtSetOption :: a -> SMTOption -> m ()
  smtAssert :: a -> SMTExpr Bool -> Maybe InterpolationGroup -> m ()
  smtCheckSat :: a -> m Bool
  smtDeclareDataTypes :: a -> TypeCollection -> m ()
  smtDeclareSort :: a -> String -> Integer -> m ()
  smtPush :: a -> m ()
  smtPop :: a -> m ()
  smtDefineFun :: (SMTType res) => a -> String -> [(String,Sort)] -> SMTExpr res -> m ()
  smtDeclareFun :: a -> String -> [Sort] -> Sort -> m ()
  smtGetValue :: SMTValue t => a -> Map String UntypedExpr -> DataTypeInfo -> SMTExpr t -> m t
  smtGetProof :: a -> Map String UntypedExpr -> DataTypeInfo -> m (SMTExpr Bool)
  smtGetUnsatCore :: a -> m [String]
  smtSimplify :: SMTType t => a -> Map String UntypedExpr -> DataTypeInfo -> SMTExpr t -> m (SMTExpr t)
  smtGetInterpolant :: a -> Map String UntypedExpr -> DataTypeInfo -> [InterpolationGroup] -> m (SMTExpr Bool)
  smtComment :: a -> String -> m ()
  smtExit :: a -> m ()

-- | Haskell types which can be represented in SMT
class (Eq t,Typeable t,Eq (SMTAnnotation t),Typeable (SMTAnnotation t))
      => SMTType t where
  type SMTAnnotation t
  getSort :: t -> SMTAnnotation t -> Sort
  asDataType :: t -> Maybe (String,TypeCollection)
  asDataType _ = Nothing
  asValueType :: t -> (forall v. SMTValue v => v -> r) -> Maybe r
  getProxyArgs :: t -> SMTAnnotation t -> [ProxyArg]
  getProxyArgs _ _ = []
  additionalConstraints :: t -> SMTAnnotation t -> SMTExpr t -> [SMTExpr Bool]
  additionalConstraints _ _ _ = []
  annotationFromSort :: t -> Sort -> SMTAnnotation t

data ArgumentSort' a = ArgumentSort Integer
                     | NormalSort (Sort' a)

type ArgumentSort = Fix ArgumentSort'

-- | Haskell values which can be represented as SMT constants
class SMTType t => SMTValue t where
  unmangle :: Value -> SMTAnnotation t -> Maybe t
  mangle :: t -> SMTAnnotation t -> Value

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

data SMTState = SMTState { nameCount :: Map String Integer
                         , declaredDataTypes :: DataTypeInfo
                         , namedExprs :: Map String UntypedExpr }

data AnyBackend m = forall b. SMTBackend b m => AnyBackend b

-- | The SMT monad used for communating with the SMT solver
data SMT' m a = SMT { runSMT :: ReaderT (AnyBackend m) (Lazy.StateT SMTState m) a }

type SMT = SMT' IO

instance Functor m => Functor (SMT' m) where
  fmap f = SMT . fmap f . runSMT

instance Monad m => Monad (SMT' m) where
  return = SMT . return
  m >>= f = SMT $ (runSMT m) >>= runSMT . f

instance MonadIO m => MonadIO (SMT' m) where
  liftIO = SMT . liftIO

instance MonadFix m => MonadFix (SMT' m) where
  mfix f = SMT $ mfix (runSMT . f)

instance (Monad m,Functor m) => Applicative (SMT' m) where
  pure = return
  (<*>) = ap

--askSMT :: Monad m => SMT' b m b
--askSMT = SMT ask

smtBackend :: Monad m => (forall b. SMTBackend b m => b -> SMT' m a) -> SMT' m a
smtBackend f = SMT $ do
  AnyBackend backend <- ask
  runSMT $ f backend

getSMT :: Monad m => SMT' m SMTState
getSMT = SMT get

putSMT :: Monad m => SMTState -> SMT' m ()
putSMT = SMT . put

modifySMT :: Monad m => (SMTState -> SMTState) -> SMT' m ()
modifySMT f = SMT $ modify f

instance MonadTrans SMT' where
  lift = SMT . lift . lift

-- | An abstract SMT expression
data SMTExpr t where
  Var :: SMTType t => String -> SMTAnnotation t -> SMTExpr t
  Const :: SMTValue t => t -> SMTAnnotation t -> SMTExpr t
  AsArray :: (Args arg,SMTType res) => SMTFunction arg res -> ArgAnnotation arg
             -> SMTExpr (SMTArray arg res)
  Forall :: Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool
  Exists :: Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool
  Let :: (Args a) => ArgAnnotation a -> a -> (a -> SMTExpr b) -> SMTExpr b
  App :: (Args arg,SMTType res) => SMTFunction arg res -> arg -> SMTExpr res
  Named :: SMTExpr a -> String -> SMTExpr a
  deriving Typeable

data UntypedExpr where
  UntypedExpr :: SMTType a => SMTExpr a -> UntypedExpr

entype :: (forall a. SMTType a => SMTExpr a -> b) -> UntypedExpr -> b
entype f (UntypedExpr x) = f x

data Sort' a = BoolSort
             | IntSort
             | RealSort
             | BVSort { bvSortWidth :: Integer
                      , bvSortUntyped :: Bool }
             | ArraySort [a] a
             | NamedSort String [a]
             deriving (Eq,Show,Functor,Foldable,Traversable)

type Sort = Fix Sort'

data Value = BoolValue Bool
           | IntValue Integer
           | RealValue (Ratio Integer)
           | BVValue { bvValueWidth :: Integer
                     , bvValueValue :: Integer }
           | ConstrValue String [Value] (Maybe Sort)
           deriving (Eq,Show)

data SMTFunction arg res where
  SMTEq :: SMTType a => SMTFunction [SMTExpr a] Bool
  SMTMap :: (Liftable arg,SMTType res,Args i) => SMTFunction arg res -> SMTFunction (Lifted arg i) (SMTArray i res)
  SMTFun :: (Liftable arg,SMTType res) => String -> SMTAnnotation res -> SMTFunction arg res
  SMTOrd :: (SMTType a) => SMTOrdOp -> SMTFunction (SMTExpr a,SMTExpr a) Bool
  SMTArith :: (SMTType a) => SMTArithOp -> SMTFunction [SMTExpr a] a
  SMTMinus :: (SMTType a) => SMTFunction (SMTExpr a,SMTExpr a) a
  SMTIntArith :: SMTIntArithOp -> SMTFunction (SMTExpr Integer,SMTExpr Integer) Integer
  SMTDivide :: SMTFunction (SMTExpr Rational,SMTExpr Rational) Rational
  SMTNeg :: (SMTType a) => SMTFunction (SMTExpr a) a
  SMTAbs :: (SMTType a) => SMTFunction (SMTExpr a) a
  SMTNot :: SMTFunction (SMTExpr Bool) Bool
  SMTLogic :: SMTLogicOp -> SMTFunction [SMTExpr Bool] Bool
  SMTDistinct :: SMTType a => SMTFunction [SMTExpr a] Bool
  SMTToReal :: SMTFunction (SMTExpr Integer) Rational
  SMTToInt :: SMTFunction (SMTExpr Rational) Integer
  SMTITE :: SMTType a => SMTFunction (SMTExpr Bool,SMTExpr a,SMTExpr a) a
  SMTBVComp :: SMTType (BitVector a) => SMTBVCompOp -> SMTFunction (SMTExpr (BitVector a),SMTExpr (BitVector a)) Bool
  SMTBVBin :: SMTType (BitVector a) => SMTBVBinOp -> SMTFunction (SMTExpr (BitVector a),SMTExpr (BitVector a)) (BitVector a)
  SMTBVUn :: SMTType (BitVector a) => SMTBVUnOp -> SMTFunction (SMTExpr (BitVector a)) (BitVector a)
  SMTSelect :: (Liftable i,SMTType v) => SMTFunction (SMTExpr (SMTArray i v),i) v
  SMTStore :: (Liftable i,SMTType v) => SMTFunction (SMTExpr (SMTArray i v),i,SMTExpr v) (SMTArray i v)
  SMTConstArray :: (Args i,SMTType v) => ArgAnnotation i -> SMTFunction (SMTExpr v) (SMTArray i v)
  SMTConcat :: (Concatable a b) => SMTFunction (SMTExpr (BitVector a),SMTExpr (BitVector b)) (BitVector (ConcatResult a b))
  SMTExtract :: (TypeableNat start,TypeableNat len,
                 Extractable from len')
                => Proxy start -> Proxy len -> SMTFunction (SMTExpr (BitVector from)) (BitVector len')
  SMTConstructor :: (Args arg,SMTType dt) => Constructor arg dt -> SMTFunction arg dt
  SMTConTest :: (Args arg,SMTType dt) => Constructor arg dt -> SMTFunction (SMTExpr dt) Bool
  SMTFieldSel :: (SMTRecordType a,SMTType f) => Field a f -> SMTFunction (SMTExpr a) f
  deriving (Typeable)

data SMTOrdOp
  = Ge
  | Gt
  | Le
  | Lt
  deriving (Typeable,Eq)

data SMTArithOp
  = Plus
  | Mult
  deriving (Typeable,Eq)

data SMTIntArithOp = Div
                   | Mod
                   | Rem
                   deriving (Typeable,Eq)

data SMTLogicOp = And
                | Or
                | XOr
                | Implies
                deriving (Typeable,Eq)

data SMTBVCompOp
  = BVULE
  | BVULT
  | BVUGE
  | BVUGT
  | BVSLE
  | BVSLT
  | BVSGE
  | BVSGT
  deriving (Typeable,Eq)

data SMTBVBinOp
  = BVAdd
  | BVSub
  | BVMul
  | BVURem
  | BVSRem
  | BVUDiv
  | BVSDiv
  | BVSHL
  | BVLSHR
  | BVASHR
  | BVXor
  | BVAnd
  | BVOr
  deriving (Typeable,Eq)

data SMTBVUnOp
  = BVNot 
  | BVNeg
  deriving (Typeable,Eq)

class (SMTValue (BitVector a)) => IsBitVector a where
  getBVSize :: Proxy a -> SMTAnnotation (BitVector a) -> Integer

class (IsBitVector a,IsBitVector b,IsBitVector (ConcatResult a b))
      => Concatable a b where
  type ConcatResult a b
  concatAnnotation :: a -> b
                      -> SMTAnnotation (BitVector a)
                      -> SMTAnnotation (BitVector b)
                      -> SMTAnnotation (BitVector (ConcatResult a b))

class (IsBitVector a,IsBitVector b) => Extractable a b where
  extractAnn :: a -> b -> Integer -> SMTAnnotation (BitVector a) -> SMTAnnotation (BitVector b)
  getExtractLen :: a -> b -> SMTAnnotation (BitVector b) -> Integer

instance Args arg => Eq (SMTFunction arg res) where
  (==) SMTEq SMTEq = True
  (==) (SMTMap f1) (SMTMap f2) = case cast f2 of
    Nothing -> False
    Just f2' -> f1 == f2'
  (==) (SMTFun f1 _) (SMTFun f2 _) = f1==f2
  (==) (SMTOrd op1) (SMTOrd op2) = op1==op2
  (==) (SMTArith op1) (SMTArith op2) = op1==op2
  (==) SMTMinus SMTMinus = True
  (==) (SMTIntArith op1) (SMTIntArith op2) = op1==op2
  (==) SMTDivide SMTDivide = True
  (==) SMTNeg SMTNeg = True
  (==) SMTAbs SMTAbs = True
  (==) SMTNot SMTNot = True
  (==) (SMTLogic op1) (SMTLogic op2) = op1==op2
  (==) SMTDistinct SMTDistinct = True
  (==) SMTToReal SMTToReal = True
  (==) SMTToInt SMTToInt = True
  (==) SMTITE SMTITE = True
  (==) (SMTBVComp op1) (SMTBVComp op2) = True
  (==) (SMTBVBin op1) (SMTBVBin op2) = True
  (==) (SMTBVUn op1) (SMTBVUn op2) = op1==op2
  (==) SMTSelect SMTSelect = True
  (==) SMTStore SMTStore = True
  (==) (SMTConstArray ann1) (SMTConstArray ann2) = ann1==ann2
  (==) SMTConcat SMTConcat = True
  (==) (SMTExtract start1 len1) (SMTExtract start2 len2) = case cast start2 of
    Just start2' -> start1 == start2'
    Nothing -> False
  (==) (SMTConTest con1) (SMTConTest con2) = case cast con2 of
    Just con2' -> con1==con2'
    Nothing -> False
  (==) (SMTFieldSel f1) (SMTFieldSel f2) = f1==f2
  (==) _ _ = False

instance Eq a => Eq (SMTExpr a) where
  (==) x y = case eqExpr 0 x y of
    Just True -> True
    _ -> False

eqExpr :: Integer -> SMTExpr a -> SMTExpr a -> Maybe Bool
eqExpr n lhs rhs = case (lhs,rhs) of
  (Var v1 _,Var v2 _) -> if v1 == v2
                         then Just True
                         else Nothing
  (Const v1 _,Const v2 _) -> Just $ v1 == v2
  (AsArray f1 arg1,AsArray f2 arg2) -> case cast f2 of
    Nothing -> Nothing
    Just f2' -> case cast arg2 of
      Nothing -> Nothing
      Just arg2' -> if f1 == f2' && arg1 == arg2'
                    then Just True
                    else Nothing
  (Forall a1 f1,Forall a2 f2) -> let name i = "internal_eq_check"++show i
                                     (n',v) = foldExprs (\i _ ann -> (i+1,Var (name i) ann)) n undefined a1
                                 in case cast (a2,f2) of
                                   Nothing -> Nothing
                                   Just (a2',f2') -> if a1==a2'
                                                     then eqExpr n' (f1 v) (f2' v)
                                                     else Nothing
  (Exists a1 f1,Exists a2 f2) -> let name i = "internal_eq_check"++show i
                                     (n',v) = foldExprs (\i _ ann -> (i+1,Var (name i) ann)) n undefined a1
                                 in case cast (a2,f2) of
                                   Nothing -> Nothing
                                   Just (a2',f2') -> if a1==a2'
                                                     then eqExpr n' (f1 v) (f2' v)
                                                     else Nothing
  (Let _ x1 f1,Let _ x2 f2) -> eqExpr n (f1 x1) (f2 x2)
  (Named e1 n1,Named e2 n2) -> if n1==n2
                               then eqExpr n e1 e2
                               else Nothing
  (App f1 arg1,App f2 arg2) -> case cast f2 of
      Nothing -> Nothing
      Just f2' -> case cast arg2 of
        Nothing -> Nothing
        Just arg2' -> if f1 == f2' && arg1 == arg2'
                      then Just True
                      else Nothing
  (_,_) -> Nothing

-- | Represents a constructor of a datatype /a/
--   Can be obtained by using the template haskell extension module
data Constructor arg res = Constructor String deriving (Eq,Show,Typeable)

-- | Represents a field of the datatype /a/ of the type /f/
data Field a f = Field String deriving (Eq,Show)

newtype InterpolationGroup = InterpolationGroup String

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print \"success\" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     | ProduceProofs Bool -- ^ Produce a proof of unsatisfiability after each failed checkSat
     | ProduceUnsatCores Bool -- ^ Enable the querying of unsatisfiable cores after a failed checkSat
     | ProduceInterpolants Bool -- ^ Enable the generation of craig interpolants
     deriving (Show,Eq,Ord)

data SMTInfo i where
  SMTSolverName :: SMTInfo String
  SMTSolverVersion :: SMTInfo String

-- | Instances of this class may be used as arguments for constructed functions and quantifiers.
class (Eq a,Typeable a,Eq (ArgAnnotation a),Typeable (ArgAnnotation a))
      => Args a where
  type ArgAnnotation a
  foldExprs :: (forall t. SMTType t => s -> SMTExpr t -> SMTAnnotation t -> (s,SMTExpr t))
               -> s -> a -> ArgAnnotation a -> (s,a)
  foldExprs f s x ann = let (s',[r]) = foldsExprs (\cs [(expr,ann')] -> let (cs',cr) = f cs expr ann'
                                                                        in (cs',[cr])
                                                  ) s [(x,ann)]
                        in (s',r)
  foldsExprs :: (forall t. SMTType t => s -> [(SMTExpr t,SMTAnnotation t)] -> (s,[SMTExpr t]))
                -> s -> [(a,ArgAnnotation a)] -> (s,[a])
  extractArgAnnotation :: a -> ArgAnnotation a
  toArgs :: [UntypedExpr] -> Maybe (a,[UntypedExpr])
  getSorts :: a -> ArgAnnotation a -> [Sort]
  getArgAnnotation :: a -> [Sort] -> (ArgAnnotation a,[Sort])

class (Args a) => Liftable a where
  type Lifted a i
  getLiftedArgumentAnn :: a -> i -> ArgAnnotation a -> ArgAnnotation i -> ArgAnnotation (Lifted a i)
  inferLiftedAnnotation :: a -> i -> ArgAnnotation (Lifted a i) -> (ArgAnnotation i,ArgAnnotation a)
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint :: Args i => p (a,i) -> Dict (Liftable (Lifted a i))
#endif

argSorts :: Args a => a -> ArgAnnotation a -> [Sort]
argSorts arg ann = Prelude.reverse res
    where
      (res,_) = foldExprs (\tps e ann' -> ((getSort (getUndef e) ann'):tps,e)) [] arg ann

unpackArgs :: Args a => (forall t. SMTType t => SMTExpr t -> SMTAnnotation t -> s -> (c,s)) -> a -> ArgAnnotation a -> s -> ([c],s)
unpackArgs f x ann i = fst $ foldExprs (\(res,ci) e ann' -> let (p,ni) = f e ann' ci
                                                            in ((res++[p],ni),e)
                                       ) ([],i) x ann

createArgs :: Args a => ArgAnnotation a -> Integer -> (a,[(String,Sort)],Integer)
createArgs ann i = let ((tps,ni),res) = foldExprs (\(tps',ci) e ann'
                                                   -> let name = "arg_"++show ci
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
  unliftArgs :: Monad m => a -> (forall t. SMTValue t => SMTExpr t -> m t) -> m (Unpacked a)

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust ((Just x):_) = Just x
firstJust (Nothing:xs) = firstJust xs

getUndef :: SMTExpr t -> t
getUndef _ = error "Don't evaluate the result of 'getUndef'"

getFunUndef :: SMTFunction arg res -> (arg,res)
getFunUndef _ = (error "Don't evaluate the first result of 'getFunUndef'",
                 error "Don't evaluate the second result of 'getFunUndef'")

getArrayUndef :: Args i => SMTExpr (SMTArray i v) -> (i,Unpacked i,v)
getArrayUndef _ = (undefined,undefined,undefined)

withSMTBackend :: SMTBackend b m => b -> SMT' m a -> m a
withSMTBackend backend act = withSMTBackend' (AnyBackend backend) act

withSMTBackend' :: AnyBackend m -> SMT' m a -> m a
withSMTBackend' backend@(AnyBackend b) f = do
  res <- evalStateT (runReaderT (runSMT f) backend)
         (SMTState { nameCount = Map.empty
                   , declaredDataTypes = emptyDataTypeInfo
                   , namedExprs = Map.empty })
  smtExit b
  return res

escapeName :: String -> String
escapeName (c:cs) = if isDigit c
                    then "num"++escapeName' (c:cs)
                    else escapeName' (c:cs)
escapeName [] = ""

escapeName' :: String -> String
escapeName' [] = []
escapeName' ('_':xs) = '_':'_':escapeName' xs
escapeName' (x:xs) = x:escapeName' xs

freeName :: Monad m => String -> SMT' m String
freeName name = do
  st <- getSMT
  let c = case Map.lookup name (nameCount st) of
        Nothing -> 0
        Just c' -> c'
  putSMT $ st { nameCount = Map.insert name (c+1) (nameCount st) }
  return $ (escapeName name)++(case c of
                                  0 -> ""
                                  _ -> "_"++show c)

argsSignature :: Args a => a -> ArgAnnotation a -> [Sort]
argsSignature arg ann
  = reverse $ fst $
    foldExprs (\sigs e ann' -> ((getSort (getUndef e) ann'):sigs,e))
    [] arg ann

{-
functionGetSignature :: (SMTFunction f)
                        => f
                        -> ArgAnnotation (SMTFunArg f)
                        -> SMTAnnotation (SMTFunRes f)
                        -> ([Sort],Sort)
functionGetSignature fun arg_ann res_ann
  = let ~(uarg,ures) = getFunUndef fun
    in (argsSignature uarg arg_ann,getSort ures res_ann)-}

{-
getSortParser :: Monad m => SMT' m SortParser
getSortParser = do
  st <- getSMT
  return $ mconcat $ fmap (withDeclaredType (\u _ -> fromSort u)) (Map.elems $ declaredTyCons st)
-}

argumentSortToSort :: Monad m => (Integer -> m Sort) -> ArgumentSort -> m Sort
argumentSortToSort f (Fix (ArgumentSort i)) = f i
argumentSortToSort f (Fix (NormalSort s)) = do
  res <- mapM (argumentSortToSort f) s
  return (Fix res)

declareType :: (Monad m,SMTType t) => t -> SMTAnnotation t -> SMT' m ()
declareType u ann = case asDataType u of
  Nothing -> return ()
  Just (dtName,dts) -> do
    let paramPrx = getProxyArgs u ann
    mapM_ (\dt
           -> dataTypeGetUndefined dt paramPrx $
              \und _ -> mapM (\con -> mapM (\field
                                            -> fieldGet field paramPrx und $
                                               \fval fann
                                               -> declareType fval fann
                                           ) (conFields con)
                             ) (dataTypeConstructors dt)
          ) (dataTypes dts)
    st <- getSMT
    if containsTypeCollection dts (declaredDataTypes st)
      then return ()
      else (do
               putSMT $ st { declaredDataTypes = addDataTypeStructure dts (declaredDataTypes st)
                           }
               smtBackend (\backend -> do
                              lift $ smtDeclareDataTypes backend dts))

-- Data type info

data DataTypeInfo = DataTypeInfo { structures :: [TypeCollection]
                                 , datatypes :: Map String (DataType,TypeCollection)
                                 , constructors :: Map String (Constr,DataType,TypeCollection)
                                 , fields :: Map String (DataField,Constr,DataType,TypeCollection) }

data TypeCollection = TypeCollection { argCount :: Integer
                                     , dataTypes :: [DataType]
                                     }

data ProxyArg = forall t. SMTType t => ProxyArg t (SMTAnnotation t)

withProxyArg :: ProxyArg -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withProxyArg (ProxyArg x ann) f = f x ann

data AnyValue = forall t. SMTType t => AnyValue t (SMTAnnotation t)

withAnyValue :: AnyValue -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withAnyValue (AnyValue x ann) f = f x ann

data DataType = DataType { dataTypeName :: String
                         , dataTypeConstructors :: [Constr]
                         , dataTypeGetUndefined
                           :: forall r. [ProxyArg]
                              -> (forall t. SMTType t => t -> SMTAnnotation t -> r)
                              -> r
                         }

data Constr = Constr { conName :: String
                     , conFields :: [DataField]
                     , construct :: forall r. Maybe [ProxyArg] -> [AnyValue]
                                    -> (forall t. SMTType t => t -> SMTAnnotation t -> r)
                                    -> r
                     , conTest :: forall t. SMTType t => [ProxyArg] -> t -> Bool
                     }

data DataField = DataField { fieldName :: String
                           , fieldSort :: ArgumentSort
                           , fieldGet :: forall r t. SMTType t => [ProxyArg] -> t
                                         -> (forall f. SMTType f => f -> SMTAnnotation f -> r)
                                         -> r
                           }

emptyDataTypeInfo :: DataTypeInfo
emptyDataTypeInfo = DataTypeInfo { structures = []
                                 , datatypes = Map.empty
                                 , constructors = Map.empty
                                 , fields = Map.empty }

containsTypeCollection :: TypeCollection -> DataTypeInfo -> Bool
containsTypeCollection struct dts = case dataTypes struct of
  dt:_ -> Map.member (dataTypeName dt) (datatypes dts)
  [] -> False

addDataTypeStructure :: TypeCollection -> DataTypeInfo -> DataTypeInfo
addDataTypeStructure struct dts
  = foldl (\cdts dt
            -> foldl (\cdts con
                      -> foldl (\cdts field
                                -> cdts { fields = Map.insert (fieldName field) (field,con,dt,struct) (fields cdts) }
                               ) (cdts { constructors = Map.insert (conName con) (con,dt,struct) (constructors cdts) })
                         (conFields con)
                     ) (cdts { datatypes = Map.insert (dataTypeName dt) (dt,struct) (datatypes cdts) })
               (dataTypeConstructors dt)
          ) (dts { structures = struct:(structures dts) }) (dataTypes struct)

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
    reifyExtract' t 0 0 1 f
      = reifyNat t $
        \(_::Proxy n1) -> f (Proxy::Proxy n1) (Proxy::Proxy Z) (Proxy::Proxy Z) (Proxy::Proxy (S Z))
    reifyExtract' t l u 0 f
      = reifyNat t $
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
  reflectNat :: Proxy a -> Integer -> Integer

instance TypeableNat Z where
  reflectNat _ = id

instance TypeableNat n => TypeableNat (S n) where
  reflectNat _ x = reflectNat (Proxy::Proxy n) (x+1)

type family Add n1 n2
type instance Add Z n = n
type instance Add (S n1) n2 = S (Add n1 n2)

data BVUntyped = BVUntyped deriving (Eq,Ord,Show,Typeable)
data BVTyped n = BVTyped deriving (Eq,Ord,Show,Typeable)

reifyNat :: (Num a,Ord a) => a -> (forall n. TypeableNat n => Proxy n -> r) -> r
reifyNat n f
  | n < 0 = error "smtlib2: Can only reify numbers >= 0."
  | otherwise = reifyNat' n f
  where
    reifyNat' :: (Num a,Eq a) => a -> (forall n. TypeableNat n => Proxy n -> r) -> r
    reifyNat' 0 f' = f' (Proxy::Proxy Z)
    reifyNat' n' f' = reifyNat' (n'-1) (f'.g)

    g :: Proxy n -> Proxy (S n)
    g _ = Proxy

reifySum :: (Num a,Ord a) => a -> a -> (forall n1 n2. (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2))
                                        => Proxy n1 -> Proxy n2 -> Proxy (Add n1 n2) -> r) -> r
reifySum n1 n2 f
  | n1 < 0 || n2 < 0 = error "smtlib2: Cann only reify numbers >= 0."
  | otherwise = reifySum' n1 n2 f
  where
    reifySum' :: (Num a,Ord a) => a -> a
                 -> (forall n1 n2. (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2))
                     => Proxy n1 -> Proxy n2 -> Proxy (Add n1 n2) -> r) -> r
    reifySum' 0 n2' f' = reifyNat n2' $ \(_::Proxy i) -> f' (Proxy::Proxy Z) (Proxy::Proxy i) (Proxy::Proxy i)
    reifySum' n1' n2' f' = reifySum' (n1'-1) n2' $ \(_::Proxy i1) (_::Proxy i2) (_::Proxy i3)
                                                   -> f' (Proxy::Proxy (S i1)) (Proxy::Proxy i2) (Proxy::Proxy (S i3))

reifyExtract :: (Num a,Ord a) => a -> a -> a
                -> (forall n1 n2 n3 n4. (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4,Add n4 n2 ~ S n3)
                    => Proxy n1 -> Proxy n2 -> Proxy n3 -> Proxy n4 -> r) -> r
reifyExtract t l u f
  | t <= u || l > u || l < 0 = error "smtlib2: Invalid extract parameters."
  | otherwise = reifyExtract' t l u (u - l + 1) f
  where
    reifyExtract' :: (Num a,Ord a) => a -> a -> a -> a
                     -> (forall n1 n2 n3 n4. (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4,Add n4 n2 ~ S n3)
                         => Proxy n1 -> Proxy n2 -> Proxy n3 -> Proxy n4 -> r) -> r
    reifyExtract' t' 0 0  1 f'
      = reifyNat t' $
        \(_::Proxy n1) -> f' (Proxy::Proxy n1) (Proxy::Proxy Z) (Proxy::Proxy Z) (Proxy::Proxy (S Z))
    reifyExtract' t' _ u' 0 f' = reifyNat t' $
                                 \(_::Proxy n1)
                                 -> reifyNat u' $
                                    \(_::Proxy n3)
                                    -> f' (Proxy::Proxy n1) (Proxy::Proxy (S n3)) (Proxy::Proxy n3) (Proxy::Proxy Z)
    reifyExtract' t' l' u' r' f' = reifyExtract' t' l' (u'-1) (r'-1) $
                                   \(_::Proxy n1) (_::Proxy n2) (_::Proxy n3) (_::Proxy n4)
                                   -> f' (Proxy::Proxy n1) (Proxy::Proxy n2) (Proxy::Proxy (S n3)) (Proxy::Proxy (S n4))

data BitVector (b :: *) = BitVector Integer deriving (Eq,Ord,Typeable)
#endif

instance Show (BitVector a) where
  show (BitVector x) = show x

instance Enum (BitVector a) where
  succ (BitVector x) = BitVector (succ x)
  pred (BitVector x) = BitVector (pred x)
  toEnum x = BitVector (toEnum x)
  fromEnum (BitVector x) = fromEnum x
  enumFrom (BitVector x) = [ BitVector y | y <- enumFrom x ]
  enumFromThen (BitVector x) (BitVector y)
    = [ BitVector z | z <- enumFromThen x y ]
  enumFromTo (BitVector x) (BitVector y)
    = [ BitVector z | z <- enumFromTo x y ]
  enumFromThenTo (BitVector x) (BitVector y) (BitVector z)
    = [ BitVector p | p <- enumFromThenTo x y z ]

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
