{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies #-}
module Language.SMTLib2 
       (SMT(),
        SMTType,
        SMTValue,
        SMTArith,
        SMTExpr,
        SMTOption(..),
        withSMTSolver,
        setOption,setLogic,
        assert,stack,
        checkSat,
        getValue,
        var,
        constant,
        (.==.),
        (.>=.),(.<.),
        distinct,
        plus,minus,mult,
        ite,
        and',not',
        select,store,arrayConst,unmangleArray,
        bvadd,bvsub,bvmul,
        forAll
       )
       where

import Data.Attoparsec
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.ByteString as BS
import Blaze.ByteString.Builder
import System.Process
import System.IO
import Data.Monoid
import Control.Monad.Reader
import Control.Monad.State
import Data.Text as T
import Data.Array
import Data.Word
import Numeric
import Data.Char
import Data.Bits

type SMT = ReaderT (Handle,Handle) (StateT Integer IO)

-- | Haskell types which can be represented in SMT
class SMTType t where
  getSort :: t -> L.Lisp

-- | Haskell values which can be represented as SMT constants
class SMTType t => SMTValue t where
  unmangle :: L.Lisp -> t
  mangle :: t -> L.Lisp

class (SMTValue t,Num t) => SMTArith t

class (SMTValue t,Bits t) => SMTBV t

instance SMTType Integer where
  getSort _ = L.Symbol "Int"

instance SMTValue Integer where
  unmangle (L.Number (L.I v)) = v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) = - v
  unmangle e = error $ "can't unmangle "++show e++" to Integer"
  mangle v = L.toLisp v

instance SMTArith Integer

instance SMTType Bool where
  getSort _ = L.Symbol "Bool"

instance SMTValue Bool where
  unmangle (L.Symbol "true") = True
  unmangle (L.Symbol "false") = False
  mangle True = L.Symbol "true"
  mangle False = L.Symbol "false"

instance (SMTType idx,SMTType val) => SMTType (Array idx val) where
  getSort u = L.List [L.Symbol "Array"
                     ,getSort (getIdx u)
                     ,getSort (getVal u)]
    where
      getIdx :: Array i v -> i
      getIdx _ = undefined
      getVal :: Array i v -> v
      getVal _ = undefined

bv :: Integer -> L.Lisp
bv n = L.List [L.Symbol "_"
              ,L.Symbol "BitVec"
              ,L.Number $ L.I n]

instance SMTType Word8 where
  getSort _ = bv 8

getBVValue :: Num a => L.Lisp -> a
getBVValue (L.Number (L.I v)) = fromInteger v
getBVValue (L.Symbol s) = case T.unpack s of
  '#':'b':rest -> let [(v,_)] = readInt 2 (\x -> x=='0' || x=='1') (\x -> if x=='0' then 0 else 1) rest in v
  '#':'x':rest -> let [(v,_)] = readHex rest in v

putBVValue :: Bits a => a -> L.Lisp
putBVValue x = L.Symbol (T.pack ('#':'b':[ if testBit x i
                                           then '1'
                                           else '0' | i <- Prelude.reverse [0..((bitSize x)-1)] ]))

instance SMTValue Word8 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word8

instance SMTType Word16 where
  getSort _ = bv 16

instance SMTValue Word16 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word16

instance SMTType Word32 where
  getSort _ = bv 32

instance SMTValue Word32 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word32

instance SMTType Word64 where
  getSort _ = bv 64

instance SMTValue Word64 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word64

-- | An abstract SMT expression
data SMTExpr t where
  Var :: SMTType t => Text -> SMTExpr t
  Const :: SMTValue t => t -> SMTExpr t
  Eq :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Ge :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Lt :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
  Plus :: SMTArith t => [SMTExpr t] -> SMTExpr t
  Minus :: SMTArith t => SMTExpr t -> SMTExpr t -> SMTExpr t
  Mult :: SMTArith t => [SMTExpr t] -> SMTExpr t
  ITE :: SMTExpr Bool -> SMTExpr t -> SMTExpr t -> SMTExpr t
  And :: [SMTExpr Bool] -> SMTExpr Bool
  Not :: SMTExpr Bool -> SMTExpr Bool
  Select :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v
  Store :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v -> SMTExpr (Array i v)
  BVAdd :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  BVSub :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  BVMul :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  Forall :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
  Fun :: (Args a b,SMTType r) => Text -> SMTExpr (b -> r)
  App :: (Args a b,SMTType r) => SMTExpr (b -> r) -> a -> SMTExpr r

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print "success" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     deriving (Show,Eq,Ord)

class Args a b | a -> b where
  createArgs :: Integer -> (a,[(Text,L.Lisp)],Integer)
  unpackArgs :: a -> Integer -> ([L.Lisp],Integer)

instance SMTType a => Args (SMTExpr a) a where
  createArgs c = let n1 = T.pack $ "f"++show c
                     v1 = Var n1
                     t1 = getSort $ getUndef v1
                 in (v1,[(n1,t1)],c+1)
  unpackArgs e c = let (e',c') = exprToLisp e c
                   in ([e'],c)

instance (SMTType a,SMTType b) => Args (SMTExpr a,SMTExpr b) (a,b) where
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     v1 = Var n1
                     v2 = Var n2
                     t1 = getSort $ getUndef v1
                     t2 = getSort $ getUndef v2
                 in ((v1,v2),[(n1,t1),(n2,t2)],c+2)
  unpackArgs (e1,e2) c = let (r1,c1) = exprToLisp e1 c
                             (r2,c2) = exprToLisp e2 c1
                         in ([r1,r2],c2)

instance SMTValue t => Eq (SMTExpr t) where
  (==) x y = (L.toLisp x) == (L.toLisp y)

instance SMTValue t => Show (SMTExpr t) where
  show x = show (L.toLisp x)

instance Num (SMTExpr Integer) where
  fromInteger = constant
  (+) x y = plus [x,y]
  (-) = minus
  (*) x y = mult [x,y]

instance Num (SMTExpr Word8) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

instance Num (SMTExpr Word16) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

instance Num (SMTExpr Word32) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

instance Num (SMTExpr Word64) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

exprsToLisp :: [SMTExpr t] -> Integer -> ([L.Lisp],Integer)
exprsToLisp [] c = ([],c)
exprsToLisp (e:es) c = let (e',c') = exprToLisp e c
                           (es',c'') = exprsToLisp es c'
                       in (e':es',c'')

exprToLisp :: SMTExpr t -> Integer -> (L.Lisp,Integer)
exprToLisp (Var name) c = (L.Symbol name,c)
exprToLisp (Const x) c = (mangle x,c)
exprToLisp (Eq l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "=",l',r'],c'')
exprToLisp (Distinct lst) c = let (lst',c') = exprsToLisp lst c
                              in (L.List $ [L.Symbol "distinct"] ++ lst',c')
exprToLisp (Plus lst) c = let (lst',c') = exprsToLisp lst c
                          in (L.List $ [L.Symbol "+"] ++ lst',c')
exprToLisp (Mult lst) c = let (lst',c') = exprsToLisp lst c
                          in (L.List $ [L.Symbol "*"] ++ lst',c')
exprToLisp (Minus l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "-",l',r'],c'')
exprToLisp (ITE cond tt ff) c = let (cond',c') = exprToLisp cond c
                                    (tt',c'') = exprToLisp tt c'
                                    (ff',c''') = exprToLisp ff c''
                                in (L.List [L.Symbol "ite",cond',tt',ff'],c''')
exprToLisp (Ge l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol ">=",l',r'],c'')
exprToLisp (Lt l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "<",l',r'],c'')
exprToLisp (And lst) c = let (lst',c') = exprsToLisp lst c
                         in (L.List $ [L.Symbol "and"] ++ lst',c')
exprToLisp (Not expr) c = let (expr',c') = exprToLisp expr c
                          in (L.List [L.Symbol "not",expr'],c')
exprToLisp (Select arr idx) c = let (arr',c') = exprToLisp arr c
                                    (idx',c'') = exprToLisp idx c'
                                in (L.List [L.Symbol "select",arr',idx'],c'')
exprToLisp (Store arr idx val) c = let (arr',c') = exprToLisp arr c
                                       (idx',c'') = exprToLisp idx c''
                                       (val',c''') = exprToLisp val c'''
                                   in (L.List [L.Symbol "store",arr',idx',val'],c''')
exprToLisp (BVAdd l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvadd",l',r'],c'')
exprToLisp (BVSub l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsub",l',r'],c'')
exprToLisp (BVMul l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvmul",l',r'],c'')
exprToLisp (Forall f) c = let (arg,tps,nc) = createArgs c
                              (arg',nc') = exprToLisp (f arg) nc
                          in (L.List [L.Symbol "forall"
                                     ,L.List [L.List [L.Symbol name
                                                     ,tp
                                                     ]
                                             | (name,tp) <- tps
                                             ]
                                     ,arg'],nc')
exprToLisp (Fun name) c = (L.Symbol name,c)
exprToLisp (App f x) c = let (f',c') = exprToLisp f c
                             (x',c'') = unpackArgs x c
                         in (L.List $ f':x',c'')

instance L.ToLisp (SMTExpr t) where
  toLisp e = fst $ exprToLisp e 0

getUndef :: SMTExpr t -> t
getUndef _ = undefined

-- | Set an option for the underlying SMT solver
setOption :: SMTOption -> SMT ()
setOption opt = putRequest $ L.List $ [L.Symbol "set-option"]
                ++(case opt of
                      PrintSuccess v -> [L.Symbol ":print-success"                                                                   
                                        ,mangle v]
                      ProduceModels v -> [L.Symbol ":produce-models"
                                         ,mangle v])

-- | Create a fresh new variable
var :: SMTType t => SMT (SMTExpr t)
var = do
  c <- get
  put (c+1)
  let name = T.pack $ "var"++show c
      res = Var name
      sort = getSort $ getUndef res
  declareFun name [] sort
  return res

{-
fun :: (Args a b,SMTType r) => SMT (SMTExpr (b -> r))
fun = do
  c <- get
  put (c+1)
  let name = T.pack $ "fun"++show c
      res = Fun name
      
      getFunArgs :: SMTExpr (b -> r) -> (b,r)
      getFunArgs _ = (undefined,undefined)
      
      (tp,rtp) = getFunArgs res
      
      args :: (a,[(Text,L.Lisp)],Integer)
      args = createArgs 0
      (_,tp,_) = args
      rtp :: r
      rtp = undefined
  declareFun name [ l | (_,l) <- tp ] (getSort rtp)
  return res
  -}    

-- | A constant expression
constant :: SMTValue t => t -> SMTExpr t
constant = Const

-- | Two expressions shall be equal
(.==.) :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.==.) = Eq

infix 4 .==.

(.>=.),(.<.) :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.>=.) = Ge
(.<.) = Lt

infix 4 .>=.
infix 4 .<.

distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
distinct = Distinct

plus,mult :: (SMTArith a) => [SMTExpr a] -> SMTExpr a
plus = Plus
mult = Mult

minus :: (SMTArith a) => SMTExpr a -> SMTExpr a -> SMTExpr a
minus = Minus

ite :: (SMTType a) => SMTExpr Bool -> SMTExpr a -> SMTExpr a -> SMTExpr a
ite = ITE

and' :: [SMTExpr Bool] -> SMTExpr Bool
and' = And

not' :: SMTExpr Bool -> SMTExpr Bool
not' = Not

select :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v
select = Select

store :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v -> SMTExpr (Array i v)
store = Store

arrayConst :: (SMTValue i,SMTValue v,Ix i) => SMTExpr (Array i v) -> Array i v -> SMTExpr Bool
arrayConst expr arr = and' [(select expr (constant i)) .==. (constant v)
                           | (i,v) <- assocs arr ]

unmangleArray :: (Ix i,SMTValue i,SMTValue v) => (i,i) -> SMTExpr (Array i v) -> SMT (Array i v)
unmangleArray b expr = mapM (\i -> do
                                v <- getValue (select expr (constant i))
                                return (i,v)
                            ) (range b) >>= return.array b

bvadd,bvsub,bvmul :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvadd = BVAdd
bvsub = BVSub
bvmul = BVMul

forAll :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
forAll = Forall

getValue :: SMTValue t => SMTExpr t -> SMT t
getValue expr = do
  clearInput
  putRequest $ L.List [L.Symbol "get-value"
                      ,L.List [L.toLisp expr]]
  val <- parseResponse
  case val of
    L.List [L.List [_,res]] -> return $ unmangle res
    _ -> error $ "unknown response to get-value: "++show val

assert :: SMTExpr Bool -> SMT ()
assert expr 
  = putRequest $ L.List [L.Symbol "assert"
                        ,L.toLisp expr]

setLogic :: Text -> SMT ()
setLogic name = putRequest $ L.List [L.Symbol "set-logic"
                                    ,L.Symbol name]

declareFun :: Text -> [L.Lisp] -> L.Lisp -> SMT ()
declareFun name tps rtp
  = putRequest $ L.List [L.Symbol "declare-fun"
                        ,L.Symbol name
                        ,args tps
                        ,rtp
                        ]

args :: [L.Lisp] -> L.Lisp
args [] = L.Symbol "()"
args xs = L.List xs

checkSat :: SMT Bool
checkSat = do
  (_,hout) <- ask
  clearInput
  putRequest (L.List [L.Symbol "check-sat"])
  res <- liftIO $ BS.hGetLine hout
  case res of
    "sat" -> return True
    "unsat" -> return False
    _ -> error $ "unknown check-sat response: "++show res
  
stack :: SMT a -> SMT a
stack act = do
  putRequest (L.List [L.Symbol "push"])
  res <- act
  putRequest (L.List [L.Symbol "pop"])
  return res

withSMTSolver :: FilePath -> [String] -> SMT a -> IO a
withSMTSolver solver args f = do
  let cmd = CreateProcess { cmdspec = RawCommand solver args
                          , cwd = Nothing
                          , env = Nothing
                          , std_in = CreatePipe
                          , std_out = CreatePipe
                          , std_err = Inherit
                          , close_fds = False
                          }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  res <- evalStateT (runReaderT (do
                                 res <- f
                                 putRequest (L.List [L.Symbol "exit"])
                                 return res
                                ) (hin,hout)) 0
  hClose hin
  hClose hout
  terminateProcess handle
  waitForProcess handle
  return res

clearInput :: SMT ()
clearInput = do
  (_,hout) <- ask
  r <- liftIO $ hReady hout
  if r
    then (do
             liftIO $ BS.hGetSome hout 1024
             clearInput)
    else return ()

putRequest :: L.Lisp -> SMT ()
putRequest e = do
  (hin,_) <- ask
  liftIO $ toByteStringIO (BS.hPutStr hin) (mappend (L.fromLisp e) flush)
  liftIO $ BS.hPutStrLn hin ""
  liftIO $ hFlush hin

parseResponse :: SMT L.Lisp
parseResponse = do
  (_,hout) <- ask
  str <- liftIO $ BS.hGetLine hout
  let continue (Done _ r) = return r
      continue res@(Partial _) = do
        str <- BS.hGetLine hout
        continue (feed res str)
      continue (Fail str ctx msg) = error $ "Error parsing "++show str++" response in "++show ctx++": "++msg
  liftIO $ continue $ parse L.lisp str