{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies #-}
module Language.SMTLib2.Internals where

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
import Data.Bits
import Data.Typeable
import Data.Foldable (foldlM)

type SMT = ReaderT (Handle,Handle) (StateT (Integer,[TypeRep]) IO)

-- | Haskell types which can be represented in SMT
class SMTType t where
  getSort :: t -> L.Lisp
  declareType :: t -> [(TypeRep,SMT ())]

-- | Haskell values which can be represented as SMT constants
class SMTType t => SMTValue t where
  unmangle :: L.Lisp -> t
  mangle :: t -> L.Lisp

class (SMTValue t,Num t) => SMTArith t

class (SMTValue t,Bits t) => SMTBV t

data SMTFun a b r = SMTFun

-- | An abstract SMT expression
data SMTExpr t where
  Var :: SMTType t => Text -> SMTExpr t
  Const :: SMTValue t => t -> SMTExpr t
  Eq :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Ge :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Gt :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Le :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Lt :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
  Plus :: SMTArith t => [SMTExpr t] -> SMTExpr t
  Minus :: SMTArith t => SMTExpr t -> SMTExpr t -> SMTExpr t
  Mult :: SMTArith t => [SMTExpr t] -> SMTExpr t
  Div :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
  Mod :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
  Divide :: SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational
  Neg :: SMTArith t => SMTExpr t -> SMTExpr t
  Abs :: SMTArith t => SMTExpr t -> SMTExpr t
  ITE :: SMTExpr Bool -> SMTExpr t -> SMTExpr t -> SMTExpr t
  And :: [SMTExpr Bool] -> SMTExpr Bool
  Or :: [SMTExpr Bool] -> SMTExpr Bool
  XOr :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
  Implies :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
  Not :: SMTExpr Bool -> SMTExpr Bool
  Select :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v
  Store :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v -> SMTExpr (Array i v)
  BVAdd :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  BVSub :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  BVMul :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  BVURem :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  BVSRem :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
  Forall :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
  Exists :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
  Fun :: (Args a b,SMTType r) => Text -> SMTExpr (SMTFun a b r)
  App :: (Args a b,SMTType r) => SMTExpr (SMTFun a b r) -> a -> SMTExpr r
  ConTest :: Constructor a -> SMTExpr a -> SMTExpr Bool
  FieldSel :: Field a f -> SMTExpr a -> SMTExpr f

data Constructor a = Constructor Text

data Field a f = Field Text

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print "success" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     deriving (Show,Eq,Ord)

class Args a b | a -> b where
  createArgs :: Integer -> (a,[(Text,L.Lisp)],Integer)
  unpackArgs :: a -> b -> Integer -> ([L.Lisp],Integer)

instance SMTValue t => Eq (SMTExpr t) where
  (==) x y = (L.toLisp x) == (L.toLisp y)

instance Show (SMTExpr t) where
  show x = show (L.toLisp x)

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
exprToLisp (Div l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "div",l',r'],c'')
exprToLisp (Divide l r) c = let (l',c') = exprToLisp l c
                                (r',c'') = exprToLisp r c'
                            in (L.List [L.Symbol "/",l',r'],c'')
exprToLisp (Mod l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "mod",l',r'],c'')
exprToLisp (Neg e) c = let (e',c') = exprToLisp e c
                       in (L.List [L.Symbol "-",e'],c')
exprToLisp (Abs e) c = let (e',c') = exprToLisp e c
                       in (L.List [L.Symbol "abs",e'],c')
exprToLisp (ITE cond tt ff) c = let (cond',c') = exprToLisp cond c
                                    (tt',c'') = exprToLisp tt c'
                                    (ff',c''') = exprToLisp ff c''
                                in (L.List [L.Symbol "ite",cond',tt',ff'],c''')
exprToLisp (Ge l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol ">=",l',r'],c'')
exprToLisp (Gt l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol ">",l',r'],c'')
exprToLisp (Le l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "<=",l',r'],c'')
exprToLisp (Lt l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "<",l',r'],c'')
exprToLisp (And lst) c = let (lst',c') = exprsToLisp lst c
                         in (L.List $ [L.Symbol "and"] ++ lst',c')
exprToLisp (Or lst) c = let (lst',c') = exprsToLisp lst c
                        in (L.List $ [L.Symbol "or"] ++ lst',c')
exprToLisp (XOr l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "xor",l',r'],c'')
exprToLisp (Implies l r) c = let (l',c') = exprToLisp l c
                                 (r',c'') = exprToLisp r c'
                             in (L.List [L.Symbol "=>",l',r'],c'')
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
                                     ,L.List [L.List [L.Symbol name,tp]
                                             | (name,tp) <- tps]
                                     ,arg'],nc')
exprToLisp (Exists f) c = let (arg,tps,nc) = createArgs c
                              (arg',nc') = exprToLisp (f arg) nc
                          in (L.List [L.Symbol "exists"
                                     ,L.List [L.List [L.Symbol name,tp]
                                             | (name,tp) <- tps ]
                                     ,arg'],nc')
exprToLisp (Fun name) c = (L.Symbol name,c)
exprToLisp (App f x) c = let (_,bu,ru) = getFunUndef f
                             (f',c') = exprToLisp f c
                             (x',c'') = unpackArgs x bu c
                         in (L.List $ f':x',c'')
exprToLisp (ConTest (Constructor name) e) c = let (e',c') = exprToLisp e c
                                              in (L.List [L.Symbol $ T.append "is-" name
                                                         ,e'],c')
exprToLisp (FieldSel (Field name) e) c = let (e',c') = exprToLisp e c
                                         in (L.List [L.Symbol name,e'],c')

instance L.ToLisp (SMTExpr t) where
  toLisp e = fst $ exprToLisp e 0

getUndef :: SMTExpr t -> t
getUndef _ = undefined

getFunUndef :: SMTExpr (SMTFun a b r) -> (a,b,r)
getFunUndef _ = (undefined,undefined,undefined)

-- | Set an option for the underlying SMT solver
setOption :: SMTOption -> SMT ()
setOption opt = putRequest $ L.List $ [L.Symbol "set-option"]
                ++(case opt of
                      PrintSuccess v -> [L.Symbol ":print-success"
                                        ,L.Symbol $ if v then "true" else "false"]
                      ProduceModels v -> [L.Symbol ":produce-models"
                                         ,L.Symbol $ if v then "true" else "false"])

-- | Create a new named variable
varNamed :: SMTType t => Text -> SMT (SMTExpr t)
varNamed name = do
  let res = Var name
      sort = getSort $ getUndef res
      tps = declareType $ getUndef res
  (c,decl) <- get
  ndecl <- foldlM (\decl (tp,act) -> if Prelude.elem tp decl
                                     then return decl
                                     else (do
                                              act
                                              return $ tp:decl)) decl (Prelude.reverse tps)
  put (c,ndecl)
  declareFun name [] sort
  return res
  

-- | Create a fresh new variable
var :: SMTType t => SMT (SMTExpr t)
var = do
  (c,decl) <- get
  let name = T.pack $ "var"++show c
  res <- varNamed name
  put (c+1,decl)
  return res

-- | Create a new uninterpreted function
fun :: (Args a b,SMTType r) => SMT (SMTExpr (SMTFun a b r))
fun = do
  (c,decl) <- get
  put (c+1,decl)
  let name = T.pack $ "fun"++show c
      res = Fun name
      
      (au,bu,rtp) = getFunUndef res
      
      assertEq :: x -> x -> y -> y
      assertEq _ _ p = p
      
      (au2,tps,_) = createArgs 0
      
  assertEq au au2 $ return ()
  declareFun name [ l | (_,l) <- tps ] (getSort rtp)
  return res
    
-- | Define a new function with a body
defFun :: (Args a b,SMTType r) => (a -> SMTExpr r) -> SMT (SMTExpr (SMTFun a b r))
defFun f = do
  (c,decl) <- get
  put (c+1,decl)
  let name = T.pack $ "fun"++show c
      res = Fun name
      
      (au,bu,rtp) = getFunUndef res
      
      (au2,tps,_) = createArgs 0
      
      (expr',_) = exprToLisp (f au2) 0
  defineFun name tps (getSort rtp) expr'
  return res

-- | Apply a function to an argument
app :: (Args a b,SMTType r) => SMTExpr (SMTFun a b r) -> a -> SMTExpr r
app = App

-- | A constant expression
constant :: SMTValue t => t -> SMTExpr t
constant = Const

-- | Two expressions shall be equal
(.==.) :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.==.) = Eq

infix 4 .==.

(.>=.),(.>.),(.<=.),(.<.) :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.>=.) = Ge
(.>.) = Gt
(.<=.) = Le
(.<.) = Lt

infix 4 .>=.
infix 4 .<.

-- | Declares all arguments to be distinct
distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
distinct = Distinct

plus,mult :: (SMTArith a) => [SMTExpr a] -> SMTExpr a
plus = Plus
mult = Mult

minus :: (SMTArith a) => SMTExpr a -> SMTExpr a -> SMTExpr a
minus = Minus

div',mod' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
div' = Div
mod' = Mod

divide :: SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational
divide = Divide

neg,abs' :: SMTArith a => SMTExpr a -> SMTExpr a
neg = Neg
abs' = Abs

ite :: (SMTType a) => SMTExpr Bool -> SMTExpr a -> SMTExpr a -> SMTExpr a
ite = ITE

and',or' :: [SMTExpr Bool] -> SMTExpr Bool
and' = And
or' = Or

xor,(.=>.) :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
xor = XOr
(.=>.) = Implies

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

forAll,exists :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
forAll = Forall
exists = Exists

is :: SMTType a => SMTExpr a -> Constructor a -> SMTExpr Bool
is e con = ConTest con e

(.#) :: SMTType a => SMTExpr a -> Field a f -> SMTExpr f
(.#) e f = FieldSel f e

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
assert expr = assert' (L.toLisp expr)

assert' :: L.Lisp -> SMT ()
assert' expr = putRequest $ L.List [L.Symbol "assert"
                                   ,expr]

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
                              | (conName,fields) <- cons ]
                         | (name,cons) <- dts ]
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
    "sat\r" -> return True
    "unsat" -> return False
    "unsat\r" -> return False
    _ -> error $ "unknown check-sat response: "++show res
  
stack :: SMT a -> SMT a
stack act = do
  putRequest (L.List [L.Symbol "push"])
  res <- act
  putRequest (L.List [L.Symbol "pop"])
  return res

withSMTSolver :: String -> SMT a -> IO a
withSMTSolver solver f = do
  let cmd = CreateProcess { cmdspec = ShellCommand solver
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
                                ) (hin,hout)) (0,[])
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
  liftIO $ toByteStringIO (BS.hPutStr hin) (mappend (L.fromLispExpr e) flush)
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