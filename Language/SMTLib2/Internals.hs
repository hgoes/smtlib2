{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies,RankNTypes,DeriveDataTypeable,TypeSynonymInstances #-}
module Language.SMTLib2.Internals where

import Data.Attoparsec
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.ByteString as BS
import Blaze.ByteString.Builder
import System.Process
import System.IO as IO
import Data.Monoid
import Control.Monad.Reader
import Control.Monad.State
import Data.Text as T
import Data.Array
import Data.Bits
import Data.Typeable
import Data.Foldable (foldlM)
import Data.Map as Map hiding (assocs)
import Data.Set as Set
import Data.List as List (genericReplicate,mapAccumL)

-- | The SMT monad used for communating with the SMT solver
type SMT = ReaderT (Handle,Handle) (StateT (Integer,[TypeRep],Map T.Text TypeRep) IO)

-- | Haskell types which can be represented in SMT
class SMTType t where
  getSort :: t -> L.Lisp
  declareType :: t -> [(TypeRep,SMT ())]

-- | Haskell values which can be represented as SMT constants
class SMTType t => SMTValue t where
  unmangle :: L.Lisp -> Maybe t
  mangle :: t -> L.Lisp

-- | A type class for all types which support arithmetic operations in SMT
class (SMTValue t,Num t) => SMTArith t

-- | A type class for all types which support bitvector operations in SMT
class (SMTValue t,Bits t) => SMTBV t

-- | Represents a function in the SMT solver. /a/ is the argument of the function in SMT terms, /b/ is the argument in haskell types and /r/ is the result type of the function.
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
  BVULE :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVULT :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVUGE :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVUGT :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVSLE :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVSLT :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVSGE :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  BVSGT :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
  Forall :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
  ForallList :: Args a b => Integer -> ([a] -> SMTExpr Bool) -> SMTExpr Bool
  Exists :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
  Let :: SMTType a => SMTExpr a -> (SMTExpr a -> SMTExpr b) -> SMTExpr b
  Lets :: SMTType a => [SMTExpr a] -> ([SMTExpr a] -> SMTExpr b) -> SMTExpr b
  Fun :: (Args a b,SMTType r) => Text -> SMTExpr (SMTFun a b r)
  App :: (Args a b,SMTType r) => SMTExpr (SMTFun a b r) -> a -> SMTExpr r
  ConTest :: Constructor a -> SMTExpr a -> SMTExpr Bool
  FieldSel :: Field a f -> SMTExpr a -> SMTExpr f
  Head :: SMTExpr [a] -> SMTExpr a
  Tail :: SMTExpr [a] -> SMTExpr [a]
  Insert :: SMTExpr a -> SMTExpr [a] -> SMTExpr [a]
  Named :: SMTExpr a -> Text -> SMTExpr a
  InternalFun :: [L.Lisp] -> SMTExpr (SMTFun (SMTExpr Bool) Bool Bool)
  Undefined :: SMTExpr a
  deriving Typeable

-- | Represents a constructor of a datatype /a/
--   Can be obtained by using the template haskell extension module
data Constructor a = Constructor Text

-- | Represents a field of the datatype /a/ of the type /f/
data Field a f = Field Text

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print \"success\" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     | ProduceProofs Bool -- ^ Produce a proof of unsatisfiability after each failed checkSat
     deriving (Show,Eq,Ord)

-- | A piece of information of type /r/ that can be obtained by the SMT solver
class SMTInfo i r | i -> r where
  getInfo :: i -> SMT r

-- | The name of the SMT solver
data SMTSolverName = SMTSolverName deriving (Show,Eq,Ord)

instance SMTInfo SMTSolverName String where
  getInfo _ = do
    putRequest (L.List [L.Symbol "get-info",L.Symbol ":name"])
    res <- parseResponse
    case res of
      L.List [L.Symbol ":name",L.String name] -> return $ T.unpack name

-- | The version of the SMT solver
data SMTSolverVersion = SMTSolverVersion deriving (Show,Eq,Ord)

instance SMTInfo SMTSolverVersion String where
  getInfo _ = do
    putRequest (L.List [L.Symbol "get-info",L.Symbol ":version"])
    res <- parseResponse
    case res of
      L.List [L.Symbol ":version",L.String name] -> return $ T.unpack name

-- | Instances of this class may be used as arguments for constructed functions and quantifiers.
class Args a b | a -> b where
  createArgs :: Integer -> (a,[(Text,L.Lisp)],Integer)
  unpackArgs :: a -> b -> Integer -> ([L.Lisp],Integer)
  foldExprs :: (forall t. s -> SMTExpr t -> s) -> s -> a -> s
  allOf :: (forall t. SMTExpr t) -> a

instance SMTValue t => Eq (SMTExpr t) where
  (==) x y = (L.toLisp x) == (L.toLisp y)

instance Show (SMTExpr t) where
  show x = show (L.toLisp x)

-- Bool

instance SMTType Bool where
  getSort _ = L.Symbol "Bool"
  declareType u = [(typeOf u,return ())]

instance SMTValue Bool where
  unmangle (L.Symbol "true") = Just True
  unmangle (L.Symbol "false") = Just False
  unmangle _ = Nothing
  mangle True = L.Symbol "true"
  mangle False = L.Symbol "false"

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
exprToLisp (BVULE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvule",l',r'],c'')
exprToLisp (BVULT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvult",l',r'],c'')
exprToLisp (BVUGE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvuge",l',r'],c'')
exprToLisp (BVUGT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvugt",l',r'],c'')
exprToLisp (BVSLE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsle",l',r'],c'')
exprToLisp (BVSLT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvslt",l',r'],c'')
exprToLisp (BVSGE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsge",l',r'],c'')
exprToLisp (BVSGT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsgt",l',r'],c'')
exprToLisp (Forall f) c = let (arg,tps,nc) = createArgs c
                              (arg',nc') = exprToLisp (f arg) nc
                          in (L.List [L.Symbol "forall"
                                     ,L.List [L.List [L.Symbol name,tp]
                                             | (name,tp) <- tps]
                                     ,arg'],nc')
exprToLisp (ForallList i f) c
  = let (args,tps,nc) = Prelude.foldl (\(cargs,ctps,cnc) _ -> let (arg,tp,nnc) = createArgs cnc
                                                              in (arg:cargs,tp++ctps,nnc)
                                      ) ([],[],c) [1..i]
        (arg',nc') = exprToLisp (f args) nc
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
exprToLisp (Let x f) c = let (arg,nc) = exprToLisp x c
                             name = T.pack $ "l"++show nc
                             (arg',nc') = exprToLisp (f (Var name)) (nc+1)
                         in (L.List [L.Symbol "let"
                                    ,L.List [L.List [L.Symbol name,arg]]
                                    ,arg'],nc')
exprToLisp (Lets xs f) c = let (nc,xs') = List.mapAccumL (\cc x -> let (x',cc') = exprToLisp x cc
                                                                       name = T.pack $ "l"++show cc'
                                                                   in (cc'+1,(name,x'))) c xs
                           in (L.List [L.Symbol "let"
                                      ,L.List [L.List [L.Symbol name,arg]
                                              | (name,arg) <- xs']],nc)
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
exprToLisp (Head xs) c = let (e,c') = exprToLisp xs c
                         in (L.List [L.Symbol "head",e],c')
exprToLisp (Tail xs) c = let (e,c') = exprToLisp xs c
                         in (L.List [L.Symbol "tail",e],c')
exprToLisp (Insert x xs) c = let (x',c') = exprToLisp x c
                                 (xs',c'') = exprToLisp xs c'
                             in (L.List [L.Symbol "insert",x',xs'],c'')
exprToLisp (Named expr name) c = let (expr',c') = exprToLisp expr c
                                 in (L.List [L.Symbol "!",expr',L.Symbol ":named",L.Symbol name],c')
exprToLisp (InternalFun args) c = (L.List (L.Symbol "_":args),c)

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Nothing:rest) = firstJust rest
firstJust ((Just x):rest) = Just x

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
                                         ,L.Symbol $ if v then "true" else "false"]
                      ProduceProofs v -> [L.Symbol ":produce-proofs"
                                         ,L.Symbol $ if v then "true" else "false"])

-- | Create a new named variable
varNamed :: (SMTType t,Typeable t) => Text -> SMT (SMTExpr t)
varNamed name = mfix (\e -> varNamed' (getUndef e) name)

varNamed' :: (SMTType t,Typeable t) => t -> Text -> SMT (SMTExpr t)
varNamed' u name = do
  let sort = getSort u
      tps = declareType u
  modify $ \(c,decl,mp) -> (c,decl,Map.insert name (typeOf u) mp)
  mapM_ (\(tp,act) -> do
            (c,decl,_) <- get
            if Prelude.elem tp decl
              then return ()
              else (do
                       act
                       modify (\(c',decl',mp') -> (c',tp:decl',mp'))
                   )
        ) (Prelude.reverse tps)
  declareFun name [] sort
  return (Var name)

-- | Create a fresh new variable
var :: (SMTType t,Typeable t) => SMT (SMTExpr t)
var = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "var"++show c
  res <- varNamed name
  return res

-- | Create a new uninterpreted function
fun :: (Args a b,SMTType r) => SMT (SMTExpr (SMTFun a b r))
fun = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
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
  (c,decl,mp) <- get
  put (c+1,decl,mp)
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

-- | Greater-or-equal function
(.>=.) :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.>=.) = Ge

-- | Greater-than function
(.>.) :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.>.) = Gt

-- | Less-or-equal function
(.<=.) :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.<=.) = Le

-- | Less-than function
(.<.) :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.<.) = Lt

infix 4 .>=.
infix 4 .<.

-- | Declares all arguments to be distinct
distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
distinct = Distinct

-- | Calculate the sum of arithmetic expressions
plus :: (SMTArith a) => [SMTExpr a] -> SMTExpr a
plus = Plus

-- | Calculate the product of arithmetic expressions
mult :: (SMTArith a) => [SMTExpr a] -> SMTExpr a
mult = Mult

-- | Subtracts two expressions
minus :: (SMTArith a) => SMTExpr a -> SMTExpr a -> SMTExpr a
minus = Minus

-- | Divide an arithmetic expression by another
div' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
div' = Div

-- | Perform a modulo operation on an arithmetic expression
mod' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
mod' = Mod

-- | Divide a rational expression by another one
divide :: SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational
divide = Divide

-- | For an expression @x@, this returns the expression @-x@.
neg :: SMTArith a => SMTExpr a -> SMTExpr a
neg = Neg

-- | Calculate the absolute (non-negative) value of an expression.
abs' :: SMTArith a => SMTExpr a -> SMTExpr a
abs' = Abs

-- | If-then-else construct
ite :: (SMTType a) => SMTExpr Bool -- ^ If this expression is true
       -> SMTExpr a -- ^ Then return this expression
       -> SMTExpr a -- ^ Else this one
       -> SMTExpr a
ite = ITE

-- | Boolean conjunction
and' :: [SMTExpr Bool] -> SMTExpr Bool
and' [] = Const True
and' [x] = x
and' xs = And xs

-- | Boolean disjunction
or' :: [SMTExpr Bool] -> SMTExpr Bool
or' [] = Const False
or' [x] = x
or' xs = Or xs

-- | Exclusive or: Return true if exactly one argument is true.
xor :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
xor = XOr

-- | Implication
(.=>.) :: SMTExpr Bool -- ^ If this expression is true
          -> SMTExpr Bool -- ^ This one must be as well
          -> SMTExpr Bool
(.=>.) = Implies

-- | Negates a boolean expression
not' :: SMTExpr Bool -> SMTExpr Bool
not' = Not

-- | Extracts an element of an array by its index
select :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v
select = Select

-- | The expression @store arr i v@ stores the value /v/ in the array /arr/ at position /i/ and returns the resulting new array.
store :: SMTExpr (Array i v) -> SMTExpr i -> SMTExpr v -> SMTExpr (Array i v)
store = Store

-- | Create a boolean expression that encodes that the array is equal to the supplied constant array.
arrayConst :: (SMTValue i,SMTValue v,Ix i) => SMTExpr (Array i v) -> Array i v -> SMTExpr Bool
arrayConst expr arr = and' [(select expr (constant i)) .==. (constant v)
                           | (i,v) <- assocs arr ]

-- | Extract all values of an array by giving the range of indices.
unmangleArray :: (Ix i,SMTValue i,SMTValue v) => (i,i) -> SMTExpr (Array i v) -> SMT (Array i v)
unmangleArray b expr = mapM (\i -> do
                                v <- getValue (select expr (constant i))
                                return (i,v)
                            ) (range b) >>= return.array b

-- | Bitvector addition
bvadd :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvadd = BVAdd

-- | Bitvector subtraction
bvsub :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvsub = BVSub

-- | Bitvector multiplication
bvmul :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvmul = BVMul

-- | Bitvector unsigned remainder
bvurem :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvurem = BVURem

-- | Bitvector signed remainder
bvsrem :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvsrem = BVSRem

-- | Bitvector unsigned less-or-equal
bvule :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvule = BVULE

-- | Bitvector unsigned less-than
bvult :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvult = BVULT

-- | Bitvector unsigned greater-or-equal
bvuge :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvuge = BVUGE

-- | Bitvector unsigned greater-than
bvugt :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvugt = BVUGT

-- | Bitvector signed less-or-equal
bvsle :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvsle = BVSLE

-- | Bitvector signed less-than
bvslt :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvslt = BVSLT

-- | Bitvector signed greater-or-equal
bvsge :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvsge = BVSGE

-- | Bitvector signed greater-than
bvsgt :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvsgt = BVSGT

-- | If the supplied function returns true for all possible values, the forall quantification returns true.
forAll :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
forAll = Forall

-- | If the supplied function returns true for at least one possible value, the exists quantification returns true.
exists :: Args a b => (a -> SMTExpr Bool) -> SMTExpr Bool
exists = Exists

-- | Binds an expression to a variable.
--   Can be used to prevent blowups in the command stream if expressions are used multiple times.
--   @let' x f@ is functionally equivalent to @f x@.
let' :: SMTType a => SMTExpr a -> (SMTExpr a -> SMTExpr b) -> SMTExpr b
let' = Let

-- | Like 'let'', but can define multiple variables of the same type.
lets :: SMTType a => [SMTExpr a] -> ([SMTExpr a] -> SMTExpr b) -> SMTExpr b
lets = Lets

-- | Like 'forAll', but can quantify over more than one variable (of the same type)
forAllList :: Args a b => Integer -- ^ Number of variables to quantify
              -> ([a] -> SMTExpr Bool) -- ^ Function which takes a list of the quantified variables
              -> SMTExpr Bool
forAllList = ForallList

-- | Checks if the expression is formed a specific constructor.
is :: SMTType a => SMTExpr a -> Constructor a -> SMTExpr Bool
is e con = ConTest con e

-- | Access a field of an expression
(.#) :: SMTType a => SMTExpr a -> Field a f -> SMTExpr f
(.#) e f = FieldSel f e

-- | After a successful 'checkSat' call, extract values from the generated model.
--   The 'ProduceModels' option must be enabled for this.
getValue :: SMTValue t => SMTExpr t -> SMT t
getValue expr = do
  clearInput
  putRequest $ L.List [L.Symbol "get-value"
                      ,L.List [L.toLisp expr]]
  val <- parseResponse
  case val of
    L.List [L.List [_,res]] -> case unmangle res of
      Nothing -> error $ "Couldn't unmangle "++show res
      Just r -> return r
    _ -> error $ "unknown response to get-value: "++show val

-- | Asserts that a boolean expression is true
assert :: SMTExpr Bool -> SMT ()
assert expr = putRequest $ L.List [L.Symbol "assert"
                                  ,L.toLisp expr]

-- | Sets the logic used for the following program (Not needed for many solvers).
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

-- | Check if the model is satisfiable (e.g. if there is a value for each variable so that every assertion holds)
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
  
-- | Perform a stacked operation, meaning that every assertion and declaration made in it will be undone after the operation.
stack :: SMT a -> SMT a
stack act = do
  putRequest (L.List [L.Symbol "push"])
  res <- act
  putRequest (L.List [L.Symbol "pop"])
  return res

-- | Insert a comment into the SMTLib2 command stream.
--   If you aren't looking at the command stream for debugging, this will do nothing.
comment :: String -> SMT ()
comment msg = do
  (hin,_) <- ask
  liftIO $ IO.hPutStrLn hin $ ';':msg

-- | Takes the first element of a list
head' :: SMTExpr [a] -> SMTExpr a
head' = Head

-- | Drops the first element from a list
tail' :: SMTExpr [a] -> SMTExpr [a]
tail' = Tail

-- | Put a new element at the front of the list
insert' :: SMTExpr a -> SMTExpr [a] -> SMTExpr [a]
insert' = Insert

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
                          }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  res <- evalStateT (runReaderT (do
                                 res <- f
                                 putRequest (L.List [L.Symbol "exit"])
                                 return res
                                ) (hin,hout)) (0,[],Map.empty)
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

-- | Given an arbitrary expression, this creates a named version of it and a name to reference it later on.
named :: SMTType a => SMTExpr a -> SMT (SMTExpr a,SMTExpr a)
named expr = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "named"++show c
  return (Named expr name,Var name)

getVars :: SMTExpr a -> Set T.Text
getVars (Var name) = Set.singleton name
getVars (Const _) = Set.empty
getVars (Eq l r) = Set.union (getVars l) (getVars r)
getVars (Ge l r) = Set.union (getVars l) (getVars r)
getVars (Gt l r) = Set.union (getVars l) (getVars r)
getVars (Le l r) = Set.union (getVars l) (getVars r)
getVars (Lt l r) = Set.union (getVars l) (getVars r)
getVars (Distinct es) = Set.unions (fmap getVars es)
getVars (Plus es) = Set.unions (fmap getVars es)
getVars (Minus l r) = Set.union (getVars l) (getVars r)
getVars (Mult es) = Set.unions (fmap getVars es)
getVars (Div l r) = Set.union (getVars l) (getVars r)
getVars (Mod l r) = Set.union (getVars l) (getVars r)
getVars (Divide l r) = Set.union (getVars l) (getVars r)
getVars (Neg e) = getVars e
getVars (Abs e) = getVars e
getVars (ITE c y n) = Set.unions [getVars c,getVars y,getVars n]
getVars (And es) = Set.unions (fmap getVars es)
getVars (Or es) = Set.unions (fmap getVars es)
getVars (XOr l r) = Set.union (getVars l) (getVars r)
getVars (Implies l r) = Set.union (getVars l) (getVars r)
getVars (Not e) = getVars e
getVars (Select l r) = Set.union (getVars l) (getVars r)
getVars (Store a i v) = Set.unions [getVars a,getVars i,getVars v]
getVars (BVAdd l r) = Set.union (getVars l) (getVars r)
getVars (BVSub l r) = Set.union (getVars l) (getVars r)
getVars (BVMul l r) = Set.union (getVars l) (getVars r)
getVars (BVURem l r) = Set.union (getVars l) (getVars r)
getVars (BVSRem l r) = Set.union (getVars l) (getVars r)
getVars (BVULE l r) = Set.union (getVars l) (getVars r)
getVars (BVULT l r) = Set.union (getVars l) (getVars r)
getVars (BVUGE l r) = Set.union (getVars l) (getVars r)
getVars (BVUGT l r) = Set.union (getVars l) (getVars r)
getVars (BVSLE l r) = Set.union (getVars l) (getVars r)
getVars (BVSLT l r) = Set.union (getVars l) (getVars r)
getVars (BVSGE l r) = Set.union (getVars l) (getVars r)
getVars (BVSGT l r) = Set.union (getVars l) (getVars r)
getVars (Forall f) = getVars (f $ allOf Undefined)
getVars (ForallList n f) = getVars (f $ genericReplicate n (allOf Undefined))
getVars (Exists f) = getVars (f $ allOf Undefined)
getVars (Let x f) = Set.union (getVars x) (getVars $ f Undefined)
getVars (Fun name) = Set.singleton name
getVars (App f arg) = Set.union (getVars f) (foldExprs (\s e -> Set.union s (getVars e)) Set.empty arg)
getVars (ConTest _ e) = getVars e
getVars (FieldSel _ e) = getVars e
getVars (Head e) = getVars e
getVars (Tail e) = getVars e
getVars (Insert x xs) = Set.union (getVars x) (getVars xs)
getVars (Named x _) = getVars x
getVars (InternalFun _) = Set.empty
getVars Undefined = Set.empty