module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat

import Data.Proxy
import Data.Typeable
import Numeric
import Text.Show
import Data.List (genericLength,genericReplicate)

class (Liftable arg,GetType (SameType arg)) => AllEq (arg::[Type]) where
  type SameType arg :: Type
  allEqToList :: Args e arg -> [e (SameType arg)]

instance GetType t => AllEq '[t] where
  type SameType '[t] = t
  allEqToList (Arg e NoArg) = [e]
instance (GetType a,AllEq (a ': b),SameType (a ': b) ~ a) => AllEq (a ': a ': b) where
  type SameType (a ': a ': b) = a
  allEqToList (Arg e1 rest)
    = e1:allEqToList rest

data Function (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) (arg :: [Type]) (res :: Type) where
  Fun :: (GetTypes arg,GetType res) => fun arg res -> Function fun con field arg res
  Eq :: AllEq arg => Function fun con field arg BoolType
  Distinct :: AllEq arg => Function fun con field arg BoolType
  Map :: (GetTypes arg,GetType res)
      => Function fun con field arg res
      -> Function fun con field (Lifted arg idx) (ArrayType idx res)
  OrdInt :: OrdOp -> Function fun con field '[IntType,IntType] BoolType
  OrdReal :: OrdOp -> Function fun con field '[RealType,RealType] BoolType
  ArithInt :: (AllEq arg, SameType arg ~ IntType)
           => ArithOp -> Function fun con field arg IntType
  ArithReal :: (AllEq arg, SameType arg ~ RealType) => ArithOp -> Function fun field con arg RealType
  ArithIntBin :: ArithOpInt -> Function fun con field '[IntType,IntType] IntType
  Divide :: Function fun con field '[RealType,RealType] RealType
  AbsInt :: Function fun con field '[IntType] IntType
  AbsReal :: Function fun con field '[RealType] RealType
  Not :: Function fun con field '[BoolType] BoolType
  Logic :: (AllEq arg, SameType arg ~ BoolType) => LogicOp -> Function fun con field arg BoolType
  ToReal :: Function fun con field '[IntType] RealType
  ToInt :: Function fun con field '[RealType] IntType
  ITE :: Function fun con field '[BoolType,a,a] a
  BVComp :: BVCompOp -> Function fun con field '[BitVecType a,BitVecType a] BoolType
  BVBin :: BVBinOp -> Function fun con field '[BitVecType a,BitVecType a] (BitVecType a)
  BVUn :: BVUnOp -> Function fun con field '[BitVecType a] (BitVecType a)
  Select :: Function fun con field (ArrayType idx val ': idx) val
  Store :: Function fun con field (ArrayType idx val ': val ': idx) (ArrayType idx val)
  ConstArray :: (GetTypes idx,GetType val) => Function fun con field '[val] (ArrayType idx val)
  Concat :: Function fun con field '[BitVecType n1,BitVecType n2]
            (BitVecType (n1 + n2))
  Extract :: (KnownNat start,KnownNat len,((start + len) <= a) ~ True) => Proxy start -> Function fun con field '[BitVecType a] (BitVecType len)
  Constructor :: IsDatatype a => con arg a -> Function fun con field arg (DataType a)
  Test :: (GetTypes arg,IsDatatype a) => con arg a -> Function fun con field '[DataType a] BoolType
  Field :: IsDatatype a => field a t -> Function fun con field '[DataType a] t
  Divisible :: Integer -> Function fun con field '[IntType] BoolType

data AnyFunction (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) where
  AnyFunction :: (Liftable arg,GetType t) => Function fun con field arg t -> AnyFunction fun con field

data OrdOp = Ge | Gt | Le | Lt deriving (Eq,Ord,Show)

data ArithOp = Plus | Mult | Minus deriving (Eq,Ord,Show)

data ArithOpInt = Div | Mod | Rem deriving (Eq,Ord,Show)

data LogicOp = And | Or | XOr | Implies deriving (Eq,Ord,Show)

data BVCompOp = BVULE
              | BVULT
              | BVUGE
              | BVUGT
              | BVSLE
              | BVSLT
              | BVSGE
              | BVSGT
              deriving (Eq,Ord,Show)

data BVBinOp = BVAdd
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
             deriving (Eq,Ord,Show)

data BVUnOp = BVNot | BVNeg deriving (Eq,Ord,Show)

data LetBinding (v :: Type -> *) (e :: Type -> *) (t :: Type)
  = LetBinding { letVar :: v t
               , letExpr :: e t }

data Quantifier = Forall | Exists deriving (Typeable,Eq,Ord,Show)

data Expression (v :: Type -> *) (qv :: Type -> *) (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) (fv :: Type -> *) (e :: Type -> *) (res :: Type) where
  Var :: v res -> Expression v qv fun con field fv e res
  QVar :: qv res -> Expression v qv fun con field fv e res
  FVar :: fv res -> Expression v qv fun con field fv e res
  App :: (GetTypes arg,GetType res)
      => Function fun con field arg res
      -> Args e arg
      -> Expression v qv fun con field fv e res
  Const :: Value con a -> Expression v qv fun con field fv e a
  AsArray :: (GetTypes arg,GetType res)
          => Function fun con field arg res
          -> Expression v qv fun con field fv e (ArrayType arg res)
  Quantification :: GetTypes arg => Quantifier -> Args qv arg -> e BoolType
                 -> Expression v qv fun con field fv e BoolType
  Let :: GetTypes arg
      => Args (LetBinding v e) arg
      -> e res
      -> Expression v qv fun con field fv e res

class OrdVar (v :: Type -> *) where
  cmpVar :: GetType t => v t -> v t -> Ordering

class OrdFun (fun :: [Type] -> Type -> *) where
  cmpFun :: (GetTypes arg,GetType t) => fun arg t -> fun arg t -> Ordering

class OrdCon (con :: [Type] -> * -> *) where
  cmpCon :: (GetTypes arg,IsDatatype t) => con arg t -> con arg t -> Ordering

class OrdField (field :: * -> Type -> *) where
  cmpField :: (IsDatatype dt,GetType t) => field dt t -> field dt t -> Ordering

instance (Typeable fun,Typeable con,Typeable field,
          OrdFun fun,OrdCon con,OrdField field,
          GetTypes arg,GetType res)
         => Eq (Function fun con field arg res) where
  (==) x y = functionCompare' x y==EQ

{-instance (OrdVar v,GetType t) => Eq (v t) where
  (==) x y = cmpVar x y==EQ

instance (OrdVar v,GetType t) => Ord (v t) where
  compare = cmpVar

instance (OrdFun fun,GetTypes arg)
         => OrdVar (fun arg) where
  cmpVar = cmpFun

instance (OrdCon con,GetTypes arg,IsDatatype dt)
         => Eq (con arg dt) where
  (==) x y = cmpCon x y==EQ

instance (OrdCon con,GetTypes arg,IsDatatype dt)
         => Ord (con arg dt) where
  compare = cmpCon

instance (OrdField field,IsDatatype dt)
         => OrdVar (field dt) where
  cmpVar = cmpField-}

allEqOfList :: GetType t => Proxy t
            -> Integer
            -> (forall arg. (AllEq (t ': arg),SameType (t ': arg) ~ t)
                => Proxy (t ': arg) -> a)
            -> a
allEqOfList (_::Proxy t) 1 f = f (Proxy::Proxy ('[t]::[Type]))
allEqOfList pr@(_::Proxy t) n f
  = allEqOfList pr (n-1) $
    \(_::Proxy (t ': ts)) -> f (Proxy::Proxy (t ': t ': ts))

functionType :: (GetTypes arg,GetType res) => Function fun con field arg res -> (Args Repr arg,Repr res)
functionType (_::Function fun con field arg res) = (getTypes (Proxy::Proxy arg),getType (Proxy::Proxy res))

mapExpr :: (Functor m,Monad m,GetType r,Typeable con2)
        => (forall t. GetType t => v1 t -> m (v2 t))
        -> (forall t. GetType t => qv1 t -> m (qv2 t))
        -> (forall arg t. (GetTypes arg,GetType t) => fun1 arg t -> m (fun2 arg t))
        -> (forall arg t. (GetTypes arg) => con1 arg t -> m (con2 arg t))
        -> (forall t res. GetType res => field1 t res -> m (field2 t res))
        -> (forall t. GetType t => fv1 t -> m (fv2 t))
        -> (forall t. GetType t => e1 t -> m (e2 t))
        -> Expression v1 qv1 fun1 con1 field1 fv1 e1 r
        -> m (Expression v2 qv2 fun2 con2 field2 fv2 e2 r)
mapExpr f _ _ _ _ _ _ (Var v) = fmap Var (f v)
mapExpr _ f _ _ _ _ _ (QVar v) = fmap QVar (f v)
mapExpr _ _ _ _ _ f _ (FVar v) = fmap FVar (f v)
mapExpr _ _ f g h _ i (App fun args) = do
  fun' <- mapFunction f g h fun
  args' <- mapArgs i args
  return (App fun' args')
mapExpr _ _ _ f _ _ _ (Const val) = fmap Const (mapValue f val)
mapExpr _ _ f g h _ _ (AsArray fun) = fmap AsArray (mapFunction f g h fun)
mapExpr _ f _ _ _ _ g (Quantification q args body) = do
  args' <- mapArgs f args
  body' <- g body
  return (Quantification q args' body')
mapExpr f _ _ _ _ _ g (Let args body) = do
  args' <- mapArgs (\bind -> do
                      nv <- f (letVar bind)
                      nexpr <- g (letExpr bind)
                      return $ LetBinding nv nexpr
                   ) args
  body' <- g body
  return (Let args' body')

mapFunction :: (Functor m,Monad m,GetTypes arg,GetType res)
            => (forall arg t. (GetTypes arg,GetType t) => fun1 arg t -> m (fun2 arg t))
            -> (forall arg t. (GetTypes arg) => con1 arg t -> m (con2 arg t))
            -> (forall t res. (GetType res) => field1 t res -> m (field2 t res))
            -> Function fun1 con1 field1 arg res
            -> m (Function fun2 con2 field2 arg res)
mapFunction f _ _ (Fun x) = fmap Fun (f x)
mapFunction _ _ _ Eq = return Eq
mapFunction _ _ _ Distinct = return Distinct
mapFunction f g h (Map x) = do
  x' <- mapFunction f g h x
  return (Map x')
mapFunction _ _ _ (OrdInt op) = return (OrdInt op)
mapFunction _ _ _ (OrdReal op) = return (OrdReal op)
mapFunction _ _ _ (ArithInt op) = return (ArithInt op)
mapFunction _ _ _ (ArithReal op) = return (ArithReal op)
mapFunction _ _ _ (ArithIntBin op) = return (ArithIntBin op)
mapFunction _ _ _ Divide = return Divide
mapFunction _ _ _ AbsInt = return AbsInt
mapFunction _ _ _ AbsReal = return AbsReal
mapFunction _ _ _ Not = return Not
mapFunction _ _ _ (Logic op) = return (Logic op)
mapFunction _ _ _ ToReal = return ToReal
mapFunction _ _ _ ToInt = return ToInt
mapFunction _ _ _ ITE = return ITE
mapFunction _ _ _ (BVComp op) = return (BVComp op)
mapFunction _ _ _ (BVBin op) = return (BVBin op)
mapFunction _ _ _ (BVUn op) = return (BVUn op)
mapFunction _ _ _ Select = return Select
mapFunction _ _ _ Store = return Store
mapFunction _ _ _ ConstArray = return ConstArray
mapFunction _ _ _ Concat = return Concat
mapFunction _ _ _ (Extract start) = return (Extract start)
mapFunction _ f _ (Constructor con) = fmap Constructor (f con)
mapFunction _ f _ (Test con) = fmap Test (f con)
mapFunction _ _ f (Field x) = fmap Field (f x)
mapFunction _ _ _ (Divisible x) = return (Divisible x)

allEqFromList :: GetType t => [e t]
              -> (forall arg. (AllEq (t ': arg),SameType (t ': arg) ~ t) => Args e (t ': arg) -> a)
              -> a
allEqFromList [e] f = f (Arg e NoArg)
allEqFromList (x:xs) f = allEqFromList xs $
                         \xs' -> f (Arg x xs')

class ShowVar (v :: Type -> *) where
  showVar :: GetType tp => Int -> v tp -> ShowS

class ShowFun (fun :: [Type] -> Type -> *) where
  showFun :: (GetTypes arg,GetType res) => Int -> fun arg res -> ShowS

class ShowCon (con :: [Type] -> * -> *) where
  showCon :: (GetTypes arg,IsDatatype t) => Int -> con arg t -> ShowS

class ShowField (field :: * -> Type -> *) where
  showField :: (IsDatatype dt,GetType t) => Int -> field dt t -> ShowS

{-instance (ShowVar v,GetType t) => Show (v t) where
  showsPrec = showVar

instance (ShowFun fun,GetTypes arg)
         => ShowVar (fun arg) where
  showVar = showFun

instance (ShowCon con,GetTypes arg,IsDatatype dt)
         => Show (con arg dt) where
  showsPrec = showCon-}

showExpression :: (GetType r,
                   ShowVar v,ShowVar qv,ShowFun fun,ShowCon con,
                   ShowField field,ShowVar fv,ShowVar e)
               => Int
               -> Expression v qv fun con field fv e r
               -> ShowS
showExpression p (Var v) = showParen (p>10) $
                           showString "Var " .
                           showVar p v
showExpression p (QVar v) = showParen (p>10) $
                            showString "QVar " .
                            showVar p v
showExpression p (FVar v) = showParen (p>10) $
                            showString "FVar " .
                            showVar p v
showExpression p (App fun args)
  = showParen (p>10) $
    showString "App " .
    showFunction 11 fun .
    showChar ' ' .
    showListWith id (argsToList (showVar 0) args)
showExpression p (Const val) = showValue p val
showExpression p (AsArray fun)
  = showParen (p>10) $
    showString "AsArray " .
    showFunction 11 fun
showExpression p (Quantification q args body)
  = showParen (p>10) $
    showsPrec 11 q .
    showListWith id (argsToList (showVar 0) args) .
    showChar ' ' .
    showVar 11 body
showExpression p (Let args body)
  = showParen (p>10) $
    showString "Let " .
    showListWith id (argsToList
                     (\(LetBinding v e)
                      -> (showVar 10 v) . showChar '=' . (showVar 10 e)
                    ) args)  .
    showChar ' ' .
    showVar 10 body

showFunction :: (GetTypes arg,GetType res,ShowFun fun,ShowCon con,ShowField field)
             => Int
             -> Function fun con field arg res
             -> ShowS
showFunction p (Fun x) = showFun p x
showFunction _ Eq = showString "Eq"
showFunction _ Distinct = showString "Distinct"
showFunction p (Map x) = showParen (p>10) $
                         showString "Map " .
                         showFunction 11 x
showFunction p (OrdInt op) = showParen (p>10) $
                             showString "OrdInt " .
                             showsPrec 11 op
showFunction p (OrdReal op) = showParen (p>10) $
                              showString "OrdReal " .
                              showsPrec 11 op
showFunction p (ArithInt op) = showParen (p>10) $
                               showString "ArithInt " .
                               showsPrec 11 op
showFunction p (ArithReal op) = showParen (p>10) $
                                showString "ArithReal " .
                                showsPrec 11 op
showFunction p (ArithIntBin op) = showParen (p>10) $
                                  showString "ArithIntBin " .
                                  showsPrec 11 op
showFunction p Divide = showString "Divide"
showFunction p AbsInt = showString "AbsInt"
showFunction p AbsReal = showString "AbsReal"
showFunction _ Not =  showString "Not"
showFunction p (Logic op) = showParen (p>10) $
                            showString "Logic " .
                            showsPrec 11 op
showFunction _ ToReal = showString "ToReal"
showFunction _ ToInt = showString "ToInt"
showFunction _ ITE = showString "ITE"
showFunction p (BVComp op) = showParen (p>10) $
                             showString "BVComp " .
                             showsPrec 11 op
showFunction p (BVBin op) = showParen (p>10) $
                            showString "BVBin " .
                            showsPrec 11 op
showFunction _ Select = showString "Select"
showFunction _ Store = showString "Store"
showFunction _ ConstArray = showString "ConstArray"
showFunction _ Concat = showString "Concat"
showFunction p (Extract pr) = showParen (p>10) $
                              showString "Extract " .
                              showsPrec 11 (natVal pr)
showFunction p (Constructor con) = showParen (p>10) $
                                   showString "Constructor " .
                                   showCon 11 con
showFunction p (Test con) = showParen (p>10) $
                            showString "Test " .
                            showCon 11 con
showFunction p (Field x) = showParen (p>10) $
                           showString "Field " .
                           showField 11 x
showFunction p (Divisible x) = showParen (p>10) $
                               showString "Divisible " .
                               showsPrec 11 x

showValue :: (ShowCon con)
          => Int
          -> Value con t
          -> ShowS
showValue p (BoolValue b) = showsPrec p b
showValue p (IntValue i) = showsPrec p i
showValue p (RealValue i) = showsPrec p i
showValue p val@(BitVecValue v) = case getType val of
  BitVecRepr bw
    | bw `mod` 4 == 0 -> let str = showHex v ""
                             exp_len = bw `div` 4
                             len = genericLength str
                         in showString "#x" .
                            showString (genericReplicate (exp_len-len) '0') .
                            showString str
    | otherwise -> let str = showIntAtBase 2 (\x -> case x of
                                                      0 -> '0'
                                                      1 -> '1'
                                             ) v ""
                       len = genericLength str
                   in showString "#b" .
                      showString (genericReplicate (bw-len) '0') .
                      showString str
showValue p (ConstrValue con args) = showParen (p>10) $
                                     showString "ConstrValue " .
                                     showCon 11 con.
                                     showChar ' ' .
                                     showListWith id (argsToList (showValue 0) args)

instance (Typeable con,OrdCon con) => OrdVar (Value con) where
  cmpVar = valueCompare'

instance (OrdVar v,OrdVar e) => OrdVar (LetBinding v e) where
  cmpVar = letCompare'

instance (Typeable fun,Typeable con,Typeable field,
          OrdFun fun,OrdCon con,OrdField field)
         => OrdFun (Function fun con field) where
  cmpFun = functionCompare'

instance (Typeable v,Typeable qv,Typeable fun,Typeable con,
          Typeable field,Typeable fv,Typeable e,
          OrdVar v,OrdVar qv,OrdFun fun,OrdCon con,OrdField field,OrdVar fv,OrdVar e,
          GetType r) => OrdVar (Expression v qv fun con field fv e) where
  cmpVar = exprCompare'

functionCompare :: (Typeable fun,Typeable con,Typeable field,
                    OrdFun fun,OrdCon con,OrdField field,
                    GetTypes arg1,GetTypes arg2,GetType res1,GetType res2)
                 => Function fun con field arg1 res1
                 -> Function fun con field arg2 res2
                 -> Ordering
functionCompare fun1 fun2 = case compareSig fun1 fun2 of
  EQ -> case cast fun2 of
    Just fun2' -> functionCompare' fun1 fun2'
  r -> r

functionCompare' :: (Typeable fun,Typeable con,Typeable field,
                     OrdFun fun,OrdCon con,OrdField field,
                     GetTypes arg,GetType res)
                 => Function fun con field arg res
                 -> Function fun con field arg res
                 -> Ordering
functionCompare' (Fun fun1) (Fun fun2) = cmpFun fun1 fun2
functionCompare' (Fun _) _ = LT
functionCompare' _ (Fun _) = GT
functionCompare' Eq Eq = EQ
functionCompare' Eq _ = LT
functionCompare' _ Eq = GT
functionCompare' Distinct Distinct = EQ
functionCompare' Distinct _ = LT
functionCompare' _ Distinct = GT
functionCompare' (Map fun1) (Map fun2) = functionCompare fun1 fun2
functionCompare' (Map _) _ = LT
functionCompare' _ (Map _) = GT
functionCompare' (OrdInt o1) (OrdInt o2) = compare o1 o2
functionCompare' (OrdInt _) _ = LT
functionCompare' _ (OrdInt _) = GT
functionCompare' (OrdReal o1) (OrdReal o2) = compare o1 o2
functionCompare' (OrdReal _) _ = LT
functionCompare' _ (OrdReal _) = GT
functionCompare' (ArithInt o1) (ArithInt o2) = compare o1 o2
functionCompare' (ArithInt _) _ = LT
functionCompare' _ (ArithInt _) = GT
functionCompare' (ArithReal o1) (ArithReal o2) = compare o1 o2
functionCompare' (ArithReal _) _ = LT
functionCompare' _ (ArithReal _) = GT
functionCompare' (ArithIntBin o1) (ArithIntBin o2) = compare o1 o2
functionCompare' (ArithIntBin _) _ = LT
functionCompare' _ (ArithIntBin _) = GT
functionCompare' Divide Divide = EQ
functionCompare' Divide _ = LT
functionCompare' _ Divide = GT
functionCompare' AbsInt AbsInt = EQ
functionCompare' AbsInt _ = LT
functionCompare' _ AbsInt = GT
functionCompare' AbsReal AbsReal = EQ
functionCompare' AbsReal _ = LT
functionCompare' _ AbsReal = GT
functionCompare' Not Not = EQ
functionCompare' Not _ = LT
functionCompare' _ Not = GT
functionCompare' (Logic o1) (Logic o2) = compare o1 o2
functionCompare' (Logic _) _ = LT
functionCompare' _ (Logic _) = GT
functionCompare' ToReal ToReal = EQ
functionCompare' ToReal _ = LT
functionCompare' _ ToReal = GT
functionCompare' ToInt ToInt = EQ
functionCompare' ToInt _ = LT
functionCompare' _ ToInt = GT
functionCompare' ITE ITE = EQ
functionCompare' ITE _ = LT
functionCompare' _ ITE = GT
functionCompare' (BVComp o1) (BVComp o2) = compare o1 o2
functionCompare' (BVComp _) _ = LT
functionCompare' _ (BVComp _) = GT
functionCompare' (BVBin o1) (BVBin o2) = compare o1 o2
functionCompare' (BVBin _) _ = LT
functionCompare' _ (BVBin _) = GT
functionCompare' (BVUn o1) (BVUn o2) = compare o1 o2
functionCompare' (BVUn _) _ = LT
functionCompare' _ (BVUn _) = GT
functionCompare' Select Select = EQ
functionCompare' Select _ = LT
functionCompare' _ Select = GT
functionCompare' Store Store = EQ
functionCompare' Store _ = LT
functionCompare' _ Store = GT
functionCompare' ConstArray ConstArray = EQ
functionCompare' ConstArray _ = LT
functionCompare' _ ConstArray = GT
functionCompare' Concat Concat = EQ
functionCompare' Concat _ = LT
functionCompare' _ Concat = GT
functionCompare' (Extract p1) (Extract p2) = compare (natVal p1) (natVal p2)
functionCompare' (Extract _) _ = LT
functionCompare' _ (Extract _) = GT
functionCompare' (Constructor c1) (Constructor c2) = cmpCon c1 c2
functionCompare' (Constructor _) _ = LT
functionCompare' _ (Constructor _) = GT
functionCompare' (Test c1) (Test c2)
  = case compareArgSig c1 c2 of
    EQ -> case cast c2 of
      Just c2' -> cmpCon c1 c2'
    r -> r
functionCompare' (Test _) _ = LT
functionCompare' _ (Test _) = GT
functionCompare' (Field f1) (Field f2) = cmpField f1 f2
functionCompare' (Field _) _ = LT
functionCompare' _ (Field _) = GT
functionCompare' (Divisible n1) (Divisible n2) = compare n1 n2

exprCompare :: (Typeable v,Typeable qv,Typeable fun,Typeable con,
                Typeable field,Typeable fv,Typeable e,
                OrdVar v,OrdVar qv,OrdFun fun,OrdCon con,OrdField field,OrdVar fv,OrdVar e,
                GetType r1,GetType r2)
            => Expression v qv fun con field fv e r1
            -> Expression v qv fun con field fv e r2
            -> Ordering
exprCompare e1 e2 = case compareRetSig e1 e2 of
  EQ -> case cast e2 of
    Just e2' -> exprCompare' e1 e2'
  r -> r

exprCompare' :: (Typeable v,Typeable qv,Typeable fun,Typeable con,
                 Typeable field,Typeable fv,Typeable e,
                 OrdVar v,OrdVar qv,OrdFun fun,OrdCon con,OrdField field,OrdVar fv,OrdVar e,
                 GetType r)
             => Expression v qv fun con field fv e r
             -> Expression v qv fun con field fv e r
             -> Ordering
exprCompare' (Var v1) (Var v2) = cmpVar v1 v2
exprCompare' (Var _) _ = LT
exprCompare' _ (Var _) = GT
exprCompare' (QVar v1) (QVar v2) = cmpVar v1 v2
exprCompare' (QVar _) _ = LT
exprCompare' _ (QVar _) = GT
exprCompare' (FVar v1) (FVar v2) = cmpVar v1 v2
exprCompare' (FVar _) _ = LT
exprCompare' _ (FVar _) = GT
exprCompare' (App f1 arg1) (App f2 arg2) = case compareArgSig f1 f2 of
  EQ -> case cast (f2,arg2) of
    Just (f2',arg2') -> case functionCompare' f1 f2' of
      EQ -> argCompare' arg1 arg2'
      r -> r
  r -> r
exprCompare' (App _ _) _ = LT
exprCompare' _ (App _ _) = GT
exprCompare' (Const x) (Const y) = valueCompare' x y
exprCompare' (Const _) _ = LT
exprCompare' _ (Const _) = GT
exprCompare' (AsArray f1) (AsArray f2) = functionCompare' f1 f2
exprCompare' (AsArray _) _ = LT
exprCompare' _ (AsArray _) = GT
exprCompare' (Quantification q1 arg1 body1) (Quantification q2 arg2 body2)
  = case compare q1 q2 of
      EQ -> case argCompare arg1 arg2 of
        EQ -> cmpVar body1 body2
        r -> r
      r -> r
exprCompare' (Quantification _ _ _) _ = LT
exprCompare' _ (Quantification _ _ _) = GT
exprCompare' (Let bnd1 body1) (Let bnd2 body2) = case argCompare bnd1 bnd2 of
  EQ -> cmpVar body1 body2
  r -> r

valueCompare' :: (Typeable con,OrdCon con,GetType t) => Value con t -> Value con t -> Ordering
valueCompare' (BoolValue b1) (BoolValue b2) = compare b1 b2
valueCompare' (IntValue v1) (IntValue v2) = compare v1 v2
valueCompare' (RealValue v1) (RealValue v2) = compare v1 v2
valueCompare' (BitVecValue v1) (BitVecValue v2) = compare v1 v2
valueCompare' (ConstrValue c1 arg1) (ConstrValue c2 arg2)
  = case compareArgSig c1 c2 of
      EQ -> case cast c2 of
        Just c2' -> case cmpCon c1 c2' of
          EQ -> argCompare arg1 arg2
          r -> r
      r -> r

argCompare' :: OrdVar v => Args v arg -> Args v arg -> Ordering
argCompare' NoArg NoArg = EQ
argCompare' (Arg x xs) (Arg y ys) = case cmpVar x y of
  EQ -> argCompare' xs ys
  r -> r

argCompare :: OrdVar v => Args v arg1 -> Args v arg2 -> Ordering
argCompare NoArg NoArg = EQ
argCompare NoArg _ = LT
argCompare _ NoArg = GT
argCompare (Arg x xs) (Arg y ys) = case compareRetSig x y of
  EQ -> case gcast y of
    Just y' -> case cmpVar x y' of
      EQ -> argCompare xs ys
      r -> r
  r -> r

letCompare :: (OrdVar v,OrdVar e,GetType t1,GetType t2)
           => LetBinding v e t1 -> LetBinding v e t2
           -> Ordering
letCompare bnd1 bnd2 = case compareRetSig bnd1 bnd2 of
  EQ -> case gcast bnd2 of
    Just bnd2' -> letCompare' bnd1 bnd2'
  r -> r

letCompare' :: (OrdVar v,OrdVar e,GetType t)
            => LetBinding v e t -> LetBinding v e t
            -> Ordering
letCompare' (LetBinding v1 e1) (LetBinding v2 e2)
  = case cmpVar v1 v2 of
      EQ -> cmpVar e1 e2
      r -> r

compareArgSig :: (Typeable (arg1::k1),Typeable (arg2::k1))
              => f arg1 (res1::k2)
              -> f arg2 (res2::k2)
              -> Ordering
compareArgSig (_::f arg1 res1) (_::f arg2 res2)
  = compare (typeRep (Proxy::Proxy arg1)) (typeRep (Proxy::Proxy arg2))

compareRetSig :: (Typeable (r1::k1),Typeable (r2::k1))
              => f r1
              -> g r2
              -> Ordering
compareRetSig (_::f r1) (_::g r2)
  = compare (typeRep (Proxy::Proxy r1)) (typeRep (Proxy::Proxy r2))

compareSig :: (Typeable (arg1::k1),Typeable (arg2::k1),Typeable (res1::k2),Typeable (res2::k2))
              => f arg1 res1
              -> f arg2 res2
              -> Ordering
compareSig f1 f2
  = case compareArgSig f1 f2 of
      EQ -> compareRetSig f1 f2
      r -> r
