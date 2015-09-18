module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat

import Data.Proxy
import Data.Typeable

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
  Map :: (GetTypes arg,GetType res) => Function fun con field arg res -> Function fun con field (Lifted arg idx) (ArrayType idx res)
  OrdInt :: OrdOp -> Function fun con field '[IntType,IntType] BoolType
  OrdReal :: OrdOp -> Function fun con field '[RealType,RealType] BoolType
  ArithInt :: (AllEq arg, SameType arg ~ IntType) => ArithOp -> Function fun con field arg IntType
  ArithReal :: (AllEq arg, SameType arg ~ RealType) => ArithOp -> Function fun field con arg RealType
  ArithIntBin :: ArithOpInt -> Function fun con field '[IntType,IntType] IntType
  ArithRealBin :: ArithOpReal -> Function fun con field '[RealType,RealType] RealType
  ArithIntUn :: ArithOpUn -> Function fun con field '[IntType] IntType
  ArithRealUn :: ArithOpUn -> Function fun con field '[RealType] RealType
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
  ConstArray :: Function fun con field '[val] (ArrayType idx val)
  Concat :: Function fun con field '[BitVecType n1,BitVecType n2]
            (BitVecType (n1 + n2))
  Extract :: (KnownNat start,KnownNat len,((start + len) <= a) ~ True) => Proxy start -> Function fun con field '[BitVecType a] (BitVecType len)
  Constructor :: con arg a -> Function fun con field arg (DataType a)
  Test :: GetTypes arg => con arg a -> Function fun con field '[DataType a] BoolType
  Field :: field a t -> Function fun con field '[DataType a] t
  Divisible :: Integer -> Function fun con field '[IntType] BoolType

--data AnyFunction (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *)
--  = forall (arg :: [Type]) (t :: Type). (Liftable arg,GetType t) => AnyFunction { anyFunction :: Function fun con field arg t }

data AnyFunction (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) where
  AnyFunction :: (Liftable arg,GetType t) => Function fun con field arg t -> AnyFunction fun con field

data OrdOp = Ge | Gt | Le | Lt

data ArithOp = Plus | Mult

data ArithOpInt = MinusInt | Div | Mod | Rem

data ArithOpReal = MinusReal | Divide

data ArithOpUn = Abs | Neg

data LogicOp = And | Or | XOr | Implies

data BVCompOp = BVULE
              | BVULT
              | BVUGE
              | BVUGT
              | BVSLE
              | BVSLT
              | BVSGE
              | BVSGT

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

data BVUnOp = BVNot | BVNeg

data LetBinding (v :: Type -> *) (e :: Type -> *) (t :: Type)
  = LetBinding { letVar :: v t
               , letExpr :: e t }

data Quantifier = Forall | Exists deriving (Typeable,Eq,Ord,Show)

data Expression (v :: Type -> *) (qv :: Type -> *) (fun :: [Type] -> Type -> *) (con :: [Type] -> * -> *) (field :: * -> Type -> *) (fv :: Type -> *) (e :: Type -> *) (res :: Type) where
  Var :: v res -> Expression v qv fun con field fv e res
  QVar :: qv res -> Expression v qv fun con field fv e res
  FVar :: fv res -> Expression v qv fun con field fv e res
  App :: (GetTypes arg,GetType res) => Function fun con field arg res -> Args e arg
      -> Expression v qv fun con field fv e res
  Const :: Value con a -> Expression v qv fun con field fv e a
  AsArray :: (GetTypes arg,GetType res) => Function fun con field arg res
          -> Expression v qv fun con field fv e (ArrayType arg res)
  Quantification :: GetTypes arg => Quantifier -> Args qv arg -> e BoolType
                 -> Expression v qv fun con field fv e BoolType
  Let :: Args (LetBinding v e) arg -> e res -> Expression v qv fun con field fv e res
  Named :: e res -> String -> Expression v qv fun con field fv e res

functionType :: (GetTypes arg,GetType res) => Function fun con field arg res -> (Args Repr arg,Repr res)
functionType (_::Function fun con field arg res) = (getTypes (Proxy::Proxy arg),getType (Proxy::Proxy res))

mapExpr :: (Monad m,GetType r)
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
mapExpr _ _ _ _ _ _ f (Named e name) = do
  e' <- f e
  return (Named e' name)

mapFunction :: (Monad m,GetTypes arg,GetType res)
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
mapFunction _ _ _ (ArithRealBin op) = return (ArithRealBin op)
mapFunction _ _ _ (ArithIntUn op) = return (ArithIntUn op)
mapFunction _ _ _ (ArithRealUn op) = return (ArithRealUn op)
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
