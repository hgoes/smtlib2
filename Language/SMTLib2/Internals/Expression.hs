module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat

import Data.Proxy
import Data.Typeable
import Text.Show
import Data.GADT.Compare
import Data.GADT.Show

class (GetTypes arg,GetType (SameType arg)) => AllEq (arg::[Type]) where
  type SameType arg :: Type
  allEqToList :: Args e arg -> [e (SameType arg)]
  mapAllEq :: Monad m => (e (SameType arg) -> m (e' (SameType arg)))
           -> Args e arg -> m (Args e' arg)
    
instance GetType t => AllEq '[t] where
  type SameType '[t] = t
  allEqToList (Arg e NoArg) = [e]
  mapAllEq f (Arg e NoArg) = do
    ne <- f e
    return (Arg ne NoArg)
instance (GetType a,AllEq (a ': b),SameType (a ': b) ~ a) => AllEq (a ': a ': b) where
  type SameType (a ': a ': b) = a
  allEqToList (Arg e1 rest)
    = e1:allEqToList rest
  mapAllEq f (Arg e es) = do
    ne <- f e
    nes <- mapAllEq f es
    return (Arg ne nes)

data Function (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) (sig :: ([Type],Type)) where
  Fun :: (GetTypes arg,GetType res) => fun '(arg,res) -> Function fun con field '(arg,res)
  Eq :: AllEq arg => Function fun con field '(arg,BoolType)
  Distinct :: AllEq arg => Function fun con field '(arg,BoolType)
  Map :: (GetTypes arg,GetType res,GetTypes idx)
      => Function fun con field '(arg,res)
      -> Function fun con field '(Lifted arg idx,ArrayType idx res)
  OrdInt :: OrdOp -> Function fun con field '([IntType,IntType],BoolType)
  OrdReal :: OrdOp -> Function fun con field '([RealType,RealType],BoolType)
  ArithInt :: (AllEq arg, SameType arg ~ IntType)
           => ArithOp -> Function fun con field '(arg,IntType)
  ArithReal :: (AllEq arg, SameType arg ~ RealType) => ArithOp -> Function fun field con '(arg,RealType)
  ArithIntBin :: ArithOpInt -> Function fun con field '([IntType,IntType],IntType)
  Divide :: Function fun con field '([RealType,RealType],RealType)
  AbsInt :: Function fun con field '( '[IntType],IntType)
  AbsReal :: Function fun con field '( '[RealType],RealType)
  Not :: Function fun con field '( '[BoolType],BoolType)
  Logic :: (AllEq arg, SameType arg ~ BoolType) => LogicOp -> Function fun con field '(arg,BoolType)
  ToReal :: Function fun con field '( '[IntType],RealType)
  ToInt :: Function fun con field '( '[RealType],IntType)
  ITE :: GetType a => Function fun con field '([BoolType,a,a],a)
  BVComp :: KnownNat a => BVCompOp -> Function fun con field '([BitVecType a,BitVecType a],BoolType)
  BVBin :: KnownNat a => BVBinOp -> Function fun con field '([BitVecType a,BitVecType a],BitVecType a)
  BVUn :: KnownNat a => BVUnOp -> Function fun con field '( '[BitVecType a],BitVecType a)
  Select :: (GetTypes idx,GetType val)
         => Function fun con field '(ArrayType idx val ': idx,val)
  Store :: (GetTypes idx,GetType val)
        => Function fun con field '(ArrayType idx val ': val ': idx,ArrayType idx val)
  ConstArray :: (GetTypes idx,GetType val)
             => Function fun con field '( '[val],ArrayType idx val)
  Concat :: (KnownNat n1,KnownNat n2)
         => Function fun con field '([BitVecType n1,BitVecType n2],BitVecType (n1 + n2))
  Extract :: (KnownNat start,KnownNat len,KnownNat a,((start + len) <= a) ~ True)
          => Proxy start -> Function fun con field '( '[BitVecType a],BitVecType len)
  Constructor :: IsDatatype a => con '(arg,a) -> Function fun con field '(arg,DataType a)
  Test :: (GetTypes arg,IsDatatype a) => con '(arg,a) -> Function fun con field '( '[DataType a],BoolType)
  Field :: (IsDatatype a,GetType t) => field '(a,t) -> Function fun con field '( '[DataType a],t)
  Divisible :: Integer -> Function fun con field '( '[IntType],BoolType)

data AnyFunction (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) where
  AnyFunction :: (GetTypes arg,GetType t) => Function fun con field '(arg,t) -> AnyFunction fun con field

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

data Expression (v :: Type -> *) (qv :: Type -> *) (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) (fv :: Type -> *) (lv :: Type -> *) (e :: Type -> *) (res :: Type) where
  Var :: GetType res => v res -> Expression v qv fun con field fv lv e res
  QVar :: GetType res => qv res -> Expression v qv fun con field fv lv e res
  FVar :: GetType res => fv res -> Expression v qv fun con field fv lv e res
  LVar :: GetType res => lv res -> Expression v qv fun con field fv lv e res
  App :: (GetTypes arg,GetType res)
      => Function fun con field '(arg,res)
      -> Args e arg
      -> Expression v qv fun con field fv lv e res
  Const :: Value con a -> Expression v qv fun con field fv lv e a
  AsArray :: (GetTypes arg,GetType res)
          => Function fun con field '(arg,res)
          -> Expression v qv fun con field fv lv e (ArrayType arg res)
  Quantification :: GetTypes arg => Quantifier -> Args qv arg -> e BoolType
                 -> Expression v qv fun con field fv lv e BoolType
  Let :: (GetTypes arg,GetType res)
      => Args (LetBinding lv e) arg
      -> e res
      -> Expression v qv fun con field fv lv e res

instance (GEq fun,GEq con,GEq field)
         => Eq (Function fun con field sig) where
  (==) = defaultEq

class GetType t => SMTOrd (t :: Type) where
  lt :: Function fun con field '( '[t,t],BoolType)
  le :: Function fun con field '( '[t,t],BoolType)
  gt :: Function fun con field '( '[t,t],BoolType)
  ge :: Function fun con field '( '[t,t],BoolType)

instance SMTOrd IntType where
  lt = OrdInt Lt
  le = OrdInt Le
  gt = OrdInt Gt
  ge = OrdInt Ge

instance SMTOrd RealType where
  lt = OrdReal Lt
  le = OrdReal Le
  gt = OrdReal Gt
  ge = OrdReal Ge

class GetType t => SMTArith t where
  arithFromInteger :: Integer -> ConcreteValue t
  plus :: (AllEq arg, SameType arg ~ t)
       => Function fun con field '(arg,t)
  minus :: (AllEq arg,SameType arg ~ t)
        => Function fun con field '(arg,t)
  mult :: (AllEq arg, SameType arg ~ t)
       => Function fun con field '(arg,t)
  abs' :: Function fun con field '( '[t],t)

instance SMTArith IntType where
  arithFromInteger n = IntValueC n
  plus = ArithInt Plus
  minus = ArithInt Minus
  mult = ArithInt Mult
  abs' = AbsInt

instance SMTArith RealType where
  arithFromInteger n = RealValueC (fromInteger n)
  plus = ArithReal Plus
  minus = ArithReal Minus
  mult = ArithReal Mult
  abs' = AbsReal

allEqOfList :: GetType t => Proxy t
            -> Integer
            -> (forall arg. (AllEq (t ': arg),SameType (t ': arg) ~ t)
                => Proxy (t ': arg) -> a)
            -> a
allEqOfList (_::Proxy t) 1 f = f (Proxy::Proxy ('[t]::[Type]))
allEqOfList pr@(_::Proxy t) n f
  = allEqOfList pr (n-1) $
    \(_::Proxy (t ': ts)) -> f (Proxy::Proxy (t ': t ': ts))

functionType :: (GetTypes arg,GetType res) => Function fun con field '(arg,res) -> (Args Repr arg,Repr res)
functionType (_::Function fun con field '(arg,res)) = (getTypes::Args Repr arg,getType::Repr res)

mapExpr :: (Functor m,Monad m,GetType r,Typeable con2)
        => (forall t. GetType t => v1 t -> m (v2 t)) -- ^ How to translate variables
        -> (forall t. GetType t => qv1 t -> m (qv2 t)) -- ^ How to translate quantified variables
        -> (forall arg t. (GetTypes arg,GetType t) => fun1 '(arg,t) -> m (fun2 '(arg,t))) -- ^ How to translate functions
        -> (forall arg t. (GetTypes arg) => con1 '(arg,t) -> m (con2 '(arg,t))) -- ^ How to translate constructrs
        -> (forall t res. GetType res => field1 '(t,res) -> m (field2 '(t,res))) -- ^ How to translate field accessors
        -> (forall t. GetType t => fv1 t -> m (fv2 t)) -- ^ How to translate function variables
        -> (forall t. GetType t => lv1 t -> m (lv2 t)) -- ^ How to translate let variables
        -> (forall t. GetType t => e1 t -> m (e2 t)) -- ^ How to translate sub-expressions
        -> Expression v1 qv1 fun1 con1 field1 fv1 lv1 e1 r -- ^ The expression to translate
        -> m (Expression v2 qv2 fun2 con2 field2 fv2 lv2 e2 r)
mapExpr f _ _ _ _ _ _ _ (Var v) = fmap Var (f v)
mapExpr _ f _ _ _ _ _ _ (QVar v) = fmap QVar (f v)
mapExpr _ _ _ _ _ f _ _ (FVar v) = fmap FVar (f v)
mapExpr _ _ _ _ _ _ f _ (LVar v) = fmap LVar (f v)
mapExpr _ _ f g h _ _ i (App fun args) = do
  fun' <- mapFunction f g h fun
  args' <- mapArgs i args
  return (App fun' args')
mapExpr _ _ _ f _ _ _ _ (Const val) = fmap Const (mapValue f val)
mapExpr _ _ f g h _ _ _ (AsArray fun) = fmap AsArray (mapFunction f g h fun)
mapExpr _ f _ _ _ _ _ g (Quantification q args body) = do
  args' <- mapArgs f args
  body' <- g body
  return (Quantification q args' body')
mapExpr _ _ _ _ _ _ f g (Let args body) = do
  args' <- mapArgs (\bind -> do
                      nv <- f (letVar bind)
                      nexpr <- g (letExpr bind)
                      return $ LetBinding nv nexpr
                   ) args
  body' <- g body
  return (Let args' body')

mapFunction :: (Functor m,Monad m,GetTypes arg,GetType res)
            => (forall arg t. (GetTypes arg,GetType t) => fun1 '(arg,t) -> m (fun2 '(arg,t)))
            -> (forall arg t. (GetTypes arg) => con1 '(arg,t) -> m (con2 '(arg,t)))
            -> (forall t res. (GetType res) => field1 '(t,res) -> m (field2 '(t,res)))
            -> Function fun1 con1 field1 '(arg,res)
            -> m (Function fun2 con2 field2 '(arg,res))
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

instance (GShow v,GShow qv,GShow fun,GShow con,GShow field,GShow fv,GShow lv,GShow e)
         => Show (Expression v qv fun con field fv lv e r) where
  showsPrec p (Var v) = showParen (p>10) $
                        showString "Var " .
                        gshowsPrec 11 v
  showsPrec p (QVar v) = showParen (p>10) $
                         showString "QVar " .
                         gshowsPrec 11 v
  showsPrec p (FVar v) = showParen (p>10) $
                         showString "FVar " .
                         gshowsPrec 11 v
  showsPrec p (LVar v) = showParen (p>10) $
                         showString "LVar " .
                         gshowsPrec 11 v
  showsPrec p (App fun args)
    = showParen (p>10) $
      showString "App " .
      showsPrec 11 fun .
      showChar ' ' .
      showListWith id (argsToList (gshowsPrec 0) args)
  showsPrec p (Const val) = showsPrec p val
  showsPrec p (AsArray fun)
    = showParen (p>10) $
      showString "AsArray " .
      showsPrec 11 fun
  showsPrec p (Quantification q args body)
    = showParen (p>10) $
      showsPrec 11 q .
      showListWith id (argsToList (gshowsPrec 0) args) .
      showChar ' ' .
      gshowsPrec 11 body
  showsPrec p (Let args body)
    = showParen (p>10) $
      showString "Let " .
      showListWith id (argsToList
                       (\(LetBinding v e)
                        -> (gshowsPrec 10 v) . showChar '=' . (gshowsPrec 10 e)
                      ) args)  .
      showChar ' ' .
      gshowsPrec 10 body

instance (GShow v,GShow qv,GShow fun,GShow con,GShow field,GShow fv,GShow lv,GShow e)
         => GShow (Expression v qv fun con field fv lv e) where
  gshowsPrec = showsPrec

instance (GShow fun,GShow con,GShow field)
         => Show (Function fun con field sig) where
  showsPrec p (Fun x) = gshowsPrec p x
  showsPrec _ Eq = showString "Eq"
  showsPrec _ Distinct = showString "Distinct"
  showsPrec p (Map x) = showParen (p>10) $
                        showString "Map " .
                        showsPrec 11 x
  showsPrec p (OrdInt op) = showParen (p>10) $
                            showString "OrdInt " .
                            showsPrec 11 op
  showsPrec p (OrdReal op) = showParen (p>10) $
                             showString "OrdReal " .
                             showsPrec 11 op
  showsPrec p (ArithInt op) = showParen (p>10) $
                              showString "ArithInt " .
                              showsPrec 11 op
  showsPrec p (ArithReal op) = showParen (p>10) $
                               showString "ArithReal " .
                               showsPrec 11 op
  showsPrec p (ArithIntBin op) = showParen (p>10) $
                                 showString "ArithIntBin " .
                                 showsPrec 11 op
  showsPrec p Divide = showString "Divide"
  showsPrec p AbsInt = showString "AbsInt"
  showsPrec p AbsReal = showString "AbsReal"
  showsPrec _ Not =  showString "Not"
  showsPrec p (Logic op) = showParen (p>10) $
                           showString "Logic " .
                           showsPrec 11 op
  showsPrec _ ToReal = showString "ToReal"
  showsPrec _ ToInt = showString "ToInt"
  showsPrec _ ITE = showString "ITE"
  showsPrec p (BVComp op) = showParen (p>10) $
                            showString "BVComp " .
                            showsPrec 11 op
  showsPrec p (BVBin op) = showParen (p>10) $
                           showString "BVBin " .
                           showsPrec 11 op
  showsPrec p (BVUn op) = showParen (p>10) $
                          showString "BVUn " .
                          showsPrec 11 op
  showsPrec _ Select = showString "Select"
  showsPrec _ Store = showString "Store"
  showsPrec _ ConstArray = showString "ConstArray"
  showsPrec _ Concat = showString "Concat"
  showsPrec p (Extract pr) = showParen (p>10) $
                             showString "Extract " .
                             showsPrec 11 (natVal pr)
  showsPrec p (Constructor con) = showParen (p>10) $
                                  showString "Constructor " .
                                  gshowsPrec 11 con
  showsPrec p (Test con) = showParen (p>10) $
                           showString "Test " .
                           gshowsPrec 11 con
  showsPrec p (Field x) = showParen (p>10) $
                          showString "Field " .
                          gshowsPrec 11 x
  showsPrec p (Divisible x) = showParen (p>10) $
                              showString "Divisible " .
                              showsPrec 11 x

instance (GShow fun,GShow con,GShow field)
         => GShow (Function fun con field) where
  gshowsPrec = showsPrec

instance (GEq v,GEq e) => GEq (LetBinding v e) where
  geq (LetBinding v1 e1) (LetBinding v2 e2) = do
    Refl <- geq v1 v2
    geq e1 e2

instance (GCompare v,GCompare e) => GCompare (LetBinding v e) where
  gcompare (LetBinding v1 e1) (LetBinding v2 e2) = case gcompare v1 v2 of
    GEQ -> gcompare e1 e2
    r -> r

instance (GEq v,GEq qv,GEq fun,GEq con,GEq field,GEq fv,GEq lv,GEq e)
         => GEq (Expression v qv fun con field fv lv e) where
  geq (Var v1) (Var v2) = geq v1 v2
  geq (QVar v1) (QVar v2) = geq v1 v2
  geq (FVar v1) (FVar v2) = geq v1 v2
  geq (LVar v1) (LVar v2) = geq v1 v2
  geq (App f1 arg1) (App f2 arg2) = do
    Refl <- geq f1 f2
    Refl <- geq arg1 arg2
    return Refl
  geq (Const x) (Const y) = geq x y
  geq (AsArray f1) (AsArray f2) = do
    Refl <- geq f1 f2
    return Refl
  geq (Quantification q1 arg1 body1) (Quantification q2 arg2 body2)
    | q1==q2 = do
        Refl <- geq arg1 arg2
        geq body1 body2
    | otherwise = Nothing
  geq (Let bnd1 body1) (Let bnd2 body2) = do
    Refl <- geq bnd1 bnd2
    geq body1 body2
  geq _ _ = Nothing

instance (GEq v,GEq qv,GEq fun,GEq con,GEq field,GEq fv,GEq lv,GEq e)
         => Eq (Expression v qv fun con field fv lv e t) where
  (==) = defaultEq

instance (GCompare v,GCompare qv,GCompare fun,GCompare con,
          GCompare field,GCompare fv,GCompare lv,GCompare e)
         => GCompare (Expression v qv fun con field fv lv e) where
  gcompare (Var v1) (Var v2) = gcompare v1 v2
  gcompare (Var _) _ = GLT
  gcompare _ (Var _) = GGT
  gcompare (QVar v1) (QVar v2) = gcompare v1 v2
  gcompare (QVar _) _ = GLT
  gcompare _ (QVar _) = GGT
  gcompare (FVar v1) (FVar v2) = gcompare v1 v2
  gcompare (FVar _) _ = GLT
  gcompare _ (FVar _) = GGT
  gcompare (LVar v1) (LVar v2) = gcompare v1 v2
  gcompare (LVar _) _ = GLT
  gcompare _ (LVar _) = GGT
  gcompare (App f1 arg1) (App f2 arg2) = case gcompare f1 f2 of
    GEQ -> case gcompare arg1 arg2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (App _ _) _ = GLT
  gcompare _ (App _ _) = GGT
  gcompare (Const v1) (Const v2) = gcompare v1 v2
  gcompare (Const _) _ = GLT
  gcompare _ (Const _) = GGT
  gcompare (AsArray f1) (AsArray f2) = case gcompare f1 f2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (AsArray _) _ = GLT
  gcompare _ (AsArray _) = GGT
  gcompare (Quantification q1 arg1 body1) (Quantification q2 arg2 body2) = case compare q1 q2 of
    LT -> GLT
    GT -> GGT
    EQ -> case gcompare arg1 arg2 of
      GEQ -> gcompare body1 body2
      GLT -> GLT
      GGT -> GGT
  gcompare (Quantification _ _ _) _ = GLT
  gcompare _ (Quantification _ _ _) = GGT
  gcompare (Let bnd1 body1) (Let bnd2 body2) = case gcompare bnd1 bnd2 of
    GEQ -> gcompare body1 body2
    GLT -> GLT
    GGT -> GGT

instance (GCompare v,GCompare qv,GCompare fun,GCompare con,
          GCompare field,GCompare fv,GCompare lv,GCompare e)
         => Ord (Expression v qv fun con field fv lv e t) where
  compare = defaultCompare

instance (GEq fun,GEq con,GEq field) => GEq (Function fun con field) where
  geq (Fun f1) (Fun f2) = geq f1 f2
  geq f1@Eq f2@Eq = case f1 of
    (_::Function fun con field '(arg1,BoolType)) -> case f2 of
      (_::Function fun con field '(arg2,BoolType)) -> do
        Refl <- eqT :: Maybe (arg1 :~: arg2)
        return Refl
  geq f1@Distinct f2@Distinct = case f1 of
    (_::Function fun con field '(arg1,BoolType)) -> case f2 of
      (_::Function fun con field '(arg2,BoolType)) -> do
        Refl <- eqT :: Maybe (arg1 :~: arg2)
        return Refl
  geq m1@(Map f1) m2@(Map f2) = do
    Refl <- geq f1 f2
    case f1 of
      (_::Function fun con field '(arg,res)) -> case m1 of
        (_::Function fun con field '(Lifted arg idx1,ArrayType idx1 res)) -> case m2 of
          (_::Function fun con field '(Lifted arg idx2,ArrayType idx2 res)) -> do
            Refl <- eqT :: Maybe (idx1 :~: idx2)
            return Refl
  geq (OrdInt o1) (OrdInt o2) = if o1==o2 then Just Refl else Nothing
  geq (OrdReal o1) (OrdReal o2) = if o1==o2 then Just Refl else Nothing
  geq f1@(ArithInt o1) f2@(ArithInt o2)
    = if o1==o2
      then case f1 of
        (_::Function fun con field '(arg1,IntType)) -> case f2 of
          (_::Function fun con field '(arg2,IntType)) -> do
            Refl <- eqT :: Maybe (arg1 :~: arg2)
            return Refl
      else Nothing
  geq f1@(ArithReal o1) f2@(ArithReal o2)
    = if o1==o2
      then case f1 of
        (_::Function fun con field '(arg1,RealType)) -> case f2 of
          (_::Function fun con field '(arg2,RealType)) -> do
            Refl <- eqT :: Maybe (arg1 :~: arg2)
            return Refl
      else Nothing
  geq (ArithIntBin o1) (ArithIntBin o2) = if o1==o2 then Just Refl else Nothing
  geq Divide Divide = Just Refl
  geq AbsInt AbsInt = Just Refl
  geq AbsReal AbsReal = Just Refl
  geq Not Not = Just Refl
  geq f1@(Logic o1) f2@(Logic o2)
    = if o1==o2
      then case f1 of
        (_::Function fun con field '(arg1,BoolType)) -> case f2 of
          (_::Function fun con field '(arg2,BoolType)) -> do
            Refl <- eqT :: Maybe (arg1 :~: arg2)
            return Refl
      else Nothing
  geq ToReal ToReal = Just Refl
  geq ToInt ToInt = Just Refl
  geq f1@ITE f2@ITE = case f1 of
    (_::Function fun con field '([BoolType,t1,t1],t1)) -> case f2 of
      (_::Function fun con field '([BoolType,t2,t2],t2)) -> do
        Refl <- eqT :: Maybe (t1 :~: t2)
        return Refl
  geq f1@(BVComp o1) f2@(BVComp o2)
    = if o1==o2
      then case f1 of
        (_::Function fun con field '([BitVecType t1,BitVecType t1],BoolType)) -> case f2 of
          (_::Function fun con field '([BitVecType t2,BitVecType t2],BoolType)) -> do
            Refl <- eqT :: Maybe (t1 :~: t2)
            return Refl
      else Nothing
  geq f1@(BVBin o1) f2@(BVBin o2)
    = if o1==o2
      then case f1 of
        (_::Function fun con field '([BitVecType t1,BitVecType t1],BitVecType t1)) -> case f2 of
          (_::Function fun con field '([BitVecType t2,BitVecType t2],BitVecType t2)) -> do
            Refl <- eqT :: Maybe (t1 :~: t2)
            return Refl
      else Nothing
  geq f1@(BVUn o1) f2@(BVUn o2)
    = if o1==o2
      then case f1 of
        (_::Function fun con field '( '[BitVecType t1],BitVecType t1)) -> case f2 of
          (_::Function fun con field '( '[BitVecType t2],BitVecType t2)) -> do
            Refl <- eqT :: Maybe (t1 :~: t2)
            return Refl
      else Nothing
  geq f1@Select f2@Select
    = case f1 of
      (_::Function fun con field '(ArrayType idx1 val1 ': idx1,val1)) -> case f2 of
        (_::Function fun con field '(ArrayType idx2 val2 ': idx2,val2)) -> do
          Refl <- eqT :: Maybe (idx1 :~: idx2)
          Refl <- eqT :: Maybe (val1 :~: val2)
          return Refl
  geq f1@Store f2@Store
    = case f1 of
      (_::Function fun con field '(ArrayType idx1 val1 ': val1 ': idx1,ArrayType idx1 val1)) -> case f2 of
        (_::Function fun con field '(ArrayType idx2 val2 ': val2 ': idx2,ArrayType idx2 val2)) -> do
          Refl <- eqT :: Maybe (idx1 :~: idx2)
          Refl <- eqT :: Maybe (val1 :~: val2)
          return Refl
  geq f1@ConstArray f2@ConstArray = case f1 of
    (_::Function fun con field '( '[val1],ArrayType idx1 val1)) -> case f2 of
      (_::Function fun con field '( '[val2],ArrayType idx2 val2)) -> do
         Refl <- eqT :: Maybe (idx1 :~: idx2)
         Refl <- eqT :: Maybe (val1 :~: val2)
         return Refl
  geq f1@Concat f2@Concat = case f1 of
    (_::Function fun con field '( '[BitVecType a1,BitVecType b1],BitVecType (a1+b1))) -> case f2 of
      (_::Function fun con field '( '[BitVecType a2,BitVecType b2],BitVecType (a2+b2))) -> do
        Refl <- eqT :: Maybe (a1 :~: a2)
        Refl <- eqT :: Maybe (b1 :~: b2)
        return Refl
  geq f1@(Extract (_::Proxy s1)) f2@(Extract (_::Proxy s2)) = do
    Refl <- eqT :: Maybe (s1 :~: s2)
    case f1 of
      (_::Function fun con field '( '[BitVecType a1],BitVecType len1)) -> case f2 of
        (_::Function fun con field '( '[BitVecType a2],BitVecType len2)) -> do
          Refl <- eqT :: Maybe (a1 :~: a2)
          Refl <- eqT :: Maybe (len1 :~: len2)
          return Refl
  geq (Constructor c1) (Constructor c2) = do
    Refl <- geq c1 c2
    return Refl
  geq (Test c1) (Test c2) = do
    Refl <- geq c1 c2
    return Refl
  geq (Field f1) (Field f2) = do
    Refl <- geq f1 f2
    return Refl
  geq (Divisible n1) (Divisible n2) = if n1==n2 then Just Refl else Nothing
  geq _ _ = Nothing

instance (GCompare fun,GCompare con,GCompare field)
         => GCompare (Function fun con field) where
  gcompare (Fun x) (Fun y) = gcompare x y
  gcompare (Fun _) _ = GLT
  gcompare _ (Fun _) = GGT
  gcompare f1@Eq f2@Eq = case f1 of
    (_::Function fun con field '(arg1,BoolType)) -> case f2 of
      (_::Function fun con field '(arg2,BoolType))
        -> case gcompare (getTypes::Args Repr arg1)
                         (getTypes::Args Repr arg2) of
             GEQ -> GEQ
             GLT -> GLT
             GGT -> GGT
  gcompare Eq _ = GLT
  gcompare _ Eq = GGT
  gcompare f1@Distinct f2@Distinct = case f1 of
    (_::Function fun con field '(arg1,BoolType)) -> case f2 of
      (_::Function fun con field '(arg2,BoolType))
        -> case gcompare (getTypes::Args Repr arg1)
                         (getTypes::Args Repr arg2) of
             GEQ -> GEQ
             GLT -> GLT
             GGT -> GGT
  gcompare Distinct _ = GLT
  gcompare _ Distinct = GGT
  gcompare m1@(Map f1) m2@(Map f2) = case gcompare f1 f2 of
    GEQ -> case f1 of
      (_::Function fun con field '(arg,res)) -> case m1 of
        (_::Function fun con field '(Lifted arg idx1,ArrayType idx1 res)) -> case m2 of
          (_::Function fun con field '(Lifted arg idx2,ArrayType idx2 res))
            -> case gcompare (getTypes::Args Repr idx1)
                             (getTypes::Args Repr idx2) of
                 GEQ -> GEQ
                 GLT -> GLT
                 GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Map _) _ = GLT
  gcompare _ (Map _) = GGT
  gcompare (OrdInt o1) (OrdInt o2) = case compare o1 o2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (OrdInt _) _ = GLT
  gcompare _ (OrdInt _) = GGT
  gcompare (OrdReal o1) (OrdReal o2) = case compare o1 o2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (OrdReal _) _ = GLT
  gcompare _ (OrdReal _) = GGT
  gcompare f1@(ArithInt o1) f2@(ArithInt o2) = case compare o1 o2 of
    EQ -> case f1 of
      (_::Function fun con field '(arg1,IntType)) -> case f2 of
        (_::Function fun con field '(arg2,IntType))
          -> case gcompare (getTypes::Args Repr arg1)
                           (getTypes::Args Repr arg2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (ArithInt _) _ = GLT
  gcompare _ (ArithInt _) = GGT
  gcompare f1@(ArithReal o1) f2@(ArithReal o2) = case compare o1 o2 of
    EQ -> case f1 of
      (_::Function fun con field '(arg1,RealType)) -> case f2 of
        (_::Function fun con field '(arg2,RealType))
          -> case gcompare (getTypes::Args Repr arg1)
                           (getTypes::Args Repr arg2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (ArithReal _) _ = GLT
  gcompare _ (ArithReal _) = GGT
  gcompare (ArithIntBin o1) (ArithIntBin o2) = case compare o1 o2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (ArithIntBin _) _ = GLT
  gcompare _ (ArithIntBin _) = GGT
  gcompare Divide Divide = GEQ
  gcompare Divide _ = GLT
  gcompare _ Divide = GGT
  gcompare AbsInt AbsInt = GEQ
  gcompare AbsInt _ = GLT
  gcompare _ AbsInt = GGT
  gcompare AbsReal AbsReal = GEQ
  gcompare AbsReal _ = GLT
  gcompare _ AbsReal = GGT
  gcompare Not Not = GEQ
  gcompare Not _ = GLT
  gcompare _ Not = GGT
  gcompare f1@(Logic o1) f2@(Logic o2) = case compare o1 o2 of
    EQ -> case f1 of
      (_::Function fun con field '(arg1,BoolType)) -> case f2 of
        (_::Function fun con field '(arg2,BoolType))
          -> case gcompare (getTypes::Args Repr arg1)
                           (getTypes::Args Repr arg2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (Logic _) _ = GLT
  gcompare _ (Logic _) = GGT
  gcompare ToReal ToReal = GEQ
  gcompare ToReal _ = GLT
  gcompare _ ToReal = GGT
  gcompare ToInt ToInt = GEQ
  gcompare ToInt _ = GLT
  gcompare _ ToInt = GGT
  gcompare f1@ITE f2@ITE = case f1 of
    (_::Function fun con field '([BoolType,a,a],a)) -> case f2 of
      (_::Function fun con field '([BoolType,b,b],b))
        -> case gcompare (getType::Repr a)
                         (getType::Repr b) of
             GEQ -> GEQ
             GLT -> GLT
             GGT -> GGT
  gcompare ITE _ = GLT
  gcompare _ ITE = GGT
  gcompare f1@(BVComp o1) f2@(BVComp o2) = case compare o1 o2 of
    EQ -> case f1 of
      (_::Function fun con field '([BitVecType n1,BitVecType n1],BoolType)) -> case f2 of
        (_::Function fun con field '([BitVecType n2,BitVecType n2],BoolType))
          -> case compareNat (Proxy::Proxy n1) (Proxy::Proxy n2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (BVComp _) _ = GLT
  gcompare _ (BVComp _) = GGT
  gcompare f1@(BVBin o1) f2@(BVBin o2) = case compare o1 o2 of
    EQ -> case f1 of
      (_::Function fun con field '([BitVecType n1,BitVecType n1],BitVecType n1)) -> case f2 of
        (_::Function fun con field '([BitVecType n2,BitVecType n2],BitVecType n2))
          -> case compareNat (Proxy::Proxy n1) (Proxy::Proxy n2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (BVBin _) _ = GLT
  gcompare _ (BVBin _) = GGT
  gcompare f1@(BVUn o1) f2@(BVUn o2) = case compare o1 o2 of
    EQ -> case f1 of
      (_::Function fun con field '( '[BitVecType n1],BitVecType n1)) -> case f2 of
        (_::Function fun con field '( '[BitVecType n2],BitVecType n2))
          -> case compareNat (Proxy::Proxy n1) (Proxy::Proxy n2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (BVUn _) _ = GLT
  gcompare _ (BVUn _) = GGT
  gcompare f1@Select f2@Select = case f1 of
    (_::Function fun con field '(ArrayType idx1 val1 ': idx1,val1)) -> case f2 of
      (_::Function fun con field '(ArrayType idx2 val2 ': idx2,val2))
        -> case gcompare (getTypes::Args Repr idx1)
                         (getTypes::Args Repr idx2) of
             GEQ -> case gcompare (getType::Repr val1)
                                  (getType::Repr val2) of
                      GEQ -> GEQ
                      GLT -> GLT
                      GGT -> GGT
             GLT -> GLT
             GGT -> GGT
  gcompare Select _ = GLT
  gcompare _ Select = GGT
  gcompare f1@Store f2@Store = case f1 of
    (_::Function fun con field '(ArrayType idx1 val1 ': val1 ': idx1,
                                 ArrayType idx1 val1)) -> case f2 of
      (_::Function fun con field '(ArrayType idx2 val2 ': val2 ': idx2,
                                   ArrayType idx2 val2))
        -> case gcompare (getTypes::Args Repr idx1)
                         (getTypes::Args Repr idx2) of
             GEQ -> case gcompare (getType::Repr val1)
                                  (getType::Repr val2) of
                      GEQ -> GEQ
                      GLT -> GLT
                      GGT -> GGT
             GLT -> GLT
             GGT -> GGT
  gcompare Store _ = GLT
  gcompare _ Store = GGT
  gcompare f1@ConstArray f2@ConstArray = case f1 of
    (_::Function fun con field '( '[val1],ArrayType idx1 val1)) -> case f2 of
      (_::Function fun con field '( '[val2],ArrayType idx2 val2))
        -> case gcompare (getType::Repr val1)
                         (getType::Repr val2) of
             GEQ -> case gcompare (getTypes::Args Repr idx1)
                                  (getTypes::Args Repr idx2) of
                      GEQ -> GEQ
                      GLT -> GLT
                      GGT -> GGT
             GLT -> GLT
             GGT -> GGT
  gcompare ConstArray _ = GLT
  gcompare _ ConstArray = GGT
  gcompare f1@Concat f2@Concat = case f1 of
    (_::Function fun con field '( '[BitVecType n1,BitVecType n2],
                                  BitVecType (n1 + n2))) -> case f2 of
      (_::Function fun con field '( '[BitVecType m1,BitVecType m2],
                                    BitVecType (m1 + m2)))
        -> case compareNat (Proxy::Proxy n1) (Proxy::Proxy m1) of
             GEQ -> case compareNat (Proxy::Proxy n2) (Proxy::Proxy m2) of
               GEQ -> GEQ
               GLT -> GLT
               GGT -> GGT
             GLT -> GLT
             GGT -> GGT
  gcompare Concat _ = GLT
  gcompare _ Concat = GGT
  gcompare f1@(Extract p1) f2@(Extract p2) = case compareNat p1 p2 of
    GEQ -> case f1 of
      (_::Function fun con field '( '[BitVecType a1],BitVecType len1)) -> case f2 of
        (_::Function fun con field '( '[BitVecType a2],BitVecType len2))
          -> case compareNat (Proxy::Proxy a1) (Proxy::Proxy a2) of
               GEQ -> case compareNat (Proxy::Proxy len1) (Proxy::Proxy len2) of
                 GEQ -> GEQ
                 GLT -> GLT
                 GGT -> GGT
               GLT -> GLT
               GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Extract _) _ = GLT
  gcompare _ (Extract _) = GGT
  gcompare (Constructor c1) (Constructor c2) = case gcompare c1 c2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Constructor _) _ = GLT
  gcompare _ (Constructor _) = GGT
  gcompare (Test c1) (Test c2) = case gcompare c1 c2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Test _) _ = GLT
  gcompare _ (Test _) = GGT
  gcompare (Field f1) (Field f2) = case gcompare f1 f2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Field _) _ = GLT
  gcompare _ (Field _) = GGT
  gcompare (Divisible n1) (Divisible n2) = case compare n1 n2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT

compareNat :: (KnownNat a,KnownNat b) => Proxy a -> Proxy b -> GOrdering a b
compareNat (prA::Proxy a) (prB::Proxy b) = case eqT::Maybe (a :~: b) of
  Just Refl -> GEQ
  Nothing -> case compare (natVal prA) (natVal prB) of
    LT -> GLT
    GT -> GGT

data NoVar (t::Type) = NoVar'
data NoFun (sig::([Type],Type)) = NoFun'
data NoCon (sig::([Type],*)) = NoCon'
data NoField (sig::(*,Type)) = NoField'

instance GEq NoVar where
  geq _ _ = error "geq for NoVar"

instance GEq NoFun where
  geq _ _ = error "geq for NoFun"

instance GEq NoCon where
  geq _ _ = error "geq for NoCon"

instance GEq NoField where
  geq _ _ = error "geq for NoField"

instance GCompare NoVar where
  gcompare _ _ = error "gcompare for NoVar"

instance GCompare NoFun where
  gcompare _ _ = error "gcompare for NoFun"

instance GCompare NoCon where
  gcompare _ _ = error "gcompare for NoCon"

instance GCompare NoField where
  gcompare _ _ = error "gcompare for NoField"

instance Eq (NoVar t) where
  (==) _ _ = error "== for NoVar"

instance Eq (NoFun t) where
  (==) _ _ = error "== for NoFun"

instance Eq (NoCon t) where
  (==) _ _ = error "== for NoCon"

instance Eq (NoField t) where
  (==) _ _ = error "== for NoField"

instance Ord (NoVar t) where
  compare _ _ = error "compare for NoVar"

instance Ord (NoFun t) where
  compare _ _ = error "compare for NoFun"

instance Ord (NoCon t) where
  compare _ _ = error "compare for NoCon"

instance Ord (NoField t) where
  compare _ _ = error "compare for NoField"

instance Show (NoVar t) where
  showsPrec _ _ = showString "NoVar"

instance GShow NoVar where
  gshowsPrec = showsPrec

instance Show (NoFun t) where
  showsPrec _ _ = showString "NoFun"

instance GShow NoFun where
  gshowsPrec = showsPrec

instance Show (NoCon t) where
  showsPrec _ _ = showString "NoCon"

instance GShow NoCon where
  gshowsPrec = showsPrec

instance Show (NoField t) where
  showsPrec _ _ = showString "NoVar"

instance GShow NoField where
  gshowsPrec = showsPrec
