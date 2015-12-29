module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.Typeable
import Text.Show
import Data.GADT.Compare
import Data.GADT.Show
import Data.Functor.Identity

type family AllEq (tp :: Type) (n :: Nat) :: [Type] where
  AllEq tp Z = '[]
  AllEq tp (S n) = tp ': (AllEq tp n)

allEqToList :: Natural n -> List a (AllEq tp n) -> [a tp]
allEqToList Zero Nil = []
allEqToList (Succ n) (Cons x xs) = x:allEqToList n xs

allEqFromList :: [a tp] -> (forall n. Natural n -> List a (AllEq tp n) -> r) -> r
allEqFromList [] f = f Zero Nil
allEqFromList (x:xs) f = allEqFromList xs (\n arg -> f (Succ n) (Cons x arg))

allEqOf :: Repr tp -> Natural n -> List Repr (AllEq tp n)
allEqOf tp Zero = Nil
allEqOf tp (Succ n) = Cons tp (allEqOf tp n)

mapAllEq :: Monad m => (e1 tp -> m (e2 tp))
         -> Natural n
         -> List e1 (AllEq tp n)
         -> m (List e2 (AllEq tp n))
mapAllEq f Zero Nil = return Nil
mapAllEq f (Succ n) (Cons x xs) = do
  x' <- f x
  xs' <- mapAllEq f n xs
  return (Cons x' xs')

data Function (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) (sig :: ([Type],Type)) where
  Fun :: fun '(arg,res) -> Function fun con field '(arg,res)
  Eq :: Repr tp -> Natural n -> Function fun con field '(AllEq tp n,BoolType)
  Distinct :: Repr tp -> Natural n -> Function fun con field '(AllEq tp n,BoolType)
  Map :: List Repr idx -> Function fun con field '(arg,res)
      -> Function fun con field '(Lifted arg idx,ArrayType idx res)
  Ord :: NumRepr tp -> OrdOp -> Function fun con field '([tp,tp],BoolType)
  Arith :: NumRepr tp -> ArithOp -> Natural n
        -> Function fun con field '(AllEq tp n,tp)
  ArithIntBin :: ArithOpInt -> Function fun con field '([IntType,IntType],IntType)
  Divide :: Function fun con field '([RealType,RealType],RealType)
  Abs :: NumRepr tp -> Function fun con field '( '[tp],tp)
  Not :: Function fun con field '( '[BoolType],BoolType)
  Logic :: LogicOp -> Natural n -> Function fun con field '(AllEq BoolType n,BoolType)
  ToReal :: Function fun con field '( '[IntType],RealType)
  ToInt :: Function fun con field '( '[RealType],IntType)
  ITE :: Repr a -> Function fun con field '([BoolType,a,a],a)
  BVComp :: BVCompOp -> Natural a -> Function fun con field '([BitVecType a,BitVecType a],BoolType)
  BVBin :: BVBinOp -> Natural a -> Function fun con field '([BitVecType a,BitVecType a],BitVecType a)
  BVUn :: BVUnOp -> Natural a -> Function fun con field '( '[BitVecType a],BitVecType a)
  Select :: List Repr idx -> Repr val -> Function fun con field '(ArrayType idx val ': idx,val)
  Store :: List Repr idx -> Repr val -> Function fun con field '(ArrayType idx val ': val ': idx,ArrayType idx val)
  ConstArray :: List Repr idx -> Repr val -> Function fun con field '( '[val],ArrayType idx val)
  Concat :: Natural n1 -> Natural n2 -> Function fun con field '([BitVecType n1,BitVecType n2],BitVecType (n1 + n2))
  Extract :: (((start + len) <= bw) ~ True)
          => Natural bw -> Natural start -> Natural len -> Function fun con field '( '[BitVecType bw],BitVecType len)
  Constructor :: IsDatatype a => con '(arg,a)
              -> Function fun con field '(arg,DataType a)
  Test :: (IsDatatype a) => con '(arg,a) -> Function fun con field '( '[DataType a],BoolType)
  Field :: (IsDatatype a) => field '(a,t) -> Function fun con field '( '[DataType a],t)
  Divisible :: Integer -> Function fun con field '( '[IntType],BoolType)

data AnyFunction (fun :: ([Type],Type) -> *) (con :: ([Type],*) -> *) (field :: (*,Type) -> *) where
  AnyFunction :: Function fun con field '(arg,t) -> AnyFunction fun con field

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
  Var :: v res -> Expression v qv fun con field fv lv e res
  QVar :: qv res -> Expression v qv fun con field fv lv e res
  FVar :: fv res -> Expression v qv fun con field fv lv e res
  LVar :: lv res -> Expression v qv fun con field fv lv e res
  App :: Function fun con field '(arg,res)
      -> List e arg
      -> Expression v qv fun con field fv lv e res
  Const :: Value con a -> Expression v qv fun con field fv lv e a
  AsArray :: Function fun con field '(arg,res)
          -> Expression v qv fun con field fv lv e (ArrayType arg res)
  Quantification :: Quantifier -> List qv arg -> e BoolType
                 -> Expression v qv fun con field fv lv e BoolType
  Let :: List (LetBinding lv e) arg
      -> e res
      -> Expression v qv fun con field fv lv e res

instance (GEq fun,GEq con,GEq field)
         => Eq (Function fun con field sig) where
  (==) = defaultEq

class SMTOrd (t :: Type) where
  lt :: Function fun con field '( '[t,t],BoolType)
  le :: Function fun con field '( '[t,t],BoolType)
  gt :: Function fun con field '( '[t,t],BoolType)
  ge :: Function fun con field '( '[t,t],BoolType)

instance SMTOrd IntType where
  lt = Ord NumInt Lt
  le = Ord NumInt Le
  gt = Ord NumInt Gt
  ge = Ord NumInt Ge

instance SMTOrd RealType where
  lt = Ord NumReal Lt
  le = Ord NumReal Le
  gt = Ord NumReal Gt
  ge = Ord NumReal Ge

class SMTArith t where
  arithFromInteger :: Integer -> ConcreteValue t
  arith :: ArithOp -> Natural n -> Function fun con field '(AllEq t n,t)
  plus :: Natural n -> Function fun con field '(AllEq t n,t)
  minus :: Natural n -> Function fun con field '(AllEq t n,t)
  mult :: Natural n -> Function fun con field '(AllEq t n,t)
  abs' :: Function fun con field '( '[t],t)

instance SMTArith IntType where
  arithFromInteger n = IntValueC n
  arith = Arith NumInt
  plus = Arith NumInt Plus
  minus = Arith NumInt Minus
  mult = Arith NumInt Mult
  abs' = Abs NumInt

instance SMTArith RealType where
  arithFromInteger n = RealValueC (fromInteger n)
  arith = Arith NumReal
  plus = Arith NumReal Plus
  minus = Arith NumReal Minus
  mult = Arith NumReal Mult
  abs' = Abs NumReal

functionType :: (forall arg t. fun '(arg,t) -> (List Repr arg,Repr t))
             -> (forall arg dt. IsDatatype dt => con '(arg,dt)
                 -> (List Repr arg,Datatype '(DatatypeSig dt,dt)))
             -> (forall dt t. IsDatatype dt => field '(dt,t)
                 -> (Datatype '(DatatypeSig dt,dt),Repr t))
             -> Function fun con field '(arg,res)
             -> (List Repr arg,Repr res)
functionType f _ _ (Fun fun) = f fun
functionType _ _ _ (Eq tp n) = (allEqOf tp n,BoolRepr)
functionType _ _ _ (Distinct tp n) = (allEqOf tp n,BoolRepr)
functionType f g h (Map idx fun) = let (arg,res) = functionType f g h fun
                                   in (liftType arg idx,ArrayRepr idx res)
functionType _ _ _ (Ord tp _) = (Cons (numRepr tp) (Cons (numRepr tp) Nil),BoolRepr)
functionType _ _ _ (Arith tp _ n) = (allEqOf (numRepr tp) n,numRepr tp)
functionType _ _ _ (ArithIntBin _) = (Cons IntRepr (Cons IntRepr Nil),IntRepr)
functionType _ _ _ Divide = (Cons RealRepr (Cons RealRepr Nil),RealRepr)
functionType _ _ _ (Abs tp) = (Cons (numRepr tp) Nil,numRepr tp)
functionType _ _ _ Not = (Cons BoolRepr Nil,BoolRepr)
functionType _ _ _ (Logic op n) = (allEqOf BoolRepr n,BoolRepr)
functionType _ _ _ ToReal = (Cons IntRepr Nil,RealRepr)
functionType _ _ _ ToInt = (Cons RealRepr Nil,IntRepr)
functionType _ _ _ (ITE tp) = (Cons BoolRepr (Cons tp (Cons tp Nil)),tp)
functionType _ _ _ (BVComp _ n) = (Cons (BitVecRepr n) (Cons (BitVecRepr n) Nil),BoolRepr)
functionType _ _ _ (BVBin _ n) = (Cons (BitVecRepr n) (Cons (BitVecRepr n) Nil),BitVecRepr n)
functionType _ _ _ (BVUn _ n) = (Cons (BitVecRepr n) Nil,BitVecRepr n)
functionType _ _ _ (Select idx el) = (Cons (ArrayRepr idx el) idx,el)
functionType _ _ _ (Store idx el) = (Cons (ArrayRepr idx el) (Cons el idx),ArrayRepr idx el)
functionType _ _ _ (ConstArray idx el) = (Cons el Nil,ArrayRepr idx el)
functionType _ _ _ (Concat bw1 bw2) = (Cons (BitVecRepr bw1) (Cons (BitVecRepr bw2) Nil),
                                       BitVecRepr (naturalAdd bw1 bw2))
functionType _ _ _ (Extract bw start len) = (Cons (BitVecRepr bw) Nil,BitVecRepr len)
functionType _ f _ (Constructor con) = let (tps,dt) = f con
                                       in (tps,DataRepr dt)
functionType _ f _ (Test con) = let (_,dt) = f con
                                in (Cons (DataRepr dt) Nil,BoolRepr)
functionType _ _ f (Field field) = let (dt,tp) = f field
                                   in (Cons (DataRepr dt) Nil,tp)
functionType _ _ _ (Divisible _) = (Cons IntRepr Nil,BoolRepr)

expressionType :: (forall t. v t -> Repr t)
               -> (forall t. qv t -> Repr t)
               -> (forall arg t. fun '(arg,t) -> (List Repr arg,Repr t))
               -> (forall arg dt. IsDatatype dt => con '(arg,dt)
                   -> (List Repr arg,Datatype '(DatatypeSig dt,dt)))
               -> (forall dt t. IsDatatype dt => field '(dt,t)
                   -> (Datatype '(DatatypeSig dt,dt),Repr t))
               -> (forall t. fv t -> Repr t)
               -> (forall t. lv t -> Repr t)
               -> (forall t. e t -> Repr t)
               -> Expression v qv fun con field fv lv e res
               -> Repr res
expressionType f _ _ _ _ _ _ _ (Var v) = f v
expressionType _ f _ _ _ _ _ _ (QVar v) = f v
expressionType _ _ _ _ _ f _ _ (FVar v) = f v
expressionType _ _ _ _ _ _ f _ (LVar v) = f v
expressionType _ _ f g h _ _ _ (App fun arg) = snd $ functionType f g h fun
expressionType _ _ _ _ _ _ _ _ (Const v) = valueType v
expressionType _ _ f g h _ _ _ (AsArray fun) = let (arg,res) = functionType f g h fun
                                               in ArrayRepr arg res
expressionType _ _ _ _ _ _ _ _ (Quantification _ _ _) = BoolRepr
expressionType _ _ _ _ _ _ _ f (Let _ body) = f body

mapExpr :: (Functor m,Monad m,Typeable con2)
        => (forall t. v1 t -> m (v2 t)) -- ^ How to translate variables
        -> (forall t. qv1 t -> m (qv2 t)) -- ^ How to translate quantified variables
        -> (forall arg t. fun1 '(arg,t) -> m (fun2 '(arg,t))) -- ^ How to translate functions
        -> (forall arg t. con1 '(arg,t) -> m (con2 '(arg,t))) -- ^ How to translate constructrs
        -> (forall t res. field1 '(t,res) -> m (field2 '(t,res))) -- ^ How to translate field accessors
        -> (forall t. fv1 t -> m (fv2 t)) -- ^ How to translate function variables
        -> (forall t. lv1 t -> m (lv2 t)) -- ^ How to translate let variables
        -> (forall t. e1 t -> m (e2 t)) -- ^ How to translate sub-expressions
        -> Expression v1 qv1 fun1 con1 field1 fv1 lv1 e1 r -- ^ The expression to translate
        -> m (Expression v2 qv2 fun2 con2 field2 fv2 lv2 e2 r)
mapExpr f _ _ _ _ _ _ _ (Var v) = fmap Var (f v)
mapExpr _ f _ _ _ _ _ _ (QVar v) = fmap QVar (f v)
mapExpr _ _ _ _ _ f _ _ (FVar v) = fmap FVar (f v)
mapExpr _ _ _ _ _ _ f _ (LVar v) = fmap LVar (f v)
mapExpr _ _ f g h _ _ i (App fun args) = do
  fun' <- mapFunction f g h fun
  args' <- List.mapM i args
  return (App fun' args')
mapExpr _ _ _ f _ _ _ _ (Const val) = fmap Const (mapValue f val)
mapExpr _ _ f g h _ _ _ (AsArray fun) = fmap AsArray (mapFunction f g h fun)
mapExpr _ f _ _ _ _ _ g (Quantification q args body) = do
  args' <- List.mapM f args
  body' <- g body
  return (Quantification q args' body')
mapExpr _ _ _ _ _ _ f g (Let args body) = do
  args' <- List.mapM (\bind -> do
                         nv <- f (letVar bind)
                         nexpr <- g (letExpr bind)
                         return $ LetBinding nv nexpr
                     ) args
  body' <- g body
  return (Let args' body')

mapFunction :: (Functor m,Monad m)
            => (forall arg t. fun1 '(arg,t) -> m (fun2 '(arg,t)))
            -> (forall arg t. con1 '(arg,t) -> m (con2 '(arg,t)))
            -> (forall t res. field1 '(t,res) -> m (field2 '(t,res)))
            -> Function fun1 con1 field1 '(arg,res)
            -> m (Function fun2 con2 field2 '(arg,res))
mapFunction f _ _ (Fun x) = fmap Fun (f x)
mapFunction _ _ _ (Eq tp n) = return (Eq tp n)
mapFunction _ _ _ (Distinct tp n) = return (Distinct tp n)
mapFunction f g h (Map idx x) = do
  x' <- mapFunction f g h x
  return (Map idx x')
mapFunction _ _ _ (Ord tp op) = return (Ord tp op)
mapFunction _ _ _ (Arith tp op n) = return (Arith tp op n)
mapFunction _ _ _ (ArithIntBin op) = return (ArithIntBin op)
mapFunction _ _ _ Divide = return Divide
mapFunction _ _ _ (Abs tp) = return (Abs tp)
mapFunction _ _ _ Not = return Not
mapFunction _ _ _ (Logic op n) = return (Logic op n)
mapFunction _ _ _ ToReal = return ToReal
mapFunction _ _ _ ToInt = return ToInt
mapFunction _ _ _ (ITE tp) = return (ITE tp)
mapFunction _ _ _ (BVComp op bw) = return (BVComp op bw)
mapFunction _ _ _ (BVBin op bw) = return (BVBin op bw)
mapFunction _ _ _ (BVUn op bw) = return (BVUn op bw)
mapFunction _ _ _ (Select idx el) = return (Select idx el)
mapFunction _ _ _ (Store idx el) = return (Store idx el)
mapFunction _ _ _ (ConstArray idx el) = return (ConstArray idx el)
mapFunction _ _ _ (Concat bw1 bw2) = return (Concat bw1 bw2)
mapFunction _ _ _ (Extract bw start len) = return (Extract bw start len)
mapFunction _ f _ (Constructor con) = fmap Constructor (f con)
mapFunction _ f _ (Test con) = fmap Test (f con)
mapFunction _ _ f (Field x) = fmap Field (f x)
mapFunction _ _ _ (Divisible x) = return (Divisible x)

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
      showsPrec 11 args
  showsPrec p (Const val) = showsPrec p val
  showsPrec p (AsArray fun)
    = showParen (p>10) $
      showString "AsArray " .
      showsPrec 11 fun
  showsPrec p (Quantification q args body)
    = showParen (p>10) $
      showsPrec 11 q .
      showChar ' ' .
      showsPrec 11 args .
      showChar ' ' .
      gshowsPrec 11 body
  showsPrec p (Let args body)
    = showParen (p>10) $
      showString "Let " .
      showListWith id (runIdentity $ List.toList
                       (\(LetBinding v e)
                        -> return $ (gshowsPrec 10 v) . showChar '=' . (gshowsPrec 10 e)
                      ) args)  .
      showChar ' ' .
      gshowsPrec 10 body

instance (GShow v,GShow qv,GShow fun,GShow con,GShow field,GShow fv,GShow lv,GShow e)
         => GShow (Expression v qv fun con field fv lv e) where
  gshowsPrec = showsPrec

instance (GShow fun,GShow con,GShow field)
         => Show (Function fun con field sig) where
  showsPrec p (Fun x) = gshowsPrec p x
  showsPrec _ (Eq _ _) = showString "Eq"
  showsPrec _ (Distinct _ _) = showString "Distinct"
  showsPrec p (Map _ x) = showParen (p>10) $
                          showString "Map " .
                          showsPrec 11 x
  showsPrec p (Ord tp op) = showParen (p>10) $
                            showString "Ord " .
                            showsPrec 11 tp .
                            showChar ' ' .
                            showsPrec 11 op
  showsPrec p (Arith tp op _) = showParen (p>10) $
                                showString "Arith " .
                                showsPrec 11 tp .
                                showChar ' ' .
                                showsPrec 11 op
  showsPrec p (ArithIntBin op) = showParen (p>10) $
                                 showString "ArithIntBin " .
                                 showsPrec 11 op
  showsPrec p Divide = showString "Divide"
  showsPrec p (Abs tp) = showParen (p>10) $
                         showString "Abs " .
                         showsPrec 11 tp
  showsPrec _ Not =  showString "Not"
  showsPrec p (Logic op _) = showParen (p>10) $
                             showString "Logic " .
                             showsPrec 11 op
  showsPrec _ ToReal = showString "ToReal"
  showsPrec _ ToInt = showString "ToInt"
  showsPrec _ (ITE _) = showString "ITE"
  showsPrec p (BVComp op _) = showParen (p>10) $
                              showString "BVComp " .
                              showsPrec 11 op
  showsPrec p (BVBin op _) = showParen (p>10) $
                             showString "BVBin " .
                             showsPrec 11 op
  showsPrec p (BVUn op _) = showParen (p>10) $
                            showString "BVUn " .
                            showsPrec 11 op
  showsPrec _ (Select _ _) = showString "Select"
  showsPrec _ (Store _ _) = showString "Store"
  showsPrec _ (ConstArray _ _) = showString "ConstArray"
  showsPrec _ (Concat _ _) = showString "Concat"
  showsPrec p (Extract bw start len)
    = showParen (p>10) $
      showString "Extract " .
      showsPrec 11 bw .
      showChar ' ' .
      showsPrec 11 start .
      showChar ' ' .
      showsPrec 11 len
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
  geq (Eq tp1 n1) (Eq tp2 n2) = do
    Refl <- geq tp1 tp2
    Refl <- geq n1 n2
    return Refl
  geq (Distinct tp1 n1) (Distinct tp2 n2) = do
    Refl <- geq tp1 tp2
    Refl <- geq n1 n2
    return Refl
  geq (Map i1 f1) (Map i2 f2) = do
    Refl <- geq f1 f2
    Refl <- geq i1 i2
    return Refl
  geq (Ord tp1 o1) (Ord tp2 o2) = do
    Refl <- geq tp1 tp2
    if o1==o2 then return Refl else Nothing
  geq (Arith tp1 o1 n1) (Arith tp2 o2 n2) = do
    Refl <- geq tp1 tp2
    if o1==o2
      then do
      Refl <- geq n1 n2
      return Refl
      else Nothing
  geq (ArithIntBin o1) (ArithIntBin o2) = if o1==o2 then Just Refl else Nothing
  geq Divide Divide = Just Refl
  geq (Abs tp1) (Abs tp2) = do
    Refl <- geq tp1 tp2
    return Refl
  geq Not Not = Just Refl
  geq (Logic o1 n1) (Logic o2 n2)
    = if o1==o2
      then do
        Refl <- geq n1 n2
        return Refl
      else Nothing
  geq ToReal ToReal = Just Refl
  geq ToInt ToInt = Just Refl
  geq (ITE t1) (ITE t2) = do
    Refl <- geq t1 t2
    return Refl
  geq (BVComp o1 bw1) (BVComp o2 bw2)
    = if o1==o2
      then do
        Refl <- geq bw1 bw2
        return Refl
      else Nothing
  geq (BVBin o1 bw1) (BVBin o2 bw2)
    = if o1==o2
      then do
        Refl <- geq bw1 bw2
        return Refl
      else Nothing
  geq (BVUn o1 bw1) (BVUn o2 bw2)
    = if o1==o2
      then do
        Refl <- geq bw1 bw2
        return Refl
      else Nothing
  geq (Select i1 e1) (Select i2 e2) = do
    Refl <- geq i1 i2
    Refl <- geq e1 e2
    return Refl
  geq (Store i1 e1) (Store i2 e2) = do
    Refl <- geq i1 i2
    Refl <- geq e1 e2
    return Refl
  geq (ConstArray i1 e1) (ConstArray i2 e2) = do
    Refl <- geq i1 i2
    Refl <- geq e1 e2
    return Refl
  geq (Concat a1 b1) (Concat a2 b2) = do
    Refl <- geq a1 a2
    Refl <- geq b1 b2
    return Refl
  geq (Extract bw1 start1 len1) (Extract bw2 start2 len2) = do
    Refl <- geq bw1 bw2
    Refl <- geq start1 start2
    Refl <- geq len1 len2
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
  gcompare (Eq t1 n1) (Eq t2 n2) = case gcompare t1 t2 of
    GEQ -> case gcompare n1 n2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Eq _ _) _ = GLT
  gcompare _ (Eq _ _) = GGT
  gcompare (Distinct t1 n1) (Distinct t2 n2) = case gcompare t1 t2 of
    GEQ -> case gcompare n1 n2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Distinct _ _) _ = GLT
  gcompare _ (Distinct _ _) = GGT
  gcompare (Map i1 f1) (Map i2 f2) = case gcompare f1 f2 of
    GEQ -> case gcompare i1 i2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Map _ _) _ = GLT
  gcompare _ (Map _ _) = GGT
  gcompare (Ord tp1 o1) (Ord tp2 o2) = case gcompare tp1 tp2 of
    GEQ -> case compare o1 o2 of
      EQ -> GEQ
      LT -> GLT
      GT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Ord _ _) _ = GLT
  gcompare _ (Ord _ _) = GGT
  gcompare (Arith tp1 o1 n1) (Arith tp2 o2 n2) = case gcompare tp1 tp2 of
    GEQ -> case compare o1 o2 of
      EQ -> case gcompare n1 n2 of
        GEQ -> GEQ
        GLT -> GLT
        GGT -> GGT
      LT -> GLT
      GT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Arith _ _ _) _ = GLT
  gcompare _ (Arith _ _ _) = GGT
  gcompare (ArithIntBin o1) (ArithIntBin o2) = case compare o1 o2 of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (ArithIntBin _) _ = GLT
  gcompare _ (ArithIntBin _) = GGT
  gcompare Divide Divide = GEQ
  gcompare Divide _ = GLT
  gcompare _ Divide = GGT
  gcompare (Abs tp1) (Abs tp2) = case gcompare tp1 tp2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Abs _) _ = GLT
  gcompare _ (Abs _) = GGT
  gcompare Not Not = GEQ
  gcompare Not _ = GLT
  gcompare _ Not = GGT
  gcompare (Logic o1 n1) (Logic o2 n2) = case compare o1 o2 of
    EQ -> case gcompare n1 n2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (Logic _ _) _ = GLT
  gcompare _ (Logic _ _) = GGT
  gcompare ToReal ToReal = GEQ
  gcompare ToReal _ = GLT
  gcompare _ ToReal = GGT
  gcompare ToInt ToInt = GEQ
  gcompare ToInt _ = GLT
  gcompare _ ToInt = GGT
  gcompare (ITE t1) (ITE t2) = case gcompare t1 t2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (ITE _) _ = GLT
  gcompare _ (ITE _) = GGT
  gcompare (BVComp o1 bw1) (BVComp o2 bw2) = case compare o1 o2 of
    EQ -> case gcompare bw1 bw2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (BVComp _ _) _ = GLT
  gcompare _ (BVComp _ _) = GGT
  gcompare (BVBin o1 bw1) (BVBin o2 bw2) = case compare o1 o2 of
    EQ -> case gcompare bw1 bw2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (BVBin _ _) _ = GLT
  gcompare _ (BVBin _ _) = GGT
  gcompare (BVUn o1 bw1) (BVUn o2 bw2) = case compare o1 o2 of
    EQ -> case gcompare bw1 bw2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare (BVUn _ _) _ = GLT
  gcompare _ (BVUn _ _) = GGT
  gcompare (Select i1 e1) (Select i2 e2) = case gcompare i1 i2 of
    GEQ -> case gcompare e1 e2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Select _ _) _ = GLT
  gcompare _ (Select _ _) = GGT
  gcompare (Store i1 e1) (Store i2 e2) = case gcompare i1 i2 of
    GEQ -> case gcompare e1 e2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Store _ _) _ = GLT
  gcompare _ (Store _ _) = GGT
  gcompare (ConstArray i1 e1) (ConstArray i2 e2) = case gcompare i1 i2 of
    GEQ -> case gcompare e1 e2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (ConstArray _ _) _ = GLT
  gcompare _ (ConstArray _ _) = GGT
  gcompare (Concat a1 b1) (Concat a2 b2) = case gcompare a1 a2 of
    GEQ -> case gcompare b1 b2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Concat _ _) _ = GLT
  gcompare _ (Concat _ _) = GGT
  gcompare (Extract bw1 start1 len1) (Extract bw2 start2 len2)
    = case gcompare bw1 bw2 of
    GEQ -> case gcompare start1 start2 of
      GEQ -> case gcompare len1 len2 of
        GEQ -> GEQ
        GLT -> GLT
        GGT -> GGT
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT
  gcompare (Extract _ _ _) _ = GLT
  gcompare _ (Extract _ _ _) = GGT
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

instance GetType NoVar where
  getType _ = error "getType called on NoVar."

instance GetFunType NoFun where
  getFunType _ = error "getFunType called on NoFun."

instance GetConType NoCon where
  getConType _ = error "getConType called on NoCon."

instance GetFieldType NoField where
  getFieldType _ = error "getFieldType called on NoField."

instance (GetType v,GetType qv,GetFunType fun,GetConType con,
          GetFieldType field,GetType fv,GetType lv,GetType e)
         => GetType (Expression v qv fun con field fv lv e) where
  getType = expressionType getType getType getFunType getConType getFieldType
            getType getType getType

instance (GetFunType fun,GetConType con,GetFieldType field)
         => GetFunType (Function fun con field) where
  getFunType = functionType getFunType getConType getFieldType
