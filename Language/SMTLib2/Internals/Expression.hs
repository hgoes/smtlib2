module Language.SMTLib2.Internals.Expression where

import Language.SMTLib2.Internals.Type hiding (Field)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.Typeable
import Text.Show
import Data.GADT.Compare
import Data.GADT.Show
import Data.Functor.Identity
import Data.Ratio
import qualified GHC.TypeLits as TL

type family AllEq (tp :: Type) (n :: Nat) :: [Type] where
  AllEq tp Z = '[]
  AllEq tp (S n) = tp ': (AllEq tp n)

allEqToList :: Natural n -> List a (AllEq tp n) -> [a tp]
allEqToList Zero Nil = []
allEqToList (Succ n) (x ::: xs) = x:allEqToList n xs

allEqFromList :: [a tp] -> (forall n. Natural n -> List a (AllEq tp n) -> r) -> r
allEqFromList [] f = f Zero Nil
allEqFromList (x:xs) f = allEqFromList xs (\n arg -> f (Succ n) (x ::: arg))

allEqOf :: Repr tp -> Natural n -> List Repr (AllEq tp n)
allEqOf tp Zero = Nil
allEqOf tp (Succ n) = tp ::: allEqOf tp n

mapAllEq :: Monad m => (e1 tp -> m (e2 tp))
         -> Natural n
         -> List e1 (AllEq tp n)
         -> m (List e2 (AllEq tp n))
mapAllEq f Zero Nil = return Nil
mapAllEq f (Succ n) (x ::: xs) = do
  x' <- f x
  xs' <- mapAllEq f n xs
  return (x' ::: xs')

data Function (fun :: ([Type],Type) -> *) (sig :: ([Type],Type)) where
  Fun :: fun '(arg,res) -> Function fun '(arg,res)
  Eq :: Repr tp -> Natural n -> Function fun '(AllEq tp n,BoolType)
  Distinct :: Repr tp -> Natural n -> Function fun '(AllEq tp n,BoolType)
  Map :: List Repr idx -> Function fun '(arg,res)
      -> Function fun '(Lifted arg idx,ArrayType idx res)
  Ord :: NumRepr tp -> OrdOp -> Function fun '([tp,tp],BoolType)
  Arith :: NumRepr tp -> ArithOp -> Natural n
        -> Function fun '(AllEq tp n,tp)
  ArithIntBin :: ArithOpInt -> Function fun '([IntType,IntType],IntType)
  Divide :: Function fun '([RealType,RealType],RealType)
  Abs :: NumRepr tp -> Function fun '( '[tp],tp)
  Not :: Function fun '( '[BoolType],BoolType)
  Logic :: LogicOp -> Natural n -> Function fun '(AllEq BoolType n,BoolType)
  ToReal :: Function fun '( '[IntType],RealType)
  ToInt :: Function fun '( '[RealType],IntType)
  ITE :: Repr a -> Function fun '([BoolType,a,a],a)
  BVComp :: BVCompOp -> BitWidth a -> Function fun '([BitVecType a,BitVecType a],BoolType)
  BVBin :: BVBinOp -> BitWidth a -> Function fun '([BitVecType a,BitVecType a],BitVecType a)
  BVUn :: BVUnOp -> BitWidth a -> Function fun '( '[BitVecType a],BitVecType a)
  Select :: List Repr idx -> Repr val -> Function fun '(ArrayType idx val ': idx,val)
  Store :: List Repr idx -> Repr val -> Function fun '(ArrayType idx val ': val ': idx,ArrayType idx val)
  ConstArray :: List Repr idx -> Repr val -> Function fun '( '[val],ArrayType idx val)
  Concat :: BitWidth n1 -> BitWidth n2 -> Function fun '([BitVecType n1,BitVecType n2],BitVecType (n1 TL.+ n2))
  Extract :: BitWidth bw -> BitWidth start -> BitWidth len -> Function fun '( '[BitVecType bw],BitVecType len)
  Constructor :: IsDatatype dt => Constr dt sig
              -> Function fun '(sig,DataType dt)
  Test :: IsDatatype dt => Constr dt sig -> Function fun '( '[DataType dt],BoolType)
  Field :: IsDatatype dt => Type.Field dt sig t -> Function fun '( '[DataType dt],t)
  Divisible :: Integer -> Function fun '( '[IntType],BoolType)

data AnyFunction (fun :: ([Type],Type) -> *) where
  AnyFunction :: Function fun '(arg,t) -> AnyFunction fun

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

data Expression (v :: Type -> *) (qv :: Type -> *) (fun :: ([Type],Type) -> *) (fv :: Type -> *) (lv :: Type -> *) (e :: Type -> *) (res :: Type) where
#if __GLASGOW_HASKELL__>=712
  -- | Free variable.
#endif
  Var :: v res -> Expression v qv fun fv lv e res
#if __GLASGOW_HASKELL__>=712
  -- | Quantified variable, i.e. a variable that's bound by a forall/exists quantor.
#endif
  QVar :: qv res -> Expression v qv fun fv lv e res
#if __GLASGOW_HASKELL__>=712
  -- | A function argument variable. Only used in function bodies.
#endif
  FVar :: fv res -> Expression v qv fun fv lv e res
#if __GLASGOW_HASKELL__>=712
  -- | A variable bound by a let binding.
#endif
  LVar :: lv res -> Expression v qv fun fv lv e res
#if __GLASGOW_HASKELL__>=712
  -- | Function application
#endif
  App :: Function fun '(arg,res)
      -> List e arg
      -> Expression v qv fun fv lv e res
#if __GLASGOW_HASKELL__>=712
  -- | Constant
#endif
  Const :: Value a -> Expression v qv fun fv lv e a
#if __GLASGOW_HASKELL__>=712
  -- | AsArray converts a function into an array by using the function
  --   arguments as array indices and the return type as array element.
#endif
  AsArray :: Function fun '(arg,res)
          -> Expression v qv fun fv lv e (ArrayType arg res)
#if __GLASGOW_HASKELL__>=712
  -- | Bind variables using a forall or exists quantor.
#endif
  Quantification :: Quantifier -> List qv arg -> e BoolType
                 -> Expression v qv fun fv lv e BoolType
#if __GLASGOW_HASKELL__>=712
  -- | Bind variables to expressions.
#endif
  Let :: List (LetBinding lv e) arg
      -> e res
      -> Expression v qv fun fv lv e res

instance GEq fun => Eq (Function fun sig) where
  (==) = defaultEq

class SMTOrd (t :: Type) where
  lt :: Function fun '( '[t,t],BoolType)
  le :: Function fun '( '[t,t],BoolType)
  gt :: Function fun '( '[t,t],BoolType)
  ge :: Function fun '( '[t,t],BoolType)

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
  arithFromInteger :: Integer -> Value t
  arith :: ArithOp -> Natural n -> Function fun '(AllEq t n,t)
  plus :: Natural n -> Function fun '(AllEq t n,t)
  minus :: Natural n -> Function fun '(AllEq t n,t)
  mult :: Natural n -> Function fun '(AllEq t n,t)
  abs' :: Function fun '( '[t],t)

instance SMTArith IntType where
  arithFromInteger n = IntValue n
  arith = Arith NumInt
  plus = Arith NumInt Plus
  minus = Arith NumInt Minus
  mult = Arith NumInt Mult
  abs' = Abs NumInt

instance SMTArith RealType where
  arithFromInteger n = RealValue (fromInteger n)
  arith = Arith NumReal
  plus = Arith NumReal Plus
  minus = Arith NumReal Minus
  mult = Arith NumReal Mult
  abs' = Abs NumReal

functionType :: Monad m
             => (forall arg t. fun '(arg,t) -> m (List Repr arg,Repr t))
             -> Function fun '(arg,res)
             -> m (List Repr arg,Repr res)
functionType f (Fun fun) = f fun
functionType _ (Eq tp n) = return (allEqOf tp n,BoolRepr)
functionType _ (Distinct tp n) = return (allEqOf tp n,BoolRepr)
functionType f (Map idx fun) = do
  (arg,res) <- functionType f fun
  return (liftType arg idx,ArrayRepr idx res)
functionType _ (Ord tp _) = return (numRepr tp ::: numRepr tp ::: Nil,BoolRepr)
functionType _ (Arith tp _ n) = return (allEqOf (numRepr tp) n,numRepr tp)
functionType _ (ArithIntBin _) = return (IntRepr ::: IntRepr ::: Nil,IntRepr)
functionType _ Divide = return (RealRepr ::: RealRepr ::: Nil,RealRepr)
functionType _ (Abs tp) = return (numRepr tp ::: Nil,numRepr tp)
functionType _ Not = return (BoolRepr ::: Nil,BoolRepr)
functionType _ (Logic op n) = return (allEqOf BoolRepr n,BoolRepr)
functionType _ ToReal = return (IntRepr ::: Nil,RealRepr)
functionType _ ToInt = return (RealRepr ::: Nil,IntRepr)
functionType _ (ITE tp) = return (BoolRepr ::: tp ::: tp ::: Nil,tp)
functionType _ (BVComp _ n) = return (BitVecRepr n ::: BitVecRepr n ::: Nil,BoolRepr)
functionType _ (BVBin _ n) = return (BitVecRepr n ::: BitVecRepr n ::: Nil,BitVecRepr n)
functionType _ (BVUn _ n) = return (BitVecRepr n ::: Nil,BitVecRepr n)
functionType _ (Select idx el) = return (ArrayRepr idx el ::: idx,el)
functionType _ (Store idx el) = return (ArrayRepr idx el ::: el ::: idx,ArrayRepr idx el)
functionType _ (ConstArray idx el) = return (el ::: Nil,ArrayRepr idx el)
functionType _ (Concat bw1 bw2) = return (BitVecRepr bw1 ::: BitVecRepr bw2 ::: Nil,
                                          BitVecRepr (bwAdd bw1 bw2))
functionType _ (Extract bw start len) = return (BitVecRepr bw ::: Nil,BitVecRepr len)
functionType _ (Constructor con) = return (constrSig con,DataRepr (constrDatatype con))
functionType _ (Test con) = return (DataRepr (constrDatatype con) ::: Nil,BoolRepr)
functionType _ (Field field)
  = return (DataRepr (constrDatatype $ fieldConstr field) ::: Nil,fieldType field)
functionType _ (Divisible _) = return (IntRepr ::: Nil,BoolRepr)

expressionType :: (Monad m,Functor m)
               => (forall t. v t -> m (Repr t))
               -> (forall t. qv t -> m (Repr t))
               -> (forall arg t. fun '(arg,t) -> m (List Repr arg,Repr t))
               -> (forall t. fv t -> m (Repr t))
               -> (forall t. lv t -> m (Repr t))
               -> (forall t. e t -> m (Repr t))
               -> Expression v qv fun fv lv e res
               -> m (Repr res)
expressionType f _ _ _ _ _ (Var v) = f v
expressionType _ f _ _ _ _ (QVar v) = f v
expressionType _ _ _ f _ _ (FVar v) = f v
expressionType _ _ _ _ f _ (LVar v) = f v
expressionType _ _ f _ _ _ (App fun arg) = fmap snd $ functionType f fun
expressionType _ _ _ _ _ _ (Const v) = return $ valueType v
expressionType _ _ f _ _ _ (AsArray fun) = do
  (arg,res) <- functionType f fun
  return $ ArrayRepr arg res
expressionType _ _ _ _ _ _ (Quantification _ _ _) = return BoolRepr
expressionType _ _ _ _ _ f (Let _ body) = f body

mapExpr :: (Functor m,Monad m)
        => (forall t. v1 t -> m (v2 t)) -- ^ How to translate variables
        -> (forall t. qv1 t -> m (qv2 t)) -- ^ How to translate quantified variables
        -> (forall arg t. fun1 '(arg,t) -> m (fun2 '(arg,t))) -- ^ How to translate functions
        -> (forall t. fv1 t -> m (fv2 t)) -- ^ How to translate function variables
        -> (forall t. lv1 t -> m (lv2 t)) -- ^ How to translate let variables
        -> (forall t. e1 t -> m (e2 t)) -- ^ How to translate sub-expressions
        -> Expression v1 qv1 fun1 fv1 lv1 e1 r -- ^ The expression to translate
        -> m (Expression v2 qv2 fun2 fv2 lv2 e2 r)
mapExpr f _ _ _ _ _ (Var v) = fmap Var (f v)
mapExpr _ f _ _ _ _ (QVar v) = fmap QVar (f v)
mapExpr _ _ _ f _ _ (FVar v) = fmap FVar (f v)
mapExpr _ _ _ _ f _ (LVar v) = fmap LVar (f v)
mapExpr _ _ f _ _ i (App fun args) = do
  fun' <- mapFunction f fun
  args' <- List.mapM i args
  return (App fun' args')
mapExpr _ _ _ _ _ _ (Const val) = return (Const val)
mapExpr _ _ f _ _ _ (AsArray fun) = fmap AsArray (mapFunction f fun)
mapExpr _ f _ _ _ g (Quantification q args body) = do
  args' <- List.mapM f args
  body' <- g body
  return (Quantification q args' body')
mapExpr _ _ _ _ f g (Let args body) = do
  args' <- List.mapM (\bind -> do
                         nv <- f (letVar bind)
                         nexpr <- g (letExpr bind)
                         return $ LetBinding nv nexpr
                     ) args
  body' <- g body
  return (Let args' body')

mapFunction :: (Functor m,Monad m)
            => (forall arg t. fun1 '(arg,t) -> m (fun2 '(arg,t)))
            -> Function fun1 '(arg,res)
            -> m (Function fun2 '(arg,res))
mapFunction f (Fun x) = fmap Fun (f x)
mapFunction _ (Eq tp n) = return (Eq tp n)
mapFunction _ (Distinct tp n) = return (Distinct tp n)
mapFunction f (Map idx x) = do
  x' <- mapFunction f x
  return (Map idx x')
mapFunction _ (Ord tp op) = return (Ord tp op)
mapFunction _ (Arith tp op n) = return (Arith tp op n)
mapFunction _ (ArithIntBin op) = return (ArithIntBin op)
mapFunction _ Divide = return Divide
mapFunction _ (Abs tp) = return (Abs tp)
mapFunction _ Not = return Not
mapFunction _ (Logic op n) = return (Logic op n)
mapFunction _ ToReal = return ToReal
mapFunction _ ToInt = return ToInt
mapFunction _ (ITE tp) = return (ITE tp)
mapFunction _ (BVComp op bw) = return (BVComp op bw)
mapFunction _ (BVBin op bw) = return (BVBin op bw)
mapFunction _ (BVUn op bw) = return (BVUn op bw)
mapFunction _ (Select idx el) = return (Select idx el)
mapFunction _ (Store idx el) = return (Store idx el)
mapFunction _ (ConstArray idx el) = return (ConstArray idx el)
mapFunction _ (Concat bw1 bw2) = return (Concat bw1 bw2)
mapFunction _ (Extract bw start len) = return (Extract bw start len)
mapFunction _ (Constructor con) = return (Constructor con)
mapFunction _ (Test con) = return (Test con)
mapFunction _ (Field x) = return (Field x)
mapFunction _ (Divisible x) = return (Divisible x)

instance (GShow v,GShow qv,GShow fun,GShow fv,GShow lv,GShow e)
         => Show (Expression v qv fun fv lv e r) where
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

instance (GShow v,GShow qv,GShow fun,GShow fv,GShow lv,GShow e)
         => GShow (Expression v qv fun fv lv e) where
  gshowsPrec = showsPrec

instance (GShow fun)
         => Show (Function fun sig) where
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
                                  showString (constrName con)
  showsPrec p (Test con) = showParen (p>10) $
                           showString "Test " .
                           showString (constrName con)
  showsPrec p (Field x) = showParen (p>10) $
                          showString "Field " .
                          showString (fieldName x)
  showsPrec p (Divisible x) = showParen (p>10) $
                              showString "Divisible " .
                              showsPrec 11 x

data RenderMode = SMTRendering deriving (Eq,Ord,Show)

renderExprDefault :: (GetType qv,GShow v,GShow qv,GShow fun,GShow fv,GShow lv,GShow e)
                  => RenderMode
                  -> Expression v qv fun fv lv e tp
                  -> ShowS
renderExprDefault m
  = renderExpr m (gshowsPrec 11) (gshowsPrec 11) (gshowsPrec 11)
    (gshowsPrec 11) (gshowsPrec 11) (gshowsPrec 11)

renderExpr :: (GetType qv) => RenderMode
           -> (forall tp. v tp -> ShowS)
           -> (forall tp. qv tp -> ShowS)
           -> (forall arg res. fun '(arg,res) -> ShowS)
           -> (forall tp. fv tp -> ShowS)
           -> (forall tp. lv tp -> ShowS)
           -> (forall tp. e tp -> ShowS)
           -> Expression v qv fun fv lv e tp
           -> ShowS
renderExpr _ f _ _ _ _ _ (Var x) = f x
renderExpr _ _ f _ _ _ _ (QVar x) = f x
renderExpr _ _ _ _ f _ _ (FVar x) = f x
renderExpr _ _ _ _ _ f _ (LVar x) = f x
renderExpr SMTRendering _ _ f _ _ i (App fun args)
  = showChar '(' .
    renderFunction SMTRendering f fun .
    renderArgs i args .
    showChar ')'
  where
    renderArgs :: (forall tp. e tp -> ShowS) -> List e tps -> ShowS
    renderArgs f Nil = id
    renderArgs f (x ::: xs) = showChar ' ' . f x . renderArgs f xs
renderExpr m _ _ _ _ _ _ (Const val) = renderValue m val
renderExpr SMTRendering _ _ f _ _ _ (AsArray fun)
  = showString "(_ as-array " .
    renderFunction SMTRendering f fun .
    showChar ')'
renderExpr SMTRendering _ f _ _ _ g (Quantification q args body)
  = showChar '(' .
    showString (case q of
                   Forall -> "forall"
                   Exists -> "exists") .
    showString " (" . renderArgs f args . showString ") " . g body . showChar ')'
  where
    renderArgs :: GetType qv => (forall tp. qv tp -> ShowS)
               -> List qv tps -> ShowS
    renderArgs _ Nil = id
    renderArgs f (x ::: xs) = showChar '(' .
                              f x . showChar ' ' .
                              renderType SMTRendering (getType x) .
                              showChar ')' .
                              (case xs of
                                  Nil -> id
                                  _ -> showChar ' ' . renderArgs f xs)
renderExpr SMTRendering _ _ _ _ f g (Let args body)
  = showString "(let (" . renderArgs f g args . showString ") " . g body . showChar ')'
  where
    renderArgs :: (forall tp. lv tp -> ShowS) -> (forall tp. e tp -> ShowS)
               -> List (LetBinding lv e) args
               -> ShowS
    renderArgs _ _ Nil = id
    renderArgs f g (x ::: xs)
      = showChar '(' .
        f (letVar x) . showChar ' ' .
        g (letExpr x) . showChar ')' .
        (case xs of
            Nil -> id
            _ -> showChar ' ' . renderArgs f g xs)

renderValue :: RenderMode -> Value tp -> ShowS
renderValue SMTRendering (BoolValue v) = if v then showString "true" else showString "false"
renderValue SMTRendering (IntValue v)
  = if v>=0 then showsPrec 0 v
    else showString "(- " .
         showsPrec 0 (negate v) .
         showChar ')'
renderValue SMTRendering (RealValue v)
  = showString "(/ " . n . showChar ' ' . d . showChar ')'
  where
    n = if numerator v >= 0
        then showsPrec 0 (numerator v)
        else showString "(- " . showsPrec 0 (negate $ numerator v) . showChar ')'
    d = showsPrec 0 (denominator v)
renderValue SMTRendering (BitVecValue n bw)
  = showString "(_ bv" .
    showsPrec 0 n .
    showChar ' ' .
    showsPrec 0 (bwSize bw) .
    showChar ')'
renderValue SMTRendering (ConstrValue con Nil) = showString (constrName con)
renderValue SMTRendering (ConstrValue con xs)
  = showChar '(' . showString (constrName con) . renderValues xs . showChar ')'
  where
    renderValues :: List Value arg -> ShowS
    renderValues Nil = id
    renderValues (x ::: xs) = showChar ' ' . renderValue SMTRendering x . renderValues xs

renderFunction :: RenderMode
               -> (forall arg res. fun '(arg,res) -> ShowS)
               -> Function fun '(arg,res)
               -> ShowS
renderFunction _ f (Fun x) = f x
renderFunction SMTRendering _ (Eq _ _) = showChar '='
renderFunction SMTRendering _ (Distinct _ _) = showString "distinct"
renderFunction SMTRendering f (Map _ fun)
  = showString "(map " .
    renderFunction SMTRendering f fun .
    showChar ')'
renderFunction SMTRendering _ (Ord _ Ge) = showString ">="
renderFunction SMTRendering _ (Ord _ Gt) = showChar '>'
renderFunction SMTRendering _ (Ord _ Le) = showString "<="
renderFunction SMTRendering _ (Ord _ Lt) = showString "<"
renderFunction SMTRendering _ (Arith _ Plus _) = showChar '+'
renderFunction SMTRendering _ (Arith _ Mult _) = showChar '*'
renderFunction SMTRendering _ (Arith _ Minus _) = showChar '-'
renderFunction SMTRendering _ (ArithIntBin Div) = showString "div"
renderFunction SMTRendering _ (ArithIntBin Mod) = showString "mod"
renderFunction SMTRendering _ (ArithIntBin Rem) = showString "rem"
renderFunction SMTRendering _ Divide = showChar '/'
renderFunction SMTRendering _ (Abs _) = showString "abs"
renderFunction SMTRendering _ Not = showString "not"
renderFunction SMTRendering _ (Logic And _) = showString "and"
renderFunction SMTRendering _ (Logic Or _) = showString "or"
renderFunction SMTRendering _ (Logic XOr _) = showString "xor"
renderFunction SMTRendering _ (Logic Implies _) = showString "=>"
renderFunction SMTRendering _ ToReal = showString "to_real"
renderFunction SMTRendering _ ToInt = showString "to_int"
renderFunction SMTRendering _ (ITE _) = showString "ite"
renderFunction SMTRendering _ (BVComp op _) = showString $ case op of
  BVULE -> "bvule"
  BVULT -> "bvult"
  BVUGE -> "bvuge"
  BVUGT -> "bvugt"
  BVSLE -> "bvsle"
  BVSLT -> "bvslt"
  BVSGE -> "bvsge"
  BVSGT -> "bvsgt"
renderFunction SMTRendering _ (BVBin op _) = showString $ case op of
  BVAdd -> "bvadd"
  BVSub -> "bvsub"
  BVMul -> "bvmul"
  BVURem -> "bvurem"
  BVSRem -> "bvsrem"
  BVUDiv -> "bvudiv"
  BVSDiv -> "bvsdiv"
  BVSHL -> "bvshl"
  BVLSHR -> "bvshr"
  BVASHR -> "bvashr"
  BVXor -> "bvxor"
  BVAnd -> "bvand"
  BVOr -> "bvor"
renderFunction SMTRendering _ (BVUn op _) = showString $ case op of
  BVNot -> "bvnot"
  BVNeg -> "bvneg"
renderFunction SMTRendering _ (Select _ _) = showString "select"
renderFunction SMTRendering _ (Store _ _) = showString "store"
renderFunction SMTRendering _ (ConstArray idx el)
  = showString "(as const " .
    renderType SMTRendering (ArrayRepr idx el) .
    showChar ')'
renderFunction SMTRendering _ (Concat _ _) = showString "concat"
renderFunction SMTRendering _ (Extract _ start len)
  = showString "(_ extract " .
    showString (show $ start'+len'-1) .
    showChar ' ' .
    showString (show start') .
    showChar ')'
  where
    start' = bwSize start
    len' = bwSize len
renderFunction SMTRendering _ (Constructor con) = showString (constrName con)
renderFunction SMTRendering _ (Test con) = showString "is-" . showString (constrName con)
renderFunction SMTRendering _ (Field field) = showString (fieldName field)
renderFunction SMTRendering _ (Divisible n) = showString "(_ divisible " .
  showsPrec 10 n .
  showChar ')'

renderType :: RenderMode -> Repr tp -> ShowS
renderType SMTRendering BoolRepr = showString "Bool"
renderType SMTRendering IntRepr = showString "Int"
renderType SMTRendering RealRepr = showString "Real"
renderType SMTRendering (BitVecRepr bw) = showString "(BitVec " .
                                          showString (show $ bwSize bw) .
                                          showChar ')'
renderType SMTRendering (ArrayRepr idx el) = showString "(Array (" .
                                             renderTypes idx .
                                             showString ") " .
                                             renderType SMTRendering el .
                                             showChar ')'
  where
    renderTypes :: List Repr tps -> ShowS
    renderTypes Nil = id
    renderTypes (tp ::: Nil) = renderType SMTRendering tp
    renderTypes (tp ::: tps) = renderType SMTRendering tp .
                               showChar ' ' .
                               renderTypes tps
renderType _ (DataRepr dt) = showString (datatypeName dt)

instance GShow fun => GShow (Function fun) where
  gshowsPrec = showsPrec

instance (GEq v,GEq e) => GEq (LetBinding v e) where
  geq (LetBinding v1 e1) (LetBinding v2 e2) = do
    Refl <- geq v1 v2
    geq e1 e2

instance (GCompare v,GCompare e) => GCompare (LetBinding v e) where
  gcompare (LetBinding v1 e1) (LetBinding v2 e2) = case gcompare v1 v2 of
    GEQ -> gcompare e1 e2
    r -> r

instance (GEq v,GEq qv,GEq fun,GEq fv,GEq lv,GEq e)
         => GEq (Expression v qv fun fv lv e) where
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

instance (GEq v,GEq qv,GEq fun,GEq fv,GEq lv,GEq e)
         => Eq (Expression v qv fun fv lv e t) where
  (==) = defaultEq

instance (GCompare v,GCompare qv,GCompare fun,GCompare fv,GCompare lv,GCompare e)
         => GCompare (Expression v qv fun fv lv e) where
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

instance (GCompare v,GCompare qv,GCompare fun,GCompare fv,GCompare lv,GCompare e)
         => Ord (Expression v qv fun fv lv e t) where
  compare = defaultCompare

instance GEq fun => GEq (Function fun) where
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
  geq (Constructor (c1 :: Constr dt1 sig1)) (Constructor (c2 :: Constr dt2 sig2)) = do
    Refl <- eqT :: Maybe (Datatype dt1 :~: Datatype dt2)
    Refl <- geq c1 c2
    return Refl
  geq (Test c1) (Test c2) = do
    Refl <- constrEq c1 c2
    return Refl
  geq (Field f1) (Field f2) = do
    Refl <- fieldEq f1 f2
    return Refl
  geq (Divisible n1) (Divisible n2) = if n1==n2 then Just Refl else Nothing
  geq _ _ = Nothing

instance GCompare fun => GCompare (Function fun) where
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
  gcompare (Constructor c1) (Constructor c2) = case constrCompare c1 c2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Constructor _) _ = GLT
  gcompare _ (Constructor _) = GGT
  gcompare (Test c1) (Test c2) = case constrCompare c1 c2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Test _) _ = GLT
  gcompare _ (Test _) = GGT
  gcompare (Field f1) (Field f2) = case fieldCompare f1 f2 of
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

instance (GetType v,GetType qv,GetFunType fun,GetType fv,GetType lv,GetType e)
         => GetType (Expression v qv fun fv lv e) where
  getType = runIdentity . expressionType
            (return.getType) (return.getType) (return.getFunType)
            (return.getType) (return.getType) (return.getType)

instance (GetFunType fun)
         => GetFunType (Function fun) where
  getFunType = runIdentity . functionType (return.getFunType)
