module Language.SMTLib2.Internals.Evaluate where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Field)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.GADT.Compare
import Data.GADT.Show
import Data.List (genericLength)
import Data.Bits
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Functor.Identity

data EvalResult fun res where
  ValueResult :: Value res -> EvalResult fun res
  ArrayResult :: ArrayModel fun idx el
              -> EvalResult fun (ArrayType idx el)

data ArrayModel fun idx el where
  ArrayConst :: EvalResult fun el
             -> List Repr idx
             -> ArrayModel fun idx el
  ArrayFun :: Function fun '(idx,res)
           -> ArrayModel fun idx res
  ArrayMap :: Function fun '(arg,res)
           -> List (ArrayModel fun idx) arg
           -> List Repr idx
           -> ArrayModel fun idx res
  ArrayStore :: List (EvalResult fun) idx
             -> EvalResult fun el
             -> ArrayModel fun idx el
             -> ArrayModel fun idx el

type FunctionEval m fun
  = forall tps r. fun '(tps,r)
    -> List (EvalResult fun) tps
    -> m (EvalResult fun r)

type FieldEval m fun
  = forall dt par args tp. (IsDatatype dt)
    => List Repr par
    -> Type.Field dt tp
    -> List Value args
    -> m (EvalResult fun (CType tp par))

evalResultType :: (GetFunType fun)
               => EvalResult fun res -> Repr res
evalResultType (ValueResult val) = valueType val
evalResultType (ArrayResult mdl) = let (idx,el) = arrayModelType mdl
                                   in ArrayRepr idx el

arrayModelType :: (GetFunType fun)
               => ArrayModel fun idx res -> (List Repr idx,Repr res)
arrayModelType (ArrayConst res idx) = (idx,evalResultType res)
arrayModelType (ArrayFun fun) = getFunType fun
arrayModelType (ArrayMap fun args idx)
  = let (farg,ftp) = getFunType fun
    in (idx,ftp)
arrayModelType (ArrayStore idx el mdl)
  = (runIdentity $ List.mapM (return.evalResultType) idx,evalResultType el)

evaluateArray :: (Monad m,GetFunType fun)
              => FunctionEval m fun
              -> FieldEval m fun
              -> ArrayModel fun idx el
              -> List (EvalResult fun) idx
              -> m (EvalResult fun el)
evaluateArray _ _ (ArrayConst c _) _ = return c
evaluateArray f g (ArrayFun fun) arg = evaluateFun f g fun arg
evaluateArray f g (ArrayMap fun args _) arg = do
  rargs <- List.mapM (\arr -> evaluateArray f g arr arg) args
  evaluateFun f g fun rargs
evaluateArray f g (ArrayStore idx val mdl) arg = do
  eq <- List.zipToListM (evalResultEq f g) idx arg
  if and eq
    then return val
    else evaluateArray f g mdl arg

typeNumElements :: Repr t -> Maybe Integer
typeNumElements BoolRepr = Just 2
typeNumElements IntRepr = Nothing
typeNumElements RealRepr = Nothing
typeNumElements (BitVecRepr sz) = Just (2^(bwSize sz))
typeNumElements (ArrayRepr idx el) = do
  ridx <- List.toList typeNumElements idx
  rel <- typeNumElements el
  return (product (rel:ridx))
typeNumElements (DataRepr _ _) = error "typeNumElements not implemented for datatypes"

evalResultEq :: (Monad m,GetFunType fun)
             => FunctionEval m fun
             -> FieldEval m fun
             -> EvalResult fun res
             -> EvalResult fun res
             -> m Bool
evalResultEq _ _ (ValueResult v1) (ValueResult v2) = return (v1 == v2)
evalResultEq ev evf (ArrayResult m1) (ArrayResult m2)
  = arrayModelEq ev evf m1 m2 []

arrayModelEq :: (Monad m,GetFunType fun)
             => FunctionEval m fun
             -> FieldEval m fun
             -> ArrayModel fun idx t
             -> ArrayModel fun idx t
             -> [List (EvalResult fun) idx]
             -> m Bool
arrayModelEq _ _ (ArrayFun _) _ _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq _ _ _ (ArrayFun _) _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq _ _ (ArrayMap _ _ _) _ _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq _ _ _ (ArrayMap _ _ _) _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq ev evf (ArrayConst v1 _) (ArrayConst v2 _) _
  = evalResultEq ev evf v1 v2
arrayModelEq ev evf (ArrayStore (idx::List (EvalResult fun) idx) el mdl) oth ign = do
  isIgn <- isIgnored idx ign
  if isIgn
    then arrayModelEq ev evf mdl oth ign
    else do
    othEl <- evaluateArray ev evf oth idx
    othIsEq <- evalResultEq ev evf el othEl
    if othIsEq
      then case List.toList typeNumElements (runIdentity $ List.mapM (return.evalResultType) idx) of
      Just szs -> if genericLength szs==product szs
                  then return True -- All indices are ignored
                  else arrayModelEq ev evf mdl oth (idx:ign)
      else return False
  where
    isIgnored _ [] = return False
    isIgnored idx (i:is) = do
      same <- List.zipToListM (evalResultEq ev evf) idx i
      if and same
        then return True
        else isIgnored idx is
arrayModelEq ev evf m1 m2 ign = arrayModelEq ev evf m2 m1 ign

evaluateExpr :: (Monad m,GCompare lv,GetFunType fun)
             => (forall t. v t -> m (EvalResult fun t))
             -> (forall t. qv t -> m (EvalResult fun t))
             -> (forall t. fv t -> m (EvalResult fun t))
             -> FunctionEval m fun
             -> FieldEval m fun
             -> (forall arg. Quantifier
                 -> List qv arg
                 -> e BoolType
                 -> m (EvalResult fun BoolType))
             -> DMap lv (EvalResult fun)
             -> (forall t. DMap lv (EvalResult fun) -> e t -> m (EvalResult fun t))
             -> Expression v qv fun fv lv e res
             -> m (EvalResult fun res)
evaluateExpr fv _ _ _ _ _ _ _ (Var v) = fv v
evaluateExpr _ fqv _ _ _ _ _ _ (QVar v) = fqv v
evaluateExpr _ _ ffv _ _ _ _ _ (FVar v) = ffv v
evaluateExpr _ _ _ _ _ _ binds _ (LVar v) = case DMap.lookup v binds of
  Just r -> return r
evaluateExpr _ _ _ _ _ _ _ _ (Const c) = return (ValueResult c)
evaluateExpr _ _ _ _ _ _ _ _ (AsArray fun)
  = return (ArrayResult (ArrayFun fun))
evaluateExpr _ _ _ _ _ evq _ _ (Quantification q arg body)
  = evq q arg body
evaluateExpr _ _ _ _ _ _ binds f (Let arg body) = do
  nbinds <- List.foldM (\cbinds x -> do
                           rx <- f cbinds (letExpr x)
                           return $ DMap.insert (letVar x) rx cbinds
                       ) binds arg
  f nbinds body
evaluateExpr _ _ _ evf evr _ binds f (App fun args) = do
  rargs <- List.mapM (f binds) args
  evaluateFun evf evr fun rargs

evaluateFun :: forall m fun arg res.
            (Monad m,GetFunType fun)
            => FunctionEval m fun
            -> FieldEval m fun
            -> Function fun '(arg,res)
            -> List (EvalResult fun) arg
            -> m (EvalResult fun res)
evaluateFun ev _ (Fun f) arg = ev f arg
evaluateFun ev evf (Eq tp n) args = isEq n tp args >>=
                                    return . ValueResult . BoolValue
  where
    isEq :: Natural n -> Repr tp -> List (EvalResult fun) (AllEq tp n) -> m Bool
    isEq Zero _ Nil = return True
    isEq (Succ Zero) _ (_ ::: Nil) = return True
    isEq (Succ (Succ n)) tp (x ::: y ::: xs) = do
      eq <- evalResultEq ev evf x y
      if eq
        then isEq (Succ n) tp (y ::: xs)
        else return False
evaluateFun ev evf (Distinct tp n) args = isDistinct n tp args >>=
                                          return . ValueResult . BoolValue
  where
    isDistinct :: Natural n -> Repr tp -> List (EvalResult fun) (AllEq tp n) -> m Bool
    isDistinct Zero _ Nil = return True
    isDistinct (Succ Zero) _ (_ ::: Nil) = return True
    isDistinct (Succ n) tp (x ::: xs) = do
      neq <- isNeq n tp x xs
      if neq
        then isDistinct n tp xs
        else return False
    isNeq :: Natural n -> Repr tp -> EvalResult fun tp
          -> List (EvalResult fun) (AllEq tp n) -> m Bool
    isNeq Zero _ _ Nil = return True
    isNeq (Succ n) tp x (y ::: ys) = do
      eq <- evalResultEq ev evf x y
      if eq
        then return False
        else isNeq n tp x ys
evaluateFun _ _ (Ord NumInt op) ((ValueResult (IntValue lhs)) ::: (ValueResult (IntValue rhs)) ::: Nil)
  = return $ ValueResult $ BoolValue (cmp op lhs rhs)
  where
    cmp Ge = (>=)
    cmp Gt = (>)
    cmp Le = (<=)
    cmp Lt = (<)
evaluateFun _ _ (Ord NumReal op) ((ValueResult (RealValue lhs)) ::: (ValueResult (RealValue rhs)) ::: Nil)
  = return $ ValueResult $ BoolValue (cmp op lhs rhs)
  where
    cmp Ge = (>=)
    cmp Gt = (>)
    cmp Le = (<=)
    cmp Lt = (<)
evaluateFun _ _ (Arith NumInt op n) args
  = return $ ValueResult $ IntValue $
    eval op $ fmap (\(ValueResult (IntValue v)) -> v)
    (allEqToList n args :: [EvalResult fun IntType])
  where
    eval Plus xs = sum xs
    eval Mult xs = product xs
    eval Minus [] = 0
    eval Minus [x] = -x
    eval Minus (x:xs) = x-sum xs
evaluateFun _ _ (Arith NumReal op n) args
  = return $ ValueResult $ RealValue $
    eval op $ fmap (\(ValueResult (RealValue v)) -> v)
    (allEqToList n args :: [EvalResult fun RealType])
  where
    eval Plus xs = sum xs
    eval Mult xs = product xs
    eval Minus [] = 0
    eval Minus [x] = -x
    eval Minus (x:xs) = x-sum xs
evaluateFun _ _ (ArithIntBin op) ((ValueResult (IntValue lhs)) ::: (ValueResult (IntValue rhs)) ::: Nil)
  = return $ ValueResult $ IntValue (eval op lhs rhs)
  where
    eval Div = div
    eval Mod = mod
    eval Rem = rem
evaluateFun _ _ Divide ((ValueResult (RealValue lhs)) ::: (ValueResult (RealValue rhs)) ::: Nil)
  = return $ ValueResult $ RealValue (lhs / rhs)
evaluateFun _ _ (Abs NumInt) ((ValueResult (IntValue x)) ::: Nil)
  = return $ ValueResult $ IntValue $ abs x
evaluateFun _ _ (Abs NumReal) ((ValueResult (RealValue x)) ::: Nil)
  = return $ ValueResult $ RealValue $ abs x
evaluateFun _ _ Not ((ValueResult (BoolValue x)) ::: Nil)
  = return $ ValueResult $ BoolValue $ not x
evaluateFun _ _ (Logic op n) args
  = return $ ValueResult $ BoolValue $
    eval op $ fmap (\(ValueResult (BoolValue v)) -> v)
    (allEqToList n args :: [EvalResult fun BoolType])
  where
    eval And = and
    eval Or = or
    eval XOr = foldl1 (\x y -> if x then not y else y)
    eval Implies = impl
    eval (AtLeast n) = (>=n) . foldl (\c x -> if x then c+1 else c
                                     ) 0
    eval (AtMost n) = (<=n) . foldl (\c x -> if x then c+1 else c
                                    ) 0
    impl [x] = x
    impl (x:xs) = if x then impl xs else False
evaluateFun _ _ ToReal ((ValueResult (IntValue x)) ::: Nil)
  = return $ ValueResult $ RealValue $ fromInteger x
evaluateFun _ _ ToInt ((ValueResult (RealValue x)) ::: Nil)
  = return $ ValueResult $ IntValue $ round x
evaluateFun _ _ (ITE _) ((ValueResult (BoolValue c)) ::: x ::: y ::: Nil)
  = return $ if c then x else y
evaluateFun _ _ (BVComp op _) ((ValueResult (BitVecValue x nx)) ::: (ValueResult (BitVecValue y ny)) ::: Nil)
  = return $ ValueResult $ BoolValue $ comp op
  where
    bw = bwSize nx
    sx = if x >= 2^(bw-1) then x-2^bw else x
    sy = if y >= 2^(bw-1) then y-2^bw else y
    comp BVULE = x <= y
    comp BVULT = x < y
    comp BVUGE = x >= y
    comp BVUGT = x > y
    comp BVSLE = sx <= sy
    comp BVSLT = sx < sy
    comp BVSGE = sx >= sy
    comp BVSGT = sx > sy
evaluateFun _ _ (BVBin op _) ((ValueResult (BitVecValue x nx)) ::: (ValueResult (BitVecValue y ny)) ::: Nil)
  = return $ ValueResult $ BitVecValue (comp op) nx
  where
    bw = bwSize nx
    sx = if x >= 2^(bw-1) then x-2^bw else x
    sy = if y >= 2^(bw-1) then y-2^bw else y
    toU x = if x < 0
            then x+2^bw
            else x
    comp BVAdd = (x+y) `mod` (2^bw)
    comp BVSub = (x-y) `mod` (2^bw)
    comp BVMul = (x*y) `mod` (2^bw)
    comp BVURem = x `rem` y
    comp BVSRem = toU (sx `rem` sy)
    comp BVUDiv = x `div` y
    comp BVSDiv = toU (sx `div` sy)
    comp BVSHL = x * 2^y
    comp BVLSHR = x `div` (2^y)
    comp BVASHR = toU $ sx `div` (2^y)
    comp BVXor = xor x y
    comp BVAnd = x .&. y
    comp BVOr = x .|. y
evaluateFun _ _ (BVUn op _) ((ValueResult (BitVecValue x nx)) ::: Nil)
  = return $ ValueResult $ BitVecValue (comp op) nx
  where
    bw = bwSize nx
    comp BVNot = xor (2^bw-1) x
    comp BVNeg = 2^bw-x
evaluateFun ev evf (Select _ _) ((ArrayResult mdl) ::: idx)
  = evaluateArray ev evf mdl idx
evaluateFun _ _ (Store _ _) ((ArrayResult mdl) ::: el ::: idx)
  = return $ ArrayResult (ArrayStore idx el mdl)
evaluateFun _ _ (ConstArray idx _) (val ::: Nil)
  = return $ ArrayResult (ArrayConst val idx)
evaluateFun _ _ (Concat _ _) ((ValueResult (BitVecValue x nx)) ::: (ValueResult (BitVecValue y ny)) ::: Nil)
  = return $ ValueResult $ BitVecValue (x*(2^bw)+y) (bwAdd nx ny)
  where
    bw = bwSize nx
evaluateFun _ _ (Extract bw start len) ((ValueResult (BitVecValue x nx)) ::: Nil)
  = return $ ValueResult $ BitVecValue (x `div` (2^(bwSize start))) len
evaluateFun _ _ (Constructor dt par con) args = do
  rargs <- List.mapM (\(ValueResult v) -> return v) args
  return $ ValueResult $ DataValue (construct par con rargs)
evaluateFun _ _ (Test dt par con) ((ValueResult (ConstrValue par' con' _)) ::: Nil)
  = return $ ValueResult $ BoolValue $ case geq con con' of
  Just Refl -> True
  Nothing -> False
--evaluateFun _ ev (Field f) ((ValueResult (ConstrValue con args)) ::: Nil)
--  = ev f con args
evaluateFun _ _ (Divisible n) ((ValueResult (IntValue i)) ::: Nil)
  = return $ ValueResult $ BoolValue $ i `mod` n == 0

instance GetFunType fun => GetType (EvalResult fun) where
  getType (ValueResult v) = getType v
  getType (ArrayResult v) = let (idx,res) = getArrayModelType v
                            in ArrayRepr idx res

getArrayModelType :: GetFunType fun => ArrayModel fun idx el -> (List Repr idx,Repr el)
getArrayModelType (ArrayConst c idx) = (idx,getType c)
getArrayModelType (ArrayFun fun) = getFunType fun
getArrayModelType (ArrayMap fun args idx)
  = let (_,res) = getFunType fun
    in (idx,res)
getArrayModelType (ArrayStore idx el arr) = getArrayModelType arr

instance GShow fun => Show (EvalResult fun res) where
  showsPrec p (ValueResult v) = showsPrec p v
  showsPrec p (ArrayResult arr) = showsPrec p arr

instance GShow fun => Show (ArrayModel fun idx el) where
  showsPrec p (ArrayConst c idx)
    = showString "(array-const " .
      showsPrec 11 idx . showChar ' ' .
      showsPrec 11 c . showChar ')'
  showsPrec p (ArrayFun fun)
    = showString "(array-fun " .
      showsPrec 11 fun . showChar ')'
  showsPrec p (ArrayMap fun args idx)
    = showString "(array-map " .
      showsPrec 11 fun . showChar ' ' .
      showsPrec 11 args . showChar ')'
  showsPrec p (ArrayStore idx el mdl)
    = showString "(array-store " .
      showsPrec 11 idx . showChar ' ' .
      showsPrec 11 el . showChar ' ' .
      showsPrec 11 mdl . showChar ')'

instance GShow fun => GShow (EvalResult fun) where
  gshowsPrec = showsPrec

instance GShow fun => GShow (ArrayModel fun idx) where
  gshowsPrec = showsPrec

instance GEq fun => GEq (EvalResult fun) where
  geq (ValueResult x) (ValueResult y) = geq x y
  geq (ArrayResult mdl1) (ArrayResult mdl2) = do
    (Refl,Refl) <- geqArrayModel mdl1 mdl2
    return Refl
  geq _ _ = Nothing

instance GCompare fun => GCompare (EvalResult fun) where
  gcompare (ValueResult x) (ValueResult y) = gcompare x y
  gcompare (ValueResult _) _ = GLT
  gcompare _ (ValueResult _) = GGT
  gcompare (ArrayResult x) (ArrayResult y) = case gcompareArrayModel x y of
    (GEQ,GEQ) -> GEQ
    (GEQ,GLT) -> GLT
    (GEQ,GGT) -> GGT
    (GLT,_) -> GLT
    (GGT,_) -> GGT

geqArrayModel :: GEq fun => ArrayModel fun idx1 el1 -> ArrayModel fun idx2 el2 -> Maybe (idx1 :~: idx2,el1 :~: el2)
geqArrayModel (ArrayConst v1 idx1) (ArrayConst v2 idx2) = do
  Refl <- geq v1 v2
  Refl <- geq idx1 idx2
  return (Refl,Refl)
geqArrayModel (ArrayFun f1) (ArrayFun f2) = do
  Refl <- geq f1 f2
  return (Refl,Refl)
geqArrayModel (ArrayMap f1 arg1 idx1) (ArrayMap f2 arg2 idx2) = do
  Refl <- geq idx1 idx2
  Refl <- geq f1 f2
  _ <- zipToListM (\x y -> do
                      (Refl,Refl) <- geqArrayModel x y
                      return ()) arg1 arg2
  return (Refl,Refl)
geqArrayModel (ArrayStore idx1 el1 arr1) (ArrayStore idx2 el2 arr2) = do
  Refl <- geq idx1 idx2
  Refl <- geq el1 el2
  (Refl,Refl) <- geqArrayModel arr1 arr2
  return (Refl,Refl)
geqArrayModel _ _ = Nothing

gcompareArrayModel :: GCompare fun => ArrayModel fun idx1 el1 -> ArrayModel fun idx2 el2
                   -> (GOrdering idx1 idx2,
                       GOrdering el1 el2)
gcompareArrayModel (ArrayConst c1 idx1) (ArrayConst c2 idx2)
  = case gcompare idx1 idx2 of
  GEQ -> (GEQ,gcompare c1 c2)
  GLT -> (GLT,GLT)
  GGT -> (GGT,GGT)
gcompareArrayModel (ArrayConst _ _) _ = (GLT,GLT)
gcompareArrayModel _ (ArrayConst _ _) = (GGT,GGT)
gcompareArrayModel (ArrayFun f1) (ArrayFun f2) = case gcompare f1 f2 of
  GEQ -> (GEQ,GEQ)
  GLT -> (GLT,GLT)
  GGT -> (GGT,GGT)
gcompareArrayModel (ArrayFun _) _ = (GLT,GLT)
gcompareArrayModel _ (ArrayFun _) = (GGT,GGT)
gcompareArrayModel (ArrayMap f1 arg1 idx1) (ArrayMap f2 arg2 idx2)
  = case gcompare idx1 idx2 of
  GEQ -> (GEQ,case gcompare f1 f2 of
                GEQ -> case gcompareArrayModels arg1 arg2 of
                  GEQ -> GEQ
                  GLT -> GLT
                  GGT -> GGT
                GLT -> GLT
                GGT -> GGT)
  GLT -> (GLT,GLT)
  GGT -> (GGT,GGT)
  where
    gcompareArrayModels :: GCompare fun
                        => List (ArrayModel fun idx) arg1
                        -> List (ArrayModel fun idx) arg2
                        -> GOrdering arg1 arg2
    gcompareArrayModels Nil Nil = GEQ
    gcompareArrayModels Nil _ = GLT
    gcompareArrayModels _ Nil = GGT
    gcompareArrayModels (x:::xs) (y:::ys) = case gcompareArrayModel x y of
      (GEQ,GEQ) -> case gcompareArrayModels xs ys of
        GEQ -> GEQ
        GLT -> GLT
        GGT -> GGT
      (GEQ,GLT) -> GLT
      (GEQ,GGT) -> GGT
      (GLT,_) -> GLT
      (GGT,_) -> GGT
gcompareArrayModel (ArrayMap _ _ _) _ = (GLT,GLT)
gcompareArrayModel _ (ArrayMap _ _ _) = (GGT,GGT)
gcompareArrayModel (ArrayStore idx1 el1 mdl1) (ArrayStore idx2 el2 mdl2)
  = case gcompareArrayModel mdl1 mdl2 of
  (GEQ,GEQ) -> case gcompare idx1 idx2 of
    GEQ -> case gcompare el1 el2 of
      GEQ -> (GEQ,GEQ)
      GLT -> (GEQ,GLT)
      GGT -> (GEQ,GGT)
    GLT -> (GLT,GLT)
    GGT -> (GGT,GGT)
  r -> r
