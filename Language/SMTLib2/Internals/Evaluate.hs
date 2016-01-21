module Language.SMTLib2.Internals.Evaluate where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.GADT.Compare
import Data.List (genericLength)
import Data.Bits
import Data.Typeable
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Functor.Identity

data EvalResult fun con field res where
  ValueResult :: Value con res -> EvalResult fun con field res
  ArrayResult :: ArrayModel fun con field idx el
              -> EvalResult fun con field (ArrayType idx el)

data ArrayModel fun con field idx el where
  ArrayConst :: EvalResult fun con field el
             -> List Repr idx
             -> ArrayModel fun con field idx el
  ArrayFun :: Function fun con field '(idx,res)
           -> ArrayModel fun con field idx res
  ArrayMap :: Function fun con field '(arg,res)
           -> List (ArrayModel fun con field idx) arg
           -> List Repr idx
           -> ArrayModel fun con field idx res
  ArrayStore :: List (EvalResult fun con field) idx
             -> EvalResult fun con field el
             -> ArrayModel fun con field idx el
             -> ArrayModel fun con field idx el

type FunctionEval m fun con field
  = forall tps r. fun '(tps,r)
    -> List (EvalResult fun con field) tps
    -> m (EvalResult fun con field r)

type FieldEval m fun con field
  = forall dt args tp. (IsDatatype dt)
    => field '(dt,tp)
    -> con '(args,dt)
    -> List (Value con) args
    -> m (EvalResult fun con field tp)

evalResultType :: (GetFunType fun,GetConType con,GetFieldType field)
               => EvalResult fun con field res -> Repr res
evalResultType (ValueResult val) = valueType val
evalResultType (ArrayResult mdl) = let (idx,el) = arrayModelType mdl
                                   in ArrayRepr idx el

arrayModelType :: (GetFunType fun,GetConType con,GetFieldType field)
               => ArrayModel fun con field idx res -> (List Repr idx,Repr res)
arrayModelType (ArrayConst res idx) = (idx,evalResultType res)
arrayModelType (ArrayFun fun) = getFunType fun
arrayModelType (ArrayMap fun args idx)
  = let (farg,ftp) = getFunType fun
    in (idx,ftp)
arrayModelType (ArrayStore idx el mdl)
  = (runIdentity $ List.mapM (return.evalResultType) idx,evalResultType el)

evaluateArray :: (Monad m,Typeable con,GCompare con,
                  GetFunType fun,GetConType con,GetFieldType field)
              => FunctionEval m fun con field
              -> FieldEval m fun con field
              -> ArrayModel fun con field idx el
              -> List (EvalResult fun con field) idx
              -> m (EvalResult fun con field el)
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
typeNumElements (BitVecRepr sz) = Just (2^(naturalToInteger sz))
typeNumElements (ArrayRepr idx el) = do
  ridx <- List.toList typeNumElements idx
  rel <- typeNumElements el
  return (product (rel:ridx))
typeNumElements (DataRepr dt) = error "typeNumElements not implemented for datatypes"

evalResultEq :: (Monad m,Typeable con,GCompare con,
                 GetFunType fun,GetConType con,GetFieldType field)
             => FunctionEval m fun con field
             -> FieldEval m fun con field
             -> EvalResult fun con field res
             -> EvalResult fun con field res
             -> m Bool
evalResultEq _ _ (ValueResult v1) (ValueResult v2) = return (v1 == v2)
evalResultEq ev evf (ArrayResult m1) (ArrayResult m2)
  = arrayModelEq ev evf m1 m2 []

arrayModelEq :: (Monad m,Typeable con,GCompare con,
                 GetFunType fun,GetConType con,GetFieldType field)
             => FunctionEval m fun con field
             -> FieldEval m fun con field
             -> ArrayModel fun con field idx t
             -> ArrayModel fun con field idx t
             -> [List (EvalResult fun con field) idx]
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
arrayModelEq ev evf (ArrayStore (idx::List (EvalResult fun con field) idx) el mdl) oth ign = do
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

evaluateExpr :: (Monad m,Typeable con,GCompare con,GCompare lv,
                 GetFunType fun,GetConType con,GetFieldType field)
             => (forall t. v t -> m (EvalResult fun con field t))
             -> (forall t. qv t -> m (EvalResult fun con field t))
             -> (forall t. fv t -> m (EvalResult fun con field t))
             -> FunctionEval m fun con field
             -> FieldEval m fun con field
             -> (forall arg. Quantifier
                 -> List qv arg
                 -> e BoolType
                 -> m (EvalResult fun con field BoolType))
             -> DMap lv (EvalResult fun con field)
             -> (forall t. DMap lv (EvalResult fun con field) -> e t -> m (EvalResult fun con field t))
             -> Expression v qv fun con field fv lv e res
             -> m (EvalResult fun con field res)
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

evaluateFun :: forall m fun con field arg res.
            (Monad m,Typeable con,GCompare con,
             GetFunType fun,GetConType con,GetFieldType field)
            => FunctionEval m fun con field
            -> FieldEval m fun con field
            -> Function fun con field '(arg,res)
            -> List (EvalResult fun con field) arg
            -> m (EvalResult fun con field res)
evaluateFun ev _ (Fun f) arg = ev f arg
evaluateFun ev evf (Eq tp n) args = isEq n tp args >>=
                                    return . ValueResult . BoolValue
  where
    isEq :: Natural n -> Repr tp -> List (EvalResult fun con field) (AllEq tp n) -> m Bool
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
    isDistinct :: Natural n -> Repr tp -> List (EvalResult fun con field) (AllEq tp n) -> m Bool
    isDistinct Zero _ Nil = return True
    isDistinct (Succ Zero) _ (_ ::: Nil) = return True
    isDistinct (Succ n) tp (x ::: xs) = do
      neq <- isNeq n tp x xs
      if neq
        then isDistinct n tp xs
        else return False
    isNeq :: Natural n -> Repr tp -> EvalResult fun con field tp
          -> List (EvalResult fun con field) (AllEq tp n) -> m Bool
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
    (allEqToList n args :: [EvalResult fun con field IntType])
  where
    eval Plus xs = sum xs
    eval Mult xs = product xs
    eval Minus [] = 0
    eval Minus [x] = -x
    eval Minus (x:xs) = x-sum xs
evaluateFun _ _ (Arith NumReal op n) args
  = return $ ValueResult $ RealValue $
    eval op $ fmap (\(ValueResult (RealValue v)) -> v)
    (allEqToList n args :: [EvalResult fun con field RealType])
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
    (allEqToList n args :: [EvalResult fun con field BoolType])
  where
    eval And = and
    eval Or = or
    eval XOr = foldl1 (\x y -> if x then not y else y)
    eval Implies = impl
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
    bw = naturalToInteger nx
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
    bw = naturalToInteger nx
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
    bw = naturalToInteger nx
    comp BVNot = xor (2^bw-1) x
    comp BVNeg = 2^bw-x
evaluateFun ev evf (Select _ _) ((ArrayResult mdl) ::: idx)
  = evaluateArray ev evf mdl idx
evaluateFun _ _ (Store _ _) ((ArrayResult mdl) ::: el ::: idx)
  = return $ ArrayResult (ArrayStore idx el mdl)
evaluateFun _ _ (ConstArray idx _) (val ::: Nil)
  = return $ ArrayResult (ArrayConst val idx)
evaluateFun _ _ (Concat _ _) ((ValueResult (BitVecValue x nx)) ::: (ValueResult (BitVecValue y ny)) ::: Nil)
  = return $ ValueResult $ BitVecValue (x*(2^bw)+y) (naturalAdd nx ny)
  where
    bw = naturalToInteger nx
evaluateFun _ _ (Extract bw start len) ((ValueResult (BitVecValue x nx)) ::: Nil)
  = return $ ValueResult $ BitVecValue (x `div` (2^(naturalToInteger start))) len
evaluateFun _ _ (Constructor con) args = do
  rargs <- List.mapM (\(ValueResult v) -> return v) args
  return $ ValueResult $ ConstrValue con rargs
evaluateFun _ _ (Test con) ((ValueResult (ConstrValue con' _)) ::: Nil)
  = return $ ValueResult $ BoolValue $ case geq con con' of
  Just Refl -> True
  Nothing -> False
evaluateFun _ ev (Field f) ((ValueResult (ConstrValue con args)) ::: Nil)
  = ev f con args
evaluateFun _ _ (Divisible n) ((ValueResult (IntValue i)) ::: Nil)
  = return $ ValueResult $ BoolValue $ i `mod` n == 0
