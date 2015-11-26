module Language.SMTLib2.Internals.Evaluate where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat

import Data.GADT.Compare
import Data.List (genericLength)
import Data.Proxy
import Data.Bits
import Data.Constraint
import Data.Typeable
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap

data EvalResult fun con field res where
  ValueResult :: Value con res -> EvalResult fun con field res
  ArrayResult :: GetTypes idx
              => ArrayModel fun con field idx el
              -> EvalResult fun con field (ArrayType idx el)

data ArrayModel fun con field idx el where
  ArrayConst :: EvalResult fun con field el
             -> ArrayModel fun con field idx el
  ArrayFun :: Function fun con field '(idx,res)
           -> ArrayModel fun con field idx res
  ArrayMap :: GetTypes arg
           => Function fun con field '(arg,res)
           -> Args (ArrayModel fun con field idx) arg
           -> ArrayModel fun con field idx res
  ArrayStore :: Args (EvalResult fun con field) idx
             -> EvalResult fun con field el
             -> ArrayModel fun con field idx el
             -> ArrayModel fun con field idx el

type FunctionEval m fun con field
  = forall tps r. (GetTypes tps,GetType r)
    => fun '(tps,r)
    -> Args (EvalResult fun con field) tps
    -> m (EvalResult fun con field r)

type FieldEval m fun con field
  = forall dt args tp. (IsDatatype dt,GetTypes args,GetType tp)
    => field '(dt,tp)
    -> con '(args,dt)
    -> Args (Value con) args
    -> m (EvalResult fun con field tp)

evaluateArray :: (Monad m,Typeable con,GCompare con,GetTypes idx)
              => FunctionEval m fun con field
              -> FieldEval m fun con field
              -> ArrayModel fun con field idx el
              -> Args (EvalResult fun con field) idx
              -> m (EvalResult fun con field el)
evaluateArray _ _ (ArrayConst c) _ = return c
evaluateArray f g (ArrayFun fun) arg = evaluateFun f g fun arg
evaluateArray f g (ArrayMap fun args) arg = do
  rargs <- mapArgs (\arr -> evaluateArray f g arr arg) args
  evaluateFun f g fun rargs
evaluateArray f g (ArrayStore idx val mdl) arg = do
  eq <- argsEqM (evalResultEq f g) idx arg
  if eq
    then return val
    else evaluateArray f g mdl arg

typeNumElements :: Repr t -> Maybe Integer
typeNumElements BoolRepr = Just 2
typeNumElements IntRepr = Nothing
typeNumElements RealRepr = Nothing
typeNumElements (BitVecRepr sz) = Just (2^sz)
typeNumElements (ArrayRepr idx el) = do
  ridx <- argsToListM typeNumElements idx
  rel <- typeNumElements el
  return (product (rel:ridx))
typeNumElements (DataRepr dt) = error "typeNumElements not implemented for datatypes"

evalResultEq :: (Monad m,Typeable con,GCompare con)
             => FunctionEval m fun con field
             -> FieldEval m fun con field
             -> EvalResult fun con field res
             -> EvalResult fun con field res
             -> m Bool
evalResultEq _ _ (ValueResult v1) (ValueResult v2) = return (v1 == v2)
evalResultEq ev evf (ArrayResult m1) (ArrayResult m2)
  = arrayModelEq ev evf m1 m2 []

arrayModelEq :: (Monad m,GetTypes idx,Typeable con,GCompare con)
             => FunctionEval m fun con field
             -> FieldEval m fun con field
             -> ArrayModel fun con field idx t
             -> ArrayModel fun con field idx t
             -> [Args (EvalResult fun con field) idx]
             -> m Bool
arrayModelEq _ _ (ArrayFun _) _ _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq _ _ _ (ArrayFun _) _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq _ _ (ArrayMap _ _) _ _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq _ _ _ (ArrayMap _ _) _
  = error "Cannot decide array equality with arrays built from functions."
arrayModelEq ev evf (ArrayConst v1) (ArrayConst v2) _
  = evalResultEq ev evf v1 v2
arrayModelEq ev evf (ArrayStore (idx::Args (EvalResult fun con field) idx) el mdl) oth ign = do
  isIgn <- isIgnored idx ign
  if isIgn
    then arrayModelEq ev evf mdl oth ign
    else do
    othEl <- evaluateArray ev evf oth idx
    othIsEq <- evalResultEq ev evf el othEl
    if othIsEq
      then case argsToListM typeNumElements (getTypes :: Args Repr idx) of
      Just szs -> if genericLength szs==product szs
                  then return True -- All indices are ignored
                  else arrayModelEq ev evf mdl oth (idx:ign)
      else return False
  where
    isIgnored _ [] = return False
    isIgnored idx (i:is) = do
      same <- argsEqM (evalResultEq ev evf) idx i
      if same
        then return True
        else isIgnored idx is
arrayModelEq ev evf m1 m2 ign = arrayModelEq ev evf m2 m1 ign

evaluateExpr :: (Monad m,Typeable con,GCompare con,GCompare lv)
             => (forall t. GetType t => v t -> m (EvalResult fun con field t))
             -> (forall t. GetType t => qv t -> m (EvalResult fun con field t))
             -> (forall t. GetType t => fv t -> m (EvalResult fun con field t))
             -> FunctionEval m fun con field
             -> FieldEval m fun con field
             -> (forall arg. GetTypes arg
                 => Quantifier
                 -> Args qv arg
                 -> e BoolType
                 -> m (EvalResult fun con field BoolType))
             -> DMap lv (EvalResult fun con field)
             -> (forall t. GetType t => DMap lv (EvalResult fun con field) -> e t -> m (EvalResult fun con field t))
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
  nbinds <- foldArgs (\cbinds x -> do
                         rx <- f cbinds (letExpr x)
                         return $ DMap.insert (letVar x) rx cbinds
                     ) binds arg
  f nbinds body
evaluateExpr _ _ _ evf evr _ binds f (App fun args) = do
  rargs <- mapArgs (f binds) args
  evaluateFun evf evr fun rargs

evaluateFun :: (Monad m,GetTypes arg,Typeable con,GCompare con)
            => FunctionEval m fun con field
            -> FieldEval m fun con field
            -> Function fun con field '(arg,res)
            -> Args (EvalResult fun con field) arg
            -> m (EvalResult fun con field res)
evaluateFun ev _ (Fun f) arg = ev f arg
evaluateFun ev evf Eq args = fmap (ValueResult . BoolValue) $ isEq (allEqToList args)
  where
    isEq [] = return True
    isEq [_] = return True
    isEq (x:y:xs) = do
      eq <- evalResultEq ev evf x y
      if eq
        then isEq (y:xs)
        else return False
evaluateFun ev evf Distinct args = fmap (ValueResult . BoolValue) $ isDistinct (allEqToList args)
  where
    isDistinct [] = return True
    isDistinct [_] = return True
    isDistinct (x:xs) = do
      neq <- isNeq x xs
      if neq
        then isDistinct xs
        else return False
    isNeq x [] = return True
    isNeq x (y:ys) = do
      eq <- evalResultEq ev evf x y
      if eq
        then return False
        else isNeq x ys
evaluateFun _ _ (OrdInt op) (Arg (ValueResult (IntValue lhs)) (Arg (ValueResult (IntValue rhs)) NoArg))
  = return $ ValueResult $ BoolValue (cmp op lhs rhs)
  where
    cmp Ge = (>=)
    cmp Gt = (>)
    cmp Le = (<=)
    cmp Lt = (<)
evaluateFun _ _ (OrdReal op) (Arg (ValueResult (RealValue lhs)) (Arg (ValueResult (RealValue rhs)) NoArg))
  = return $ ValueResult $ BoolValue (cmp op lhs rhs)
  where
    cmp Ge = (>=)
    cmp Gt = (>)
    cmp Le = (<=)
    cmp Lt = (<)
evaluateFun _ _ (ArithInt op) args
  = return $ ValueResult $ IntValue (eval op $ fmap (\(ValueResult (IntValue v)) -> v) (allEqToList args))
  where
    eval Plus xs = sum xs
    eval Mult xs = product xs
    eval Minus [] = 0
    eval Minus [x] = -x
    eval Minus (x:xs) = x-sum xs
evaluateFun _ _ (ArithReal op) args
  = return $ ValueResult $ RealValue (eval op $ fmap (\(ValueResult (RealValue v)) -> v) (allEqToList args))
  where
    eval Plus xs = sum xs
    eval Mult xs = product xs
    eval Minus [] = 0
    eval Minus [x] = -x
    eval Minus (x:xs) = x-sum xs
evaluateFun _ _ (ArithIntBin op) (Arg (ValueResult (IntValue lhs)) (Arg (ValueResult (IntValue rhs)) NoArg))
  = return $ ValueResult $ IntValue (eval op lhs rhs)
  where
    eval Div = div
    eval Mod = mod
    eval Rem = rem
evaluateFun _ _ Divide (Arg (ValueResult (RealValue lhs)) (Arg (ValueResult (RealValue rhs)) NoArg))
  = return $ ValueResult $ RealValue (lhs / rhs)
evaluateFun _ _ AbsInt (Arg (ValueResult (IntValue x)) NoArg)
  = return $ ValueResult $ IntValue $ abs x
evaluateFun _ _ AbsReal (Arg (ValueResult (RealValue x)) NoArg)
  = return $ ValueResult $ RealValue $ abs x
evaluateFun _ _ Not (Arg (ValueResult (BoolValue x)) NoArg)
  = return $ ValueResult $ BoolValue $ not x
evaluateFun _ _ (Logic op) args
  = return $ ValueResult $ BoolValue $
    eval op $ fmap (\(ValueResult (BoolValue v)) -> v) (allEqToList args)
  where
    eval And = and
    eval Or = or
    eval XOr = foldl1 (\x y -> if x then not y else y)
    eval Implies = impl
    impl [x] = x
    impl (x:xs) = if x then impl xs else False
evaluateFun _ _ ToReal (Arg (ValueResult (IntValue x)) NoArg)
  = return $ ValueResult $ RealValue $ fromInteger x
evaluateFun _ _ ToInt (Arg (ValueResult (RealValue x)) NoArg)
  = return $ ValueResult $ IntValue $ round x
evaluateFun _ _ ITE (Arg (ValueResult (BoolValue c)) (Arg x (Arg y NoArg)))
  = return $ if c then x else y
evaluateFun _ _ (BVComp op) (Arg (ValueResult (BitVecValue x::Value con (BitVecType bw))) (Arg (ValueResult (BitVecValue y)) NoArg))
  = return $ ValueResult $ BoolValue $ comp op
  where
    bw = natVal (Proxy::Proxy bw)
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
evaluateFun _ _ (BVBin op) (Arg (ValueResult (BitVecValue x::Value con (BitVecType bw))) (Arg (ValueResult (BitVecValue y)) NoArg))
  = return $ ValueResult $ BitVecValue $ comp op
  where
    bw = natVal (Proxy::Proxy bw)
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
evaluateFun _ _ (BVUn op) (Arg (ValueResult (BitVecValue x::Value con (BitVecType bw))) NoArg)
  = return $ ValueResult $ BitVecValue $ comp op
  where
    bw = natVal (Proxy::Proxy bw)
    comp BVNot = xor (2^bw-1) x
    comp BVNeg = 2^bw-x
evaluateFun ev evf Select (Arg (ArrayResult mdl) idx)
  = evaluateArray ev evf mdl idx
evaluateFun _ _ Store (Arg (ArrayResult mdl) (Arg el idx))
  = return $ ArrayResult (ArrayStore idx el mdl)
evaluateFun _ _ ConstArray (Arg val NoArg)
  = return $ ArrayResult (ArrayConst val)
evaluateFun _ _ Concat (Arg (ValueResult (BitVecValue x::Value con (BitVecType bwx))) (Arg (ValueResult (BitVecValue y::Value con (BitVecType bwy))) NoArg))
  = case deriveAdd (Proxy::Proxy bwx) (Proxy::Proxy bwy) of
  Dict -> return $ ValueResult $ BitVecValue $ x*(2^bw)+y
  where
    bw = natVal (Proxy::Proxy bwy)
evaluateFun _ _ (Extract start) (Arg (ValueResult (BitVecValue x::Value con (BitVecType bw))) NoArg)
  = return $ ValueResult $ mkMod Proxy (x `div` (2^(natVal start)))
  where
    mkMod :: KnownNat res => Proxy res -> Integer -> Value con (BitVecType res)
    mkMod pr x = BitVecValue (x `mod` (2^(natVal pr)))
evaluateFun _ _ (Constructor con) args = do
  rargs <- mapArgs (\(ValueResult v) -> return v) args
  return $ ValueResult $ ConstrValue con rargs
evaluateFun _ _ (Test con) (Arg (ValueResult (ConstrValue con' _)) NoArg)
  = return $ ValueResult $ BoolValue $ case geq con con' of
  Just Refl -> True
  Nothing -> False
evaluateFun _ ev (Field f) (Arg (ValueResult (ConstrValue con args)) NoArg)
  = ev f con args
evaluateFun _ _ (Divisible n) (Arg (ValueResult (IntValue i)) NoArg)
  = return $ ValueResult $ BoolValue $ i `mod` n == 0
