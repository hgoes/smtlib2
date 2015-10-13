{- | Implements various instance declarations for 'Language.SMTLib2.SMTType',
     'Language.SMTLib2.SMTValue', etc. -}
{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,RankNTypes,TypeFamilies,GeneralizedNewtypeDeriving,DeriveDataTypeable,GADTs,FlexibleContexts,CPP,ScopedTypeVariables,TypeOperators #-}
module Language.SMTLib2.Internals.Instances where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Data.Ratio
import Data.Typeable
import Data.List (genericReplicate,zip4,zip5,zip6,genericIndex)
#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
import Data.Proxy
#endif
import Data.Fix
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable (mapM)
import Data.Foldable (foldlM)
import Text.Show
import Data.Functor.Identity
import Prelude hiding (mapM)

valueToHaskell :: DataTypeInfo
                  -> (forall t. SMTType t => [ProxyArg] -> t -> SMTAnnotation t -> r)
                  -> Maybe Sort
                  -> Value
                  -> r
valueToHaskell _ f _ (BoolValue v) = f [] v ()
valueToHaskell _ f _ (IntValue v) = f [] v ()
valueToHaskell _ f _ (RealValue v) = f [] v ()
valueToHaskell _ f (Just (Fix (BVSort { bvSortUntyped = True }))) (BVValue { bvValueWidth = w
                                                                             , bvValueValue = v })
  = f [] (BitVector v::BitVector BVUntyped) w
valueToHaskell _ f _ (BVValue { bvValueWidth = w
                                , bvValueValue = v })
  = reifyNat w (\(_::Proxy tp) -> f [] (BitVector v::BitVector (BVTyped tp)) ())
valueToHaskell dtInfo f sort (ConstrValue name args sort')
  = case Map.lookup name (constructors dtInfo) of
  Just (con,dt,struct)
    -> let sort'' = case sort of
             Just (Fix (NamedSort name args)) -> Just (name,args)
             Nothing -> sort'
           argPrx = case sort'' of
             Just (_,sort''') -> fmap (\s -> Just $ withSort dtInfo s ProxyArg) sort'''
             Nothing -> genericReplicate (argCount struct) Nothing
           sorts' = fmap (\field -> argumentSortToSort
                                    (\i -> case sort'' of
                                        Nothing -> Nothing
                                        Just (_,sort''') -> Just $ sort''' `genericIndex` i)
                                    (fieldSort field)
                         ) (conFields con)
           rargs :: [AnyValue]
           rargs = fmap (\(val,s) -> valueToHaskell dtInfo AnyValue s val) (zip args sorts')
       in construct con argPrx rargs f

-- | Reconstruct the type annotation for a given SMT expression.
extractAnnotation :: SMTExpr a -> SMTAnnotation a
extractAnnotation (Var _ ann) = ann
extractAnnotation (QVar _ _ ann) = ann
extractAnnotation (FunArg _ ann) = ann
extractAnnotation (Const _ ann) = ann
extractAnnotation (AsArray f arg) = (arg,inferResAnnotation f arg)
extractAnnotation (Forall _ _ _) = ()
extractAnnotation (Exists _ _ _) = ()
extractAnnotation (Let _ _ f) = extractAnnotation f
extractAnnotation (Named x _) = extractAnnotation x
extractAnnotation (App f arg) = inferResAnnotation f (extractArgAnnotation arg)
extractAnnotation (InternalObj _ ann) = ann
extractAnnotation (UntypedExpr (expr::SMTExpr t)) = ProxyArg (undefined::t) (extractAnnotation expr)
extractAnnotation (UntypedExprValue (expr::SMTExpr t)) = ProxyArgValue (undefined::t) (extractAnnotation expr)

inferResAnnotation :: SMTFunction arg res -> ArgAnnotation arg -> SMTAnnotation res
inferResAnnotation SMTEq _ = ()
inferResAnnotation x@(SMTMap f) ann
  = withUndef f x (\ua ui -> let (i_ann,a_ann) = inferLiftedAnnotation ua ui ann
                             in (i_ann,inferResAnnotation f a_ann))
  where
    withUndef :: SMTFunction arg res -> SMTFunction (Lifted arg i) (SMTArray i res) -> (arg -> i -> b) -> b
    withUndef _ _ f' = f' undefined undefined
inferResAnnotation (SMTFun _ ann) _ = ann
inferResAnnotation (SMTBuiltIn _ ann) _ = ann
inferResAnnotation (SMTOrd _) _ = ()
inferResAnnotation (SMTArith _) ~(ann:_) = ann
inferResAnnotation SMTMinus ~(ann,_) = ann
inferResAnnotation (SMTIntArith _) ~(ann,_) = ann
inferResAnnotation SMTDivide ~(ann,_) = ann
inferResAnnotation SMTNeg ann = ann
inferResAnnotation SMTAbs ann = ann
inferResAnnotation SMTNot _ = ()
inferResAnnotation (SMTLogic _) _ = ()
inferResAnnotation SMTDistinct _ = ()
inferResAnnotation SMTToReal _ = ()
inferResAnnotation SMTToInt _ = ()
inferResAnnotation SMTITE ~(_,ann,_) = ann
inferResAnnotation (SMTBVComp _) _ = ()
inferResAnnotation (SMTBVBin _) ~(ann,_) = ann
inferResAnnotation (SMTBVUn _) ann = ann
inferResAnnotation SMTSelect ~(~(_,ann),_) = ann
inferResAnnotation SMTStore ~(ann,_,_) = ann
inferResAnnotation (SMTConstArray i_ann) v_ann = (i_ann,v_ann)
inferResAnnotation x@SMTConcat ~(ann1,ann2)
  = withUndef x $ \u1 u2 -> concatAnnotation u1 u2 ann1 ann2
  where
    withUndef :: SMTFunction (SMTExpr (BitVector a),SMTExpr (BitVector b)) res
                 -> (a -> b -> c) -> c
    withUndef _ f = f undefined undefined
inferResAnnotation x@(SMTExtract _ prLen) ann
  = withUndef x $ \u1 u2 -> extractAnn u1 u2 (reflectNat prLen 0) ann
  where
    withUndef :: SMTFunction (SMTExpr (BitVector a)) (BitVector res)
                 -> (a -> res -> c) -> c
    withUndef _ f = f undefined undefined
inferResAnnotation (SMTConstructor (Constructor prx dt con)) _
  = case dataTypeGetUndefined dt prx (\_ ann' -> cast ann') of
    Just ann' -> ann'
inferResAnnotation (SMTConTest _) _ = ()
inferResAnnotation (SMTFieldSel (Field prx dt _ f)) _
  = dataTypeGetUndefined dt prx (\u _ -> case fieldGet f prx u (\_ ann -> cast ann) of
                                    Just ann' -> ann')
inferResAnnotation (SMTDivisible _) _ = ()

-- Untyped

entype :: (forall a. SMTType a => SMTExpr a -> b) -> SMTExpr Untyped -> b
entype f (Var i (ProxyArg (_::t) ann))
  = f (Var i ann::SMTExpr t)
entype f (QVar lvl i (ProxyArg (_::t) ann))
  = f (QVar lvl i ann::SMTExpr t)
entype f (FunArg i (ProxyArg (_::t) ann))
  = f (FunArg i ann::SMTExpr t)
entype f (UntypedExpr x) = f x
entype f (InternalObj obj (ProxyArg (_::t) ann))
  = f (InternalObj obj ann :: SMTExpr t)
entype f expr = error $ "Can't entype expression "++show expr

entypeValue :: (forall a. SMTValue a => SMTExpr a -> b) -> SMTExpr UntypedValue -> b
entypeValue f (Var i (ProxyArgValue (_::t) ann))
  = f (Var i ann::SMTExpr t)
entypeValue f (QVar lvl i (ProxyArgValue (_::t) ann))
  = f (QVar lvl i ann::SMTExpr t)
entypeValue f (FunArg i (ProxyArgValue (_::t) ann))
  = f (FunArg i ann::SMTExpr t)
entypeValue f (Const (UntypedValue v) (ProxyArgValue (_::t) ann))
  = case cast v of
  Just rv -> f (Const (rv::t) ann)
entypeValue f (UntypedExprValue x) = f x
entypeValue f (InternalObj obj (ProxyArgValue (_::t) ann))
  = f (InternalObj obj ann :: SMTExpr t)
entypeValue f expr = error $ "Can't entype expression "++show expr

{-
entypeValueFunction :: (forall a. SMTValue a => SMTFunction arg a -> b)
                       -> SMTFunction arg UntypedValue
                       -> b
entypeValueFunction f (SMTFun i (ProxyArgValue (_::t) ann))
  = f (SMTFun i ann::SMTFunction arg t)-}

castUntypedExpr :: SMTType t => SMTExpr Untyped -> SMTExpr t
castUntypedExpr = entype (\expr -> case cast expr of
                             Just r -> r
                             Nothing -> error $ "smtlib2: castUntypedExpr failed.")

castUntypedExprValue :: SMTType t => SMTExpr UntypedValue -> SMTExpr t
castUntypedExprValue
  = entypeValue (\expr -> case cast expr of
                    Just r -> r
                    Nothing -> error $ "smtlib2: castUntypedExprValue failed.")

instance SMTType Untyped where
  type SMTAnnotation Untyped = ProxyArg
  getSort _ (ProxyArg u ann) = getSort u ann
  asDataType _ (ProxyArg u ann) = asDataType u ann
  asValueType _ (ProxyArg u ann) f = asValueType u ann f
  getProxyArgs _ (ProxyArg u ann) = getProxyArgs u ann
  additionalConstraints _ (ProxyArg u ann) = do
    constr <- additionalConstraints u ann
    return $ \(UntypedExpr x) -> case cast x of
      Just x' -> constr x'
  annotationFromSort _ sort = withSort emptyDataTypeInfo sort ProxyArg
  defaultExpr (ProxyArg (_::t) ann) = UntypedExpr (defaultExpr ann :: SMTExpr t)

instance SMTType UntypedValue where
  type SMTAnnotation UntypedValue = ProxyArgValue
  getSort _ (ProxyArgValue u ann) = getSort u ann
  asDataType _ (ProxyArgValue u ann) = asDataType u ann
  asValueType _ (ProxyArgValue u ann) f = asValueType u ann f
  getProxyArgs _ (ProxyArgValue u ann) = getProxyArgs u ann
  additionalConstraints _ (ProxyArgValue u ann) = do
    constr <- additionalConstraints u ann
    return $ \(UntypedExprValue x) -> case cast x of
      Just x' -> constr x'
  annotationFromSort _ sort
    = withSort emptyDataTypeInfo sort
      (\u ann -> case asValueType u ann ProxyArgValue of
          Just r -> r
          Nothing -> error $ "annotationFromSort for non-value type "++show (typeOf u)++" used.")
  defaultExpr (ProxyArgValue (_::t) ann)
    = UntypedExprValue (defaultExpr ann :: SMTExpr t)

instance SMTValue UntypedValue where
  unmangle = ComplexUnmangling $
             \f st val (ProxyArgValue _ ann)
             -> entypeValue
                (\(expr'::SMTExpr t) -> case cast ann of
                  Just ann' -> do
                    (res,nst) <- f st expr' ann'
                    return (Just $ UntypedValue res,nst)
                ) val
  mangle = ComplexMangling (\(UntypedValue x) (ProxyArgValue (_::t) ann)
                             -> case cast x of
                                 Just x' -> UntypedExprValue $ Const (x'::t) ann)

-- Bool

instance SMTType Bool where
  type SMTAnnotation Bool = ()
  getSort _ _ = Fix BoolSort
  annotationFromSort _ _ = ()
  asValueType x ann f = Just $ f x ann
  defaultExpr _ = Const False ()

instance SMTValue Bool where
  unmangle = PrimitiveUnmangling (\val _ -> case val of
                                   BoolValue v -> Just v
                                   _ -> Nothing)
  mangle = PrimitiveMangling (\v _ -> BoolValue v)

-- Integer

instance SMTType Integer where
  type SMTAnnotation Integer = ()
  getSort _ _ = Fix IntSort
  annotationFromSort _ _ = ()
  asValueType x ann f = Just $ f x ann
  defaultExpr _ = Const 0 ()

instance SMTValue Integer where
  unmangle = PrimitiveUnmangling (\val _ -> case val of
                                   IntValue v -> Just v
                                   _ -> Nothing)
  mangle = PrimitiveMangling (\v _ -> IntValue v)

instance SMTArith Integer

instance Num (SMTExpr Integer) where
  fromInteger x = Const x ()
  (+) x y = App (SMTArith Plus) [x,y]
  (-) x y = App SMTMinus (x,y)
  (*) x y = App (SMTArith Mult) [x,y]
  negate x = App SMTNeg x
  abs x = App SMTAbs x
  signum x = App SMTITE (App (SMTOrd Ge) (x,Const 0 ()),Const 1 (),Const (-1) ())

instance SMTOrd Integer where
  (.<.) x y = App (SMTOrd Lt) (x,y)
  (.<=.) x y = App (SMTOrd Le) (x,y)
  (.>.) x y = App (SMTOrd Gt) (x,y)
  (.>=.) x y = App (SMTOrd Ge) (x,y)

instance Enum (SMTExpr Integer) where
  succ x = x + 1
  pred x = x - 1
  toEnum x = Const (fromIntegral x) ()
  fromEnum (Const x _) = fromIntegral x
  fromEnum _ = error $ "smtlib2: Can't use fromEnum on non-constant SMTExpr (use getValue to extract values from the solver)"
  enumFrom x = case x of
    Const x' _ -> fmap (\i -> Const i ()) (enumFrom x')
    _ -> x:[ x+(Const n ()) | n <- [1..] ]
  enumFromThen x inc = case inc of
    Const inc' _ -> case x of
      Const x' _ -> fmap (\i -> Const i ()) (enumFromThen x' inc')
      _ -> x:[ x + (Const (n*inc') ()) | n <- [1..]]
    _ -> [ Prelude.foldl (+) x (genericReplicate n inc) | n <- [(0::Integer)..]]
  enumFromThenTo (Const x _) (Const inc _) (Const lim _)
    = fmap (\i -> Const i ()) (enumFromThenTo x inc lim)
  enumFromThenTo _ _ _ = error $ "smtlib2: Can't use enumFromThenTo on non-constant SMTExprs"

-- Real

instance SMTType (Ratio Integer) where
  type SMTAnnotation (Ratio Integer) = ()
  getSort _ _ = Fix RealSort
  annotationFromSort _ _ = ()
  asValueType x ann f = Just $ f x ann
  defaultExpr _ = Const 0 ()

instance SMTValue (Ratio Integer) where
  unmangle = PrimitiveUnmangling (\val _ -> case val of
                                   RealValue v -> Just v
                                   _ -> Nothing)
  mangle = PrimitiveMangling (\v _ -> RealValue v)

instance SMTArith (Ratio Integer)

instance Num (SMTExpr (Ratio Integer)) where
  fromInteger x = Const (fromInteger x) ()
  (+) x y = App (SMTArith Plus) [x,y]
  (-) x y = App SMTMinus (x,y)
  (*) x y = App (SMTArith Mult) [x,y]
  negate = App SMTNeg
  abs x = App SMTITE (App (SMTOrd Ge) (x,Const 0 ()),x,App SMTNeg x)
  signum x = App SMTITE (App (SMTOrd Ge) (x,Const 0 ()),Const 1 (),Const (-1) ())

instance Fractional (SMTExpr (Ratio Integer)) where
  (/) x y = App SMTDivide (x,y)
  fromRational x = Const x ()

instance SMTOrd (Ratio Integer) where
  (.<.) x y = App (SMTOrd Lt) (x,y)
  (.<=.) x y = App (SMTOrd Le) (x,y)
  (.>.) x y = App (SMTOrd Gt) (x,y)
  (.>=.) x y = App (SMTOrd Ge) (x,y)

-- Arrays

instance (Args idx,SMTType val) => SMTType (SMTArray idx val) where
  type SMTAnnotation (SMTArray idx val) = (ArgAnnotation idx,SMTAnnotation val)
  getSort u (anni,annv) = Fix $ ArraySort (argSorts (getIdx u) anni) (getSort (getVal u) annv)
    where
      getIdx :: SMTArray i v -> i
      getIdx _ = undefined
      getVal :: SMTArray i v -> v
      getVal _ = undefined
  annotationFromSort u (Fix (ArraySort argSorts valSort)) = (argAnn,annotationFromSort (getVal u) valSort)
    where
      (argAnn,[]) = getArgAnnotation (getIdx u) argSorts
      getIdx :: SMTArray i v -> i
      getIdx _ = undefined
      getVal :: SMTArray i v -> v
      getVal _ = undefined
  asValueType _ _ _ = Nothing
  defaultExpr ~(anni,annv) = App (SMTConstArray anni) (defaultExpr annv)

instance (SMTType a) => Liftable (SMTExpr a) where
  type Lifted (SMTExpr a) i = SMTExpr (SMTArray i a)
  getLiftedArgumentAnn _ _ a_ann i_ann = (i_ann,a_ann)
  inferLiftedAnnotation _ _ ~(i,a) = (i,a)
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint _ = Dict
#endif

instance (SMTType a) => Liftable [SMTExpr a] where
  type Lifted [SMTExpr a] i = [SMTExpr (SMTArray i a)]
  getLiftedArgumentAnn _ _ a_anns i_ann = fmap (\a_ann -> (i_ann,a_ann)) a_anns
  inferLiftedAnnotation _ _ ~(~(i,x):xs) = (i,x:(fmap snd xs))
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint _ = Dict
#endif

instance (Liftable a,Liftable b)
         => Liftable (a,b) where
  type Lifted (a,b) i = (Lifted a i,Lifted b i)
  getLiftedArgumentAnn ~(x,y) i (a_ann,b_ann) i_ann = (getLiftedArgumentAnn x i a_ann i_ann,
                                                       getLiftedArgumentAnn y i b_ann i_ann)
  inferLiftedAnnotation ~(x,y) i ~(a_ann,b_ann) = let (ann_i,ann_a) = inferLiftedAnnotation x i a_ann
                                                      (_,ann_b) = inferLiftedAnnotation y i b_ann
                                                  in (ann_i,(ann_a,ann_b))
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint (_ :: p ((a,b),i)) = case getConstraint (Proxy :: Proxy (a,i)) of
    Dict -> case getConstraint (Proxy :: Proxy (b,i)) of
      Dict -> Dict
#endif

instance (Liftable a,Liftable b,Liftable c)
         => Liftable (a,b,c) where
  type Lifted (a,b,c) i = (Lifted a i,Lifted b i,Lifted c i)
  getLiftedArgumentAnn ~(x1,x2,x3) i (ann1,ann2,ann3) i_ann
     = (getLiftedArgumentAnn x1 i ann1 i_ann,
        getLiftedArgumentAnn x2 i ann2 i_ann,
        getLiftedArgumentAnn x3 i ann3 i_ann)
  inferLiftedAnnotation ~(x1,x2,x3) i ~(ann1,ann2,ann3)
    = let (i_ann,ann1') = inferLiftedAnnotation x1 i ann1
          (_,ann2') = inferLiftedAnnotation x2 i ann2
          (_,ann3') = inferLiftedAnnotation x3 i ann3
      in (i_ann,(ann1',ann2',ann3'))
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint (_ :: p ((a,b,c),i)) = case getConstraint (Proxy :: Proxy (a,i)) of
    Dict -> case getConstraint (Proxy :: Proxy (b,i)) of
      Dict -> case getConstraint (Proxy :: Proxy (c,i)) of
        Dict -> Dict
#endif

instance (Liftable a,Liftable b,Liftable c,Liftable d)
         => Liftable (a,b,c,d) where
  type Lifted (a,b,c,d) i = (Lifted a i,Lifted b i,Lifted c i,Lifted d i)
  getLiftedArgumentAnn ~(x1,x2,x3,x4) i (ann1,ann2,ann3,ann4) i_ann
     = (getLiftedArgumentAnn x1 i ann1 i_ann,
        getLiftedArgumentAnn x2 i ann2 i_ann,
        getLiftedArgumentAnn x3 i ann3 i_ann,
        getLiftedArgumentAnn x4 i ann4 i_ann)
  inferLiftedAnnotation ~(x1,x2,x3,x4) i ~(ann1,ann2,ann3,ann4)
    = let (i_ann,ann1') = inferLiftedAnnotation x1 i ann1
          (_,ann2') = inferLiftedAnnotation x2 i ann2
          (_,ann3') = inferLiftedAnnotation x3 i ann3
          (_,ann4') = inferLiftedAnnotation x4 i ann4
      in (i_ann,(ann1',ann2',ann3',ann4'))
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint (_ :: p ((a,b,c,d),i)) = case getConstraint (Proxy :: Proxy (a,i)) of
    Dict -> case getConstraint (Proxy :: Proxy (b,i)) of
      Dict -> case getConstraint (Proxy :: Proxy (c,i)) of
        Dict -> case getConstraint (Proxy :: Proxy (d,i)) of
          Dict -> Dict
#endif

instance (Liftable a,Liftable b,Liftable c,Liftable d,Liftable e)
         => Liftable (a,b,c,d,e) where
  type Lifted (a,b,c,d,e) i = (Lifted a i,Lifted b i,Lifted c i,Lifted d i,Lifted e i)
  getLiftedArgumentAnn ~(x1,x2,x3,x4,x5) i (ann1,ann2,ann3,ann4,ann5) i_ann
     = (getLiftedArgumentAnn x1 i ann1 i_ann,
        getLiftedArgumentAnn x2 i ann2 i_ann,
        getLiftedArgumentAnn x3 i ann3 i_ann,
        getLiftedArgumentAnn x4 i ann4 i_ann,
        getLiftedArgumentAnn x5 i ann5 i_ann)
  inferLiftedAnnotation ~(x1,x2,x3,x4,x5) i ~(ann1,ann2,ann3,ann4,ann5)
    = let (i_ann,ann1') = inferLiftedAnnotation x1 i ann1
          (_,ann2') = inferLiftedAnnotation x2 i ann2
          (_,ann3') = inferLiftedAnnotation x3 i ann3
          (_,ann4') = inferLiftedAnnotation x4 i ann4
          (_,ann5') = inferLiftedAnnotation x5 i ann5
      in (i_ann,(ann1',ann2',ann3',ann4',ann5'))
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint (_ :: p ((a,b,c,d,e),i)) = case getConstraint (Proxy :: Proxy (a,i)) of
    Dict -> case getConstraint (Proxy :: Proxy (b,i)) of
      Dict -> case getConstraint (Proxy :: Proxy (c,i)) of
        Dict -> case getConstraint (Proxy :: Proxy (d,i)) of
          Dict -> case getConstraint (Proxy :: Proxy (e,i)) of
            Dict -> Dict
#endif

instance (Liftable a,Liftable b,Liftable c,Liftable d,Liftable e,Liftable f)
         => Liftable (a,b,c,d,e,f) where
  type Lifted (a,b,c,d,e,f) i = (Lifted a i,Lifted b i,Lifted c i,Lifted d i,Lifted e i,Lifted f i)
  getLiftedArgumentAnn ~(x1,x2,x3,x4,x5,x6) i (ann1,ann2,ann3,ann4,ann5,ann6) i_ann
     = (getLiftedArgumentAnn x1 i ann1 i_ann,
        getLiftedArgumentAnn x2 i ann2 i_ann,
        getLiftedArgumentAnn x3 i ann3 i_ann,
        getLiftedArgumentAnn x4 i ann4 i_ann,
        getLiftedArgumentAnn x5 i ann5 i_ann,
        getLiftedArgumentAnn x6 i ann6 i_ann)
  inferLiftedAnnotation ~(x1,x2,x3,x4,x5,x6) i ~(ann1,ann2,ann3,ann4,ann5,ann6)
    = let (i_ann,ann1') = inferLiftedAnnotation x1 i ann1
          (_,ann2') = inferLiftedAnnotation x2 i ann2
          (_,ann3') = inferLiftedAnnotation x3 i ann3
          (_,ann4') = inferLiftedAnnotation x4 i ann4
          (_,ann5') = inferLiftedAnnotation x5 i ann5
          (_,ann6') = inferLiftedAnnotation x6 i ann6
      in (i_ann,(ann1',ann2',ann3',ann4',ann5',ann6'))
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint (_ :: p ((a,b,c,d,e,f),i)) = case getConstraint (Proxy :: Proxy (a,i)) of
    Dict -> case getConstraint (Proxy :: Proxy (b,i)) of
      Dict -> case getConstraint (Proxy :: Proxy (c,i)) of
        Dict -> case getConstraint (Proxy :: Proxy (d,i)) of
          Dict -> case getConstraint (Proxy :: Proxy (e,i)) of
            Dict -> case getConstraint (Proxy :: Proxy (f,i)) of
              Dict -> Dict
#endif

instance (TypeableNat n1,TypeableNat n2,TypeableNat (Add n1 n2))
         => Concatable (BVTyped n1) (BVTyped n2) where
  type ConcatResult (BVTyped n1) (BVTyped n2) = BVTyped (Add n1 n2)
  concatAnnotation _ _ _ _ = ()

instance (TypeableNat n2) => Concatable BVUntyped (BVTyped n2) where
  type ConcatResult BVUntyped (BVTyped n2) = BVUntyped
  concatAnnotation _ (_::BVTyped n2) ann1 _
    = ann1+(reflectNat (Proxy::Proxy n2) 0)

instance (TypeableNat n1) => Concatable (BVTyped n1) BVUntyped where
  type ConcatResult (BVTyped n1) BVUntyped = BVUntyped
  concatAnnotation (_::BVTyped n1) _ _ ann2
    = (reflectNat (Proxy::Proxy n1) 0)+ann2

instance Concatable BVUntyped BVUntyped where
  type ConcatResult BVUntyped BVUntyped = BVUntyped
  concatAnnotation _ _ ann1 ann2 = ann1+ann2

-- Arguments

instance (SMTType a) => Args (SMTExpr a) where
  type ArgAnnotation (SMTExpr a) = SMTAnnotation a
  foldExprs f = f
  foldsExprs f = f
  extractArgAnnotation = extractAnnotation
  toArgs _ (x:xs) = do
    r <- entype gcast x
    return (r,xs)
  toArgs _ [] = Nothing
  fromArgs x = [UntypedExpr x]
  getTypes (_::SMTExpr a) ann = [ProxyArg (undefined::a) ann]
  getArgAnnotation u (s:rest) = (annotationFromSort (getUndef u) s,rest)
  getArgAnnotation _ [] = error "smtlib2: To few sorts provided."

instance (Args a,Args b) => Args (a,b) where
  type ArgAnnotation (a,b) = (ArgAnnotation a,ArgAnnotation b)
  foldExprs f s ~(e1,e2) ~(ann1,ann2) = do
    ~(s1,e1') <- foldExprs f s e1 ann1
    ~(s2,e2') <- foldExprs f s1 e2 ann2
    return (s2,(e1',e2'))
  foldsExprs f s args ~(ann1,ann2) = do
    ~(s1,e1,r1) <- foldsExprs f s (fmap (\(~(e1,_),b) -> (e1,b)) args) ann1
    ~(s2,e2,r2) <- foldsExprs f s1 (fmap (\(~(_,e2),b) -> (e2,b)) args) ann2
    return (s2,zip e1 e2,(r1,r2))
  extractArgAnnotation ~(x,y) = (extractArgAnnotation x,
                                 extractArgAnnotation y)
  toArgs ~(ann1,ann2) x = do
    (r1,x1) <- toArgs ann1 x
    (r2,x2) <- toArgs ann2 x1
    return ((r1,r2),x2)
  fromArgs (x,y) = fromArgs x ++ fromArgs y
  getTypes ~(x1,x2) (ann1,ann2) = getTypes x1 ann1 ++ getTypes x2 ann2
  getArgAnnotation (_::(a1,a2)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
      in ((ann1,ann2),r2)

instance (SMTValue a) => LiftArgs (SMTExpr a) where
  type Unpacked (SMTExpr a) = a
  liftArgs = Const
  unliftArgs expr f = f expr

instance (LiftArgs a,LiftArgs b) => LiftArgs (a,b) where
  type Unpacked (a,b) = (Unpacked a,Unpacked b)
  liftArgs (x,y) ~(a1,a2) = (liftArgs x a1,liftArgs y a2)
  unliftArgs (x,y) f = do
    rx <- unliftArgs x f
    ry <- unliftArgs y f
    return (rx,ry)

instance (Args a,Args b,Args c) => Args (a,b,c) where
  type ArgAnnotation (a,b,c) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c)
  foldExprs f s ~(e1,e2,e3) ~(ann1,ann2,ann3) = do
    ~(s1,e1') <- foldExprs f s e1 ann1
    ~(s2,e2') <- foldExprs f s1 e2 ann2
    ~(s3,e3') <- foldExprs f s2 e3 ann3
    return (s3,(e1',e2',e3'))
  foldsExprs f s args ~(ann1,ann2,ann3) = do
    ~(s1,e1,r1) <- foldsExprs f s (fmap (\(~(e1,_,_),b) -> (e1,b)) args) ann1
    ~(s2,e2,r2) <- foldsExprs f s1 (fmap (\(~(_,e2,_),b) -> (e2,b)) args) ann2
    ~(s3,e3,r3) <- foldsExprs f s2 (fmap (\(~(_,_,e3),b) -> (e3,b)) args) ann3
    return (s3,zip3 e1 e2 e3,(r1,r2,r3))
  extractArgAnnotation ~(e1,e2,e3)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3)
  toArgs ~(ann1,ann2,ann3) x = do
    (r1,x1) <- toArgs ann1 x
    (r2,x2) <- toArgs ann2 x1
    (r3,x3) <- toArgs ann3 x2
    return ((r1,r2,r3),x3)
  fromArgs (x1,x2,x3) = fromArgs x1 ++
                        fromArgs x2 ++
                        fromArgs x3
  getArgAnnotation (_::(a1,a2,a3)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
      in ((ann1,ann2,ann3),r3)
  getTypes ~(x1,x2,x3) (ann1,ann2,ann3) = getTypes x1 ann1 ++ getTypes x2 ann2 ++ getTypes x3 ann3

instance (LiftArgs a,LiftArgs b,LiftArgs c) => LiftArgs (a,b,c) where
  type Unpacked (a,b,c) = (Unpacked a,Unpacked b,Unpacked c)
  liftArgs (x,y,z) ~(a1,a2,a3) = (liftArgs x a1,liftArgs y a2,liftArgs z a3)
  unliftArgs (x,y,z) f = do
    rx <- unliftArgs x f
    ry <- unliftArgs y f
    rz <- unliftArgs z f
    return (rx,ry,rz)

instance (Args a,Args b,Args c,Args d) => Args (a,b,c,d) where
  type ArgAnnotation (a,b,c,d) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c,ArgAnnotation d)
  foldExprs f s ~(e1,e2,e3,e4) ~(ann1,ann2,ann3,ann4) = do
    ~(s1,e1') <- foldExprs f s e1 ann1
    ~(s2,e2') <- foldExprs f s1 e2 ann2
    ~(s3,e3') <- foldExprs f s2 e3 ann3
    ~(s4,e4') <- foldExprs f s3 e4 ann4
    return (s4,(e1',e2',e3',e4'))
  foldsExprs f s args ~(ann1,ann2,ann3,ann4) = do
    ~(s1,e1,r1) <- foldsExprs f s (fmap (\(~(e1,_,_,_),b) -> (e1,b)) args) ann1
    ~(s2,e2,r2) <- foldsExprs f s1 (fmap (\(~(_,e2,_,_),b) -> (e2,b)) args) ann2
    ~(s3,e3,r3) <- foldsExprs f s2 (fmap (\(~(_,_,e3,_),b) -> (e3,b)) args) ann3
    ~(s4,e4,r4) <- foldsExprs f s3 (fmap (\(~(_,_,_,e4),b) -> (e4,b)) args) ann4
    return (s4,zip4 e1 e2 e3 e4,(r1,r2,r3,r4))
  extractArgAnnotation ~(e1,e2,e3,e4)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3,
       extractArgAnnotation e4)
  toArgs ~(ann1,ann2,ann3,ann4) x = do
    (r1,x1) <- toArgs ann1 x
    (r2,x2) <- toArgs ann2 x1
    (r3,x3) <- toArgs ann3 x2
    (r4,x4) <- toArgs ann4 x3
    return ((r1,r2,r3,r4),x4)
  fromArgs (x1,x2,x3,x4)
    = fromArgs x1 ++
      fromArgs x2 ++
      fromArgs x3 ++
      fromArgs x4
  getArgAnnotation (_::(a1,a2,a3,a4)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
          (ann4,r4) = getArgAnnotation (undefined::a4) r3
      in ((ann1,ann2,ann3,ann4),r4)
  getTypes ~(x1,x2,x3,x4) (ann1,ann2,ann3,ann4)
    = getTypes x1 ann1 ++
      getTypes x2 ann2 ++
      getTypes x3 ann3 ++
      getTypes x4 ann4

instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d) => LiftArgs (a,b,c,d) where
  type Unpacked (a,b,c,d) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d)
  liftArgs (x1,x2,x3,x4) ~(a1,a2,a3,a4) = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4)
  unliftArgs (x1,x2,x3,x4) f = do
    r1 <- unliftArgs x1 f
    r2 <- unliftArgs x2 f
    r3 <- unliftArgs x3 f
    r4 <- unliftArgs x4 f
    return (r1,r2,r3,r4)

instance (Args a,Args b,Args c,Args d,Args e) => Args (a,b,c,d,e) where
  type ArgAnnotation (a,b,c,d,e) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c,ArgAnnotation d,ArgAnnotation e)
  foldExprs f s ~(e1,e2,e3,e4,e5) ~(ann1,ann2,ann3,ann4,ann5) = do
    ~(s1,e1') <- foldExprs f s e1 ann1
    ~(s2,e2') <- foldExprs f s1 e2 ann2
    ~(s3,e3') <- foldExprs f s2 e3 ann3
    ~(s4,e4') <- foldExprs f s3 e4 ann4
    ~(s5,e5') <- foldExprs f s4 e5 ann5
    return (s5,(e1',e2',e3',e4',e5'))
  foldsExprs f s args ~(ann1,ann2,ann3,ann4,ann5) = do
    ~(s1,e1,r1) <- foldsExprs f s (fmap (\(~(e1,_,_,_,_),b) -> (e1,b)) args) ann1
    ~(s2,e2,r2) <- foldsExprs f s1 (fmap (\(~(_,e2,_,_,_),b) -> (e2,b)) args) ann2
    ~(s3,e3,r3) <- foldsExprs f s2 (fmap (\(~(_,_,e3,_,_),b) -> (e3,b)) args) ann3
    ~(s4,e4,r4) <- foldsExprs f s3 (fmap (\(~(_,_,_,e4,_),b) -> (e4,b)) args) ann4
    ~(s5,e5,r5) <- foldsExprs f s4 (fmap (\(~(_,_,_,_,e5),b) -> (e5,b)) args) ann5
    return (s5,zip5 e1 e2 e3 e4 e5,(r1,r2,r3,r4,r5))
  extractArgAnnotation ~(e1,e2,e3,e4,e5)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3,
       extractArgAnnotation e4,
       extractArgAnnotation e5)
  toArgs ~(ann1,ann2,ann3,ann4,ann5) x = do
    (r1,x1) <- toArgs ann1 x
    (r2,x2) <- toArgs ann2 x1
    (r3,x3) <- toArgs ann3 x2
    (r4,x4) <- toArgs ann4 x3
    (r5,x5) <- toArgs ann5 x4
    return ((r1,r2,r3,r4,r5),x5)
  fromArgs (x1,x2,x3,x4,x5)
    = fromArgs x1 ++
      fromArgs x2 ++
      fromArgs x3 ++
      fromArgs x4 ++
      fromArgs x5
  getArgAnnotation (_::(a1,a2,a3,a4,a5)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
          (ann4,r4) = getArgAnnotation (undefined::a4) r3
          (ann5,r5) = getArgAnnotation (undefined::a5) r4
      in ((ann1,ann2,ann3,ann4,ann5),r5)
  getTypes ~(x1,x2,x3,x4,x5) (ann1,ann2,ann3,ann4,ann5)
    = getTypes x1 ann1 ++
      getTypes x2 ann2 ++
      getTypes x3 ann3 ++
      getTypes x4 ann4 ++
      getTypes x5 ann5

instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d,LiftArgs e) => LiftArgs (a,b,c,d,e) where
  type Unpacked (a,b,c,d,e) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d,Unpacked e)
  liftArgs (x1,x2,x3,x4,x5) ~(a1,a2,a3,a4,a5) = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4,liftArgs x5 a5)
  unliftArgs (x1,x2,x3,x4,x5) f = do
    r1 <- unliftArgs x1 f
    r2 <- unliftArgs x2 f
    r3 <- unliftArgs x3 f
    r4 <- unliftArgs x4 f
    r5 <- unliftArgs x5 f
    return (r1,r2,r3,r4,r5)

instance (Args a,Args b,Args c,Args d,Args e,Args f) => Args (a,b,c,d,e,f) where
  type ArgAnnotation (a,b,c,d,e,f) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c,ArgAnnotation d,ArgAnnotation e,ArgAnnotation f)
  foldExprs f s ~(e1,e2,e3,e4,e5,e6) ~(ann1,ann2,ann3,ann4,ann5,ann6) = do
    ~(s1,e1') <- foldExprs f s e1 ann1
    ~(s2,e2') <- foldExprs f s1 e2 ann2
    ~(s3,e3') <- foldExprs f s2 e3 ann3
    ~(s4,e4') <- foldExprs f s3 e4 ann4
    ~(s5,e5') <- foldExprs f s4 e5 ann5
    ~(s6,e6') <- foldExprs f s5 e6 ann6
    return (s6,(e1',e2',e3',e4',e5',e6'))
  foldsExprs f s args ~(ann1,ann2,ann3,ann4,ann5,ann6) = do
    ~(s1,e1,r1) <- foldsExprs f s (fmap (\(~(e1,_,_,_,_,_),b) -> (e1,b)) args) ann1
    ~(s2,e2,r2) <- foldsExprs f s1 (fmap (\(~(_,e2,_,_,_,_),b) -> (e2,b)) args) ann2
    ~(s3,e3,r3) <- foldsExprs f s2 (fmap (\(~(_,_,e3,_,_,_),b) -> (e3,b)) args) ann3
    ~(s4,e4,r4) <- foldsExprs f s3 (fmap (\(~(_,_,_,e4,_,_),b) -> (e4,b)) args) ann4
    ~(s5,e5,r5) <- foldsExprs f s4 (fmap (\(~(_,_,_,_,e5,_),b) -> (e5,b)) args) ann5
    ~(s6,e6,r6) <- foldsExprs f s5 (fmap (\(~(_,_,_,_,_,e6),b) -> (e6,b)) args) ann6
    return  (s6,zip6 e1 e2 e3 e4 e5 e6,(r1,r2,r3,r4,r5,r6))
  extractArgAnnotation ~(e1,e2,e3,e4,e5,e6)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3,
       extractArgAnnotation e4,
       extractArgAnnotation e5,
       extractArgAnnotation e6)
  toArgs ~(ann1,ann2,ann3,ann4,ann5,ann6) x = do
    (r1,x1) <- toArgs ann1 x
    (r2,x2) <- toArgs ann2 x1
    (r3,x3) <- toArgs ann3 x2
    (r4,x4) <- toArgs ann4 x3
    (r5,x5) <- toArgs ann5 x4
    (r6,x6) <- toArgs ann6 x5
    return ((r1,r2,r3,r4,r5,r6),x6)
  fromArgs (x1,x2,x3,x4,x5,x6)
    = fromArgs x1 ++
      fromArgs x2 ++
      fromArgs x3 ++
      fromArgs x4 ++
      fromArgs x5 ++
      fromArgs x6
  getArgAnnotation (_::(a1,a2,a3,a4,a5,a6)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
          (ann4,r4) = getArgAnnotation (undefined::a4) r3
          (ann5,r5) = getArgAnnotation (undefined::a5) r4
          (ann6,r6) = getArgAnnotation (undefined::a6) r5
      in ((ann1,ann2,ann3,ann4,ann5,ann6),r6)
  getTypes ~(x1,x2,x3,x4,x5,x6) (ann1,ann2,ann3,ann4,ann5,ann6)
    = getTypes x1 ann1 ++
      getTypes x2 ann2 ++
      getTypes x3 ann3 ++
      getTypes x4 ann4 ++
      getTypes x5 ann5 ++
      getTypes x6 ann6

instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d,LiftArgs e,LiftArgs f) => LiftArgs (a,b,c,d,e,f) where
  type Unpacked (a,b,c,d,e,f) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d,Unpacked e,Unpacked f)
  liftArgs (x1,x2,x3,x4,x5,x6) ~(a1,a2,a3,a4,a5,a6)
    = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4,liftArgs x5 a5,liftArgs x6 a6)
  unliftArgs (x1,x2,x3,x4,x5,x6) f = do
    r1 <- unliftArgs x1 f
    r2 <- unliftArgs x2 f
    r3 <- unliftArgs x3 f
    r4 <- unliftArgs x4 f
    r5 <- unliftArgs x5 f
    r6 <- unliftArgs x6 f
    return (r1,r2,r3,r4,r5,r6)

instance Args a => Args [a] where
  type ArgAnnotation [a] = [ArgAnnotation a]
  foldExprs _ s _ [] = return (s,[])
  foldExprs f s ~(x:xs) (ann:anns) = do
    (s',x') <- foldExprs f s x ann
    (s'',xs') <- foldExprs f s' xs anns
    return (s'',x':xs')
  foldsExprs f s _ [] = return (s,[],[])
  foldsExprs f s args [ann] = do
    let args_heads = fmap (\(xs,b) -> (head xs,b)) args
    ~(s1,res_heads,zhead) <- foldsExprs f s args_heads ann
    return (s1,fmap (\x -> [x]) res_heads,[zhead])
  foldsExprs f s args (ann:anns) = do
    let args_heads = fmap (\(xs,b) -> (head xs,b)) args
        args_tails = fmap (\(xs,b) -> (tail xs,b)) args
    ~(s1,res_heads,zhead) <- foldsExprs f s args_heads ann
    ~(s2,res_tails,ztail) <- foldsExprs f s1 args_tails anns
    return (s2,zipWith (:) res_heads res_tails,zhead:ztail)
  extractArgAnnotation = fmap extractArgAnnotation
  toArgs [] xs = Just ([],xs)
  toArgs (ann:anns) x = do
    (r,x') <- toArgs ann x
    (rs,x'') <- toArgs anns x'
    return (r:rs,x'')
  fromArgs xs = concat $ fmap fromArgs xs
  getArgAnnotation _ [] = ([],[])
  getArgAnnotation (_::[a]) sorts = let (x,r1) = getArgAnnotation (undefined::a) sorts
                                        (xs,r2) = getArgAnnotation (undefined::[a]) r1
                                    in (x:xs,r2)
  getTypes _ [] = []
  getTypes ~(x:xs) (ann:anns) = getTypes x ann ++ getTypes xs anns

instance (Typeable a,Show a,Args b,Ord a) => Args (Map a b) where
  type ArgAnnotation (Map a b) = Map a (ArgAnnotation b)
  foldExprs f s mp mp_ann = foldlM (\(s',cmp) (k,ann) -> do
                                       let el = case Map.lookup k mp of
                                             Nothing -> error $ "smtlib2: Map annotation contains key "++
                                                        show k++
                                                        " but it is not in the map. (Map annotation: "++
                                                        show (Map.keys mp_ann)++
                                                        ", map: "++
                                                        show (Map.keys mp)
                                             Just x -> x
                                       (s'',el') <- foldExprs f s' el ann
                                       return (s'',Map.insert k el' cmp)
                                   ) (s,Map.empty) (Map.toList mp_ann)
  foldsExprs f s args mp_ann = do
    let lst_ann = Map.toAscList mp_ann
        lst = fmap (\(mp,extra) -> ([ mp Map.! k | (k,_) <- lst_ann ],extra)
                   ) args
    (ns,lst',lst_merged) <- foldsExprs f s lst (fmap snd lst_ann)
    return (ns,fmap (\lst'' -> Map.fromAscList $ zip (fmap fst lst_ann) lst''
                    ) lst',Map.fromAscList $ zip (fmap fst lst_ann) lst_merged)
  extractArgAnnotation = fmap extractArgAnnotation
  toArgs mp_ann exprs = case Map.mapAccum (\cst ann -> case cst of
                                              Nothing -> (Nothing,undefined)
                                              Just rest -> case toArgs ann rest of
                                                Nothing -> (Nothing,undefined)
                                                Just (res,rest') -> (Just rest',res)
                                          ) (Just exprs) mp_ann of
                          (Nothing,_) -> Nothing
                          (Just rest,mp) -> Just (mp,rest)
  fromArgs exprs = concat $ fmap fromArgs $ Map.elems exprs
  getTypes (_::Map a b) anns = concat [ getTypes (undefined::b) ann | (_,ann) <- Map.toAscList anns ]
  getArgAnnotation _ sorts = (Map.empty,sorts)

instance (Args a,Args b) => Args (Either a b) where
  type ArgAnnotation (Either a b) = Either (ArgAnnotation a) (ArgAnnotation b)
  foldExprs f s ~(Left x) (Left ann) = do
    (ns,res) <- foldExprs f s x ann
    return (ns,Left res)
  foldExprs f s ~(Right x) (Right ann) = do
    (ns,res) <- foldExprs f s x ann
    return (ns,Right res)
  foldsExprs f s lst (Left ann) = do
    (ns,ress,res) <- foldsExprs f s (fmap (\(x,p) -> (case x of
                                                         Left x' -> x',p)) lst) ann
    return (ns,fmap Left ress,Left res)
  foldsExprs f s lst (Right ann) = do
    (ns,ress,res) <- foldsExprs f s (fmap (\(x,p) -> (case x of
                                                         Right x' -> x',p)) lst) ann
    return (ns,fmap Right ress,Right res)
  extractArgAnnotation (Left x) = Left $ extractArgAnnotation x
  extractArgAnnotation (Right x) = Right $ extractArgAnnotation x
  toArgs (Left ann) exprs = do
    (res,rest) <- toArgs ann exprs
    return (Left res,rest)
  toArgs (Right ann) exprs = do
    (res,rest) <- toArgs ann exprs
    return (Right res,rest)
  fromArgs (Left xs) = fromArgs xs
  fromArgs (Right xs) = fromArgs xs
  getTypes (_::Either a b) (Left ann) = getTypes (undefined::a) ann
  getTypes (_::Either a b) (Right ann) = getTypes (undefined::b) ann
  getArgAnnotation _ _ = error "smtlib2: getArgAnnotation undefined for Either"

instance Args a => Args (Maybe a) where
  type ArgAnnotation (Maybe a) = Maybe (ArgAnnotation a)
  foldExprs _ s _ Nothing = return (s,Nothing)
  foldExprs f s ~(Just x) (Just ann) = do
    (ns,res) <- foldExprs f s x ann
    return (ns,Just res)
  foldsExprs _ s lst Nothing = return (s,fmap (const Nothing) lst,Nothing)
  foldsExprs f s lst (Just ann) = do
    (ns,ress,res) <- foldsExprs f s (fmap (\(x,p) -> (case x of
                                                         Just x' -> x',p)) lst) ann
    return (ns,fmap Just ress,Just res)
  extractArgAnnotation = fmap extractArgAnnotation
  toArgs Nothing exprs = Just (Nothing,exprs)
  toArgs (Just ann) exprs = do
    (res,rest) <- toArgs ann exprs
    return (Just res,rest)
  fromArgs Nothing = []
  fromArgs (Just x) = fromArgs x
  getTypes _ Nothing = []
  getTypes (_::Maybe a) (Just ann) = getTypes (undefined::a) ann
  getArgAnnotation _ _ = error "smtlib2: getArgAnnotation undefined for Maybe"

instance LiftArgs a => LiftArgs [a] where
  type Unpacked [a] = [Unpacked a]
  liftArgs _ [] = []
  liftArgs ~(x:xs) (ann:anns) = liftArgs x ann:liftArgs xs anns
  unliftArgs [] _ = return []
  unliftArgs (x:xs) f = do
    x' <- unliftArgs x f
    xs' <- unliftArgs xs f
    return (x':xs')

instance (Typeable a,Show a,Ord a,LiftArgs b) => LiftArgs (Map a b) where
  type Unpacked (Map a b) = Map a (Unpacked b)
  liftArgs mp ann = Map.mapWithKey (\k ann' -> liftArgs (mp Map.! k) ann') ann
  unliftArgs mp f = mapM (\el -> unliftArgs el f) mp

instance (LiftArgs a,LiftArgs b) => LiftArgs (Either a b) where
  type Unpacked (Either a b) = Either (Unpacked a) (Unpacked b)
  liftArgs ~(Left x) (Left ann) = Left (liftArgs x ann)
  liftArgs ~(Right x) (Right ann) = Right (liftArgs x ann)
  unliftArgs (Left x) f = do
    res <- unliftArgs x f
    return $ Left res
  unliftArgs (Right x) f = do
    res <- unliftArgs x f
    return $ Right res

instance LiftArgs a => LiftArgs (Maybe a) where
  type Unpacked (Maybe a) = Maybe (Unpacked a)
  liftArgs _ Nothing = Nothing
  liftArgs ~(Just x) (Just ann) = Just (liftArgs x ann)
  unliftArgs Nothing _ = return Nothing
  unliftArgs (Just x) f = do
    res <- unliftArgs x f
    return (Just res)

instance SMTType a => SMTType (Maybe a) where
  type SMTAnnotation (Maybe a) = SMTAnnotation a
  getSort u ann = Fix $ NamedSort "Maybe" [getSort (undefArg u) ann]
  asDataType _ _ = Just ("Maybe",
                         TypeCollection { argCount = 1
                                        , dataTypes = [dtMaybe]
                                        })
  getProxyArgs (_::Maybe t) ann = [ProxyArg (undefined::t) ann]
  annotationFromSort u (Fix (NamedSort "Maybe" [argSort])) = annotationFromSort (undefArg u) argSort
  asValueType (_::Maybe x) ann f = asValueType (undefined::x) ann $
                                   \(_::y) ann' -> f (undefined::Maybe y) ann'
  defaultExpr ann = withUndef $
                    \u -> App (SMTConstructor (nothing' ann)) ()
    where
      withUndef :: (a -> SMTExpr (Maybe a)) -> SMTExpr (Maybe a)
      withUndef f = f undefined

dtMaybe :: DataType
dtMaybe = DataType { dataTypeName = "Maybe"
                   , dataTypeConstructors = [conNothing,
                                             conJust]
                   , dataTypeGetUndefined = \sorts f -> case sorts of
                                                         [s] -> withProxyArg s $
                                                                \(_::t) ann -> f (undefined::Maybe t) ann
                   }

conNothing :: Constr
conNothing
  = Constr { conName = "Nothing"
           , conFields = []
           , construct = \[Just prx] [] f
                         -> withProxyArg prx $
                            \(_::t) ann -> f [prx] (Nothing::Maybe t) ann
           , conUndefinedArgs = \_ f -> f () ()
           , conTest = \args x -> case args of
                                   [s] -> withProxyArg s $
                                          \(_::t) _ -> case cast x of
                                                        Just (Nothing::Maybe t) -> True
                                                        _ -> False
           }

conJust :: Constr
conJust
  = Constr { conName = "Just"
           , conFields = [fieldFromJust]
           , construct = \sort args f
                         -> case args of
                             [v] -> withAnyValue v $
                                    \_ (rv::t) ann
                                    -> f [ProxyArg (undefined::t) ann] (Just rv) ann
           , conUndefinedArgs = \sorts f -> case sorts of
                                             [s] -> withProxyArg s $
                                                    \(_::t) ann -> f (undefined::SMTExpr t) ann
           , conTest = \args x -> case args of
                                   [s] -> withProxyArg s $
                                          \(_::t) _ -> case cast x of
                                                        Just (Just (_::t)) -> True
                                                        _ -> False
           }

nothing' :: SMTType a => SMTAnnotation a -> Constructor () (Maybe a)
nothing' ann = withUndef $
               \u -> Constructor [ProxyArg u ann] dtMaybe conNothing
  where
    withUndef :: (a -> Constructor () (Maybe a)) -> Constructor () (Maybe a)
    withUndef f = f undefined

just' :: SMTType a => SMTAnnotation a -> Constructor (SMTExpr a) (Maybe a)
just' ann = withUndef $
            \u -> Constructor [ProxyArg u ann] dtMaybe conJust
  where
    withUndef :: (a -> Constructor (SMTExpr a) (Maybe a)) -> Constructor (SMTExpr a) (Maybe a)
    withUndef f = f undefined

fieldFromJust :: DataField
fieldFromJust = DataField { fieldName = "fromJust"
                          , fieldSort = Fix $ ArgumentSort 0
                          , fieldGet = \args x f
                                       -> case args of
                                           [s] -> withProxyArg s $
                                                  \(_::t) ann
                                                  -> f (case cast x of
                                                         Just (arg::Maybe t) -> fromJust arg) ann
                          }

instance SMTValue a => SMTValue (Maybe a) where
  unmangle = case unmangle of
    PrimitiveUnmangling p
      -> PrimitiveUnmangling (\val ann -> case val of
                               ConstrValue "Nothing" [] _ -> Just Nothing
                               ConstrValue "Just" [arg] _
                                 -> case p arg ann of
                                     Just v -> Just (Just v)
                                     Nothing -> Nothing
                               _ -> Nothing)
    ComplexUnmangling p
      -> ComplexUnmangling $ \f st (expr::SMTExpr (Maybe t)) ann -> do
        (isNothing,st1) <- f st (App (SMTConTest
                                      (Constructor [ProxyArg (undefined::t) (extractAnnotation expr)]
                                       dtMaybe conNothing :: Constructor () (Maybe a))) expr
                                ) ()
        if isNothing
          then return (Just Nothing,st1)
          else do
           (val,st2) <- p f st1 (App (SMTFieldSel (Field [ProxyArg (undefined::t) (extractAnnotation expr)] dtMaybe conJust fieldFromJust)) expr) ann
           case val of
            Nothing -> return (Nothing,st2)
            Just val' -> return (Just (Just val'),st2)
  mangle = case mangle of
    PrimitiveMangling p
      -> PrimitiveMangling $
         \val ann -> case val of
                      (Nothing::Maybe t) -> ConstrValue "Nothing" [] (Just ("Maybe",[getSort (undefined::t) ann]))
                      Just x -> ConstrValue "Just" [p x ann] Nothing
    ComplexMangling p
      -> ComplexMangling $
         \(val::Maybe t) ann -> case val of
         Just x -> App (SMTConstructor
                        (Constructor [ProxyArg (undefined::t) ann] dtMaybe conJust))
                   (p x ann)
         Nothing -> App (SMTConstructor
                         (Constructor [ProxyArg (undefined::t) ann]
                          dtMaybe conNothing :: Constructor () (Maybe t)))
                    ()

-- | Get an undefined value of the type argument of a type.
undefArg :: b a -> a
undefArg _ = undefined

instance (Typeable a,SMTType a) => SMTType [a] where
  type SMTAnnotation [a] = SMTAnnotation a
  getSort u ann = Fix (NamedSort "List" [getSort (undefArg u) ann])
  asDataType _ _ = Just ("List",
                         TypeCollection { argCount = 1
                                        , dataTypes = [dtList] })
  getProxyArgs (_::[t]) ann = [ProxyArg (undefined::t) ann]
  annotationFromSort u (Fix (NamedSort "List" [sort])) = annotationFromSort (undefArg u) sort
  asValueType (_::[a]) ann f = asValueType (undefined::a) ann $
                               \(_::b) ann' -> f (undefined::[b]) ann'
  defaultExpr ann = App (SMTConstructor (nil' ann)) ()

dtList :: DataType
dtList = DataType { dataTypeName = "List"
                        , dataTypeConstructors = [conNil,conInsert]
                        , dataTypeGetUndefined = \args f -> case args of
                          [s] -> withProxyArg s (\(_::t) ann -> f (undefined::[t]) ann)
                        }

conNil :: Constr
conNil = Constr { conName = "nil"
                , conFields = []
                , construct = \[Just sort] args f
                              -> withProxyArg sort $
                                 \(_::t) ann -> f [sort] ([]::[t]) ann
                , conUndefinedArgs = \_ f -> f () ()
                , conTest = \args x -> case args of
                [s] -> withProxyArg s $
                       \(_::t) _ -> case cast x of
                                     Just ([]::[t]) -> True
                                     _ -> False
                }

conInsert :: Constr
conInsert = Constr { conName = "insert"
                   , conFields = [fieldHead
                                 ,fieldTail]
                   , construct = \sort args f
                                 -> case args of
                                     [h,t] -> withAnyValue h $
                                              \_ (v::t) ann
                                              -> case castAnyValue t of
                                                  Just (vs,_) -> f [ProxyArg (undefined::t) ann] (v:vs) ann
                   , conUndefinedArgs = \sorts f -> case sorts of
                   [s] -> withProxyArg s $
                          \(_::t) ann -> f (undefined::(SMTExpr t,SMTExpr [t])) (ann,ann)
                   , conTest = \args x -> case args of
                   [s] -> withProxyArg s $
                          \(_::t) _ -> case cast x of
                                        Just ((_:_)::[t]) -> True
                                        _ -> False
                   }

insert' :: SMTType a => SMTAnnotation a -> Constructor (SMTExpr a,SMTExpr [a]) [a]
insert' ann = withUndef $
              \u -> Constructor [ProxyArg u ann] dtList conInsert
  where
    withUndef :: (a -> Constructor (SMTExpr a,SMTExpr [a]) [a]) -> Constructor (SMTExpr a,SMTExpr [a]) [a]
    withUndef f = f undefined

nil' :: SMTType a => SMTAnnotation a -> Constructor () [a]
nil' ann = withUndef $
           \u -> Constructor [ProxyArg u ann] dtList conNil
  where
    withUndef :: (a -> Constructor () [a]) -> Constructor () [a]
    withUndef f = f undefined

fieldHead :: DataField
fieldHead = DataField { fieldName = "head"
                      , fieldSort = Fix (ArgumentSort 0)
                      , fieldGet = \args x f -> case args of
                      [s] -> withProxyArg s $
                             \(_::t) ann
                             -> case cast x of
                                 Just (ys::[t]) -> f (head ys) ann
                      }

fieldTail :: DataField
fieldTail = DataField { fieldName = "tail"
                      , fieldSort = Fix (NormalSort (NamedSort "List" [Fix (ArgumentSort 0)]))
                      , fieldGet = \args x f -> case args of
                      [s] -> withProxyArg s $
                             \(_::t) ann
                             -> case cast x of
                                 Just (ys::[t]) -> f (tail ys) ann
                      }

instance (Typeable a,SMTValue a) => SMTValue [a] where
  unmangle = case unmangle of
    PrimitiveUnmangling p
      -> PrimitiveUnmangling $ pUnmangle p
    ComplexUnmangling p
      -> ComplexUnmangling $ cUnmangle p
    where
      pUnmangle _ (ConstrValue "nil" [] _) ann = Just []
      pUnmangle p (ConstrValue "insert" [h,t] _) ann = do
        h' <- p h ann
        t' <- pUnmangle p t ann
        return (h':t')
      cUnmangle :: Monad m
                => ((forall b. SMTValue b => st -> SMTExpr b -> SMTAnnotation b -> m (b,st))
                    -> st -> SMTExpr a -> SMTAnnotation a -> m (Maybe a,st))
                -> (forall b. SMTValue b => st -> SMTExpr b -> SMTAnnotation b -> m (b,st))
                -> st -> SMTExpr [a] -> SMTAnnotation a -> m (Maybe [a],st)
      cUnmangle c f st (expr::SMTExpr [t]) ann = do
        (isNil,st1) <- f st (App (SMTConTest
                                  (Constructor [ProxyArg (undefined::t) ann] dtList conNil
                                   ::Constructor () [t]))
                             expr) ()
        if isNil
          then return (Just [],st1)
          else do
           (h,st2) <- c f st1 (App (SMTFieldSel (Field [ProxyArg (undefined::t) ann] dtList conInsert fieldHead))
                     expr) ann
           (t,st3) <- cUnmangle c f st2 (App (SMTFieldSel (Field [ProxyArg (undefined::t) ann] dtList conInsert fieldTail)) expr) ann
           return (do
                      h' <- h
                      t' <- t
                      return $ h':t',st3)
  mangle = case mangle of
    PrimitiveMangling p
      -> PrimitiveMangling $ pMangle p
    ComplexMangling p
      -> ComplexMangling $ cMangle p
    where
      pMangle _ ([]::[t]) ann = ConstrValue "nil" [] (Just ("List",[getSort (undefined::t) ann]))
      pMangle p (x:xs) ann = ConstrValue "insert" [p x ann,pMangle p xs ann] Nothing
      cMangle :: (a -> SMTAnnotation a -> SMTExpr a)
              -> [a] -> SMTAnnotation a -> SMTExpr [a]
      cMangle c ([]::[t]) ann
        = App (SMTConstructor (Constructor [ProxyArg (undefined::t) ann] dtList conNil)) ()
      cMangle c ((x::t):xs) ann
        = App (SMTConstructor (Constructor [ProxyArg (undefined::t) ann] dtList conInsert))
          (c x ann,cMangle c xs ann)

-- BitVector implementation

instance SMTType (BitVector BVUntyped) where
  type SMTAnnotation (BitVector BVUntyped) = Integer
  getSort _ l = Fix (BVSort l True)
  annotationFromSort _ (Fix (BVSort l _)) = l
  asValueType x ann f = Just $ f x ann
  defaultExpr bw = Const (BitVector 0) bw

instance IsBitVector BVUntyped where
  getBVSize _ = id

instance SMTValue (BitVector BVUntyped) where
  unmangle = PrimitiveUnmangling $
             \val _ -> case val of
             BVValue _ v -> Just (BitVector v)
             _ -> Nothing
  mangle = PrimitiveMangling $
           \(BitVector v) l -> BVValue l v

instance TypeableNat n => SMTType (BitVector (BVTyped n)) where
  type SMTAnnotation (BitVector (BVTyped n)) = ()
  getSort _ _ = Fix (BVSort (reflectNat (Proxy::Proxy n) 0) False)
  annotationFromSort _ _ = ()
  asValueType x ann f = Just $ f x ann
  defaultExpr _ = Const (BitVector 0) ()

instance TypeableNat n => IsBitVector (BVTyped n) where
  getBVSize (_::Proxy (BVTyped n)) _ = reflectNat (Proxy::Proxy n) 0

instance TypeableNat n => SMTValue (BitVector (BVTyped n)) where
  unmangle = PrimitiveUnmangling $
             \val _ -> case val of
             BVValue w v
               | (reflectNat (Proxy::Proxy n) 0)==w -> Just (BitVector v)
               | otherwise -> Nothing
             _ -> Nothing
  mangle = PrimitiveMangling $
           \(BitVector v) _ -> BVValue (reflectNat (Proxy::Proxy n) 0) v

bvUnsigned :: IsBitVector a => BitVector a -> SMTAnnotation (BitVector a) -> Integer
bvUnsigned (BitVector x) _ = x

bvSigned :: IsBitVector a => BitVector a -> SMTAnnotation (BitVector a) -> Integer
bvSigned (BitVector x::BitVector a) ann
  = let sz = getBVSize (Proxy::Proxy a) ann
    in if x < 2^(sz-1)
       then x
       else x-2^sz

bvRestrict :: IsBitVector a => BitVector a -> SMTAnnotation (BitVector a) -> BitVector a
bvRestrict (BitVector x::BitVector a) ann
  = let sz = getBVSize (Proxy::Proxy a) ann
    in BitVector (x `mod` (2^sz))

instance TypeableNat n => Num (BitVector (BVTyped n)) where
  (+) (BitVector x) (BitVector y) = BitVector (x+y)
  (-) (BitVector x) (BitVector y) = BitVector (x-y)
  (*) (BitVector x) (BitVector y) = BitVector (x*y)
  negate (BitVector x) = BitVector (negate x)
  abs (BitVector x) = BitVector (abs x)
  signum (BitVector x) = BitVector (signum x)
  fromInteger i = BitVector i

instance TypeableNat n => Num (SMTExpr (BitVector (BVTyped n))) where
  (+) (x::SMTExpr (BitVector (BVTyped n))) y = App (SMTBVBin BVAdd) (x,y)
  (-) (x::SMTExpr (BitVector (BVTyped n))) y = App (SMTBVBin BVSub) (x,y)
  (*) (x::SMTExpr (BitVector (BVTyped n))) y = App (SMTBVBin BVMul) (x,y)
  negate (x::SMTExpr (BitVector (BVTyped n))) = App (SMTBVUn BVNeg) x
  abs (x::SMTExpr (BitVector (BVTyped n))) = App SMTITE (App (SMTBVComp BVUGT) (x,Const (BitVector 0) ()),x,App (SMTBVUn BVNeg) x)
  signum (x::SMTExpr (BitVector (BVTyped n))) = App SMTITE (App (SMTBVComp BVUGT) (x,Const (BitVector 0) ()),Const (BitVector 1) (),Const (BitVector (-1)) ())
  fromInteger i = Const (BitVector i) ()

instance Extractable BVUntyped BVUntyped where
  extractAnn _ _ len _ = len
  getExtractLen _ _ len = len

instance TypeableNat n => Extractable (BVTyped n) BVUntyped where
  extractAnn _ _ len _ = len
  getExtractLen _ _ len = len

instance TypeableNat n => Extractable BVUntyped (BVTyped n) where
  extractAnn _ _ _ _ = ()
  getExtractLen _ (_::BVTyped n) _ = reflectNat (Proxy::Proxy n) 0

instance (TypeableNat n1,TypeableNat n2) => Extractable (BVTyped n1) (BVTyped n2) where
  extractAnn _ _ _ _ = ()
  getExtractLen _ (_::BVTyped n) _ = reflectNat (Proxy::Proxy n) 0

withSort :: DataTypeInfo -> Sort -> (forall t. SMTType t => t -> SMTAnnotation t -> r) -> r
withSort _ (Fix BoolSort) f = f (undefined::Bool) ()
withSort _ (Fix IntSort) f = f (undefined::Integer) ()
withSort _ (Fix RealSort) f = f (undefined::Rational) ()
withSort _ (Fix (BVSort { bvSortWidth = w
                        , bvSortUntyped = unt })) f
  = if unt
    then f (undefined::BitVector BVUntyped) w
    else reifyNat w (\(_::Proxy tp) -> f (undefined::BitVector (BVTyped tp)) ())
withSort mp (Fix (ArraySort args res)) f
  = withSorts mp args $ \(_::rargs) argAnn
                         -> withSort mp res $ \(_::rres) resAnn
                                               -> f (undefined::SMTArray rargs rres) (argAnn,resAnn)
withSort mp (Fix (NamedSort name args)) f
  = case Map.lookup name (datatypes mp) of
    Just (decl,_) -> dataTypeGetUndefined decl
                     (fmap (\s -> withSort mp s ProxyArg) args) f
    Nothing -> error $ "smtlib2: Datatype "++name++" not defined."

withNumSort :: DataTypeInfo -> Sort -> (forall t. (SMTArith t) => t -> SMTAnnotation t -> r) -> Maybe r
withNumSort _ (Fix IntSort) f = Just $ f (undefined::Integer) ()
withNumSort _ (Fix RealSort) f = Just $ f (undefined::Rational) ()
withNumSort _ _ _ = Nothing

withSorts :: DataTypeInfo -> [Sort] -> (forall arg . Liftable arg => arg -> ArgAnnotation arg -> r) -> r
withSorts mp [x] f = withSort mp x $ \(_::t) ann -> f (undefined::SMTExpr t) ann
withSorts mp [x0,x1] f
  = withSort mp x0 $
    \(_::r1) ann1
    -> withSort mp x1 $
       \(_::r2) ann2 -> f (undefined::(SMTExpr r1,SMTExpr r2)) (ann1,ann2)
withSorts mp [x0,x1,x2] f
  = withSort mp x0 $
    \(_::r1) ann1
     -> withSort mp x1 $
        \(_::r2) ann2
         -> withSort mp x2 $
            \(_::r3) ann3 -> f (undefined::(SMTExpr r1,SMTExpr r2,SMTExpr r3)) (ann1,ann2,ann3)

withArraySort :: DataTypeInfo -> [Sort] -> Sort -> (forall i v. (Liftable i,SMTType v) => SMTArray i v -> (ArgAnnotation i,SMTAnnotation v) -> a) -> a
withArraySort mp idx v f
  = withSorts mp idx $
    \(_::i) anni
    -> withSort mp v $
       \(_::vt) annv -> f (undefined::SMTArray i vt) (anni,annv)

-- | Recursively fold a monadic function over all sub-expressions of this expression
foldExprM :: (SMTType a,Monad m) => (forall t. SMTType t => s -> SMTExpr t -> m (s,[SMTExpr t]))
          -> s -> SMTExpr a -> m (s,[SMTExpr a])
foldExprM f s (Forall lvl args body) = do
  (s',exprs1) <- foldExprM f s body
  return (s',[ Forall lvl args body'
             | body' <- exprs1 ])
foldExprM f s (Exists lvl args body) = do
  (s',exprs1) <- foldExprM f s body
  return (s',[ Exists lvl args body'
             | body' <- exprs1 ])
foldExprM f s (Let lvl defs body) = do
  (s1,defs') <- foldDefs s defs
  (s2,body') <- foldExprM f s1 body
  return (s2,[ Let lvl defs body
             | defs <- defs'
             , body <- body' ])
  where
    foldDefs s [] = return (s,[[]])
    foldDefs s (d:ds) = do
      (s1,d') <- foldExprM f s d
      (s2,ds') <- foldDefs s1 ds
      return (s2,[ d:ds
                 | d <- d'
                 , ds <- ds' ])
foldExprM f s (App fun arg) = do
  (s',args') <- foldArgsM f s arg
  return (s',[ App fun arg'
             | arg' <- args' ])
foldExprM f s (Named expr i) = do
  (s',exprs') <- foldExprM f s expr
  return (s',[ Named expr' i
             | expr' <- exprs' ])
foldExprM f s (UntypedExpr e) = do
  (s',exprs') <- foldExprM f s e
  return (s',[ UntypedExpr e'
             | e' <- exprs' ])
foldExprM f s (UntypedExprValue e) = do
  (s',exprs') <- foldExprM f s e
  return (s',[ UntypedExprValue e'
             | e' <- exprs' ])
foldExprM f s expr = f s expr

-- | Recursively fold a monadic function over all sub-expressions of the argument
foldArgsM :: (Args a,Monad m) => (forall t. SMTType t => s -> SMTExpr t -> m (s,[SMTExpr t]))
           -> s -> a -> m (s,[a])
foldArgsM f s arg = do
  (ns,res) <- fold s (fromArgs arg)
  let res' = fmap (\x -> let Just (x',[]) = toArgs (extractArgAnnotation arg) x
                         in x'
                  ) res
  return (ns,res')
  where
    fold cs [] = return (cs,[[]])
    fold cs ((UntypedExpr expr):exprs) = do
      (s1,nexprs) <- foldExprM f cs expr
      (s2,rest) <- fold s1 exprs
      return (s2,[ (UntypedExpr x):xs
                 | x <- nexprs
                 , xs <- rest ])

-- | Recursively fold a function over all sub-expressions of this expression.
--   It is implemented as a special case of 'foldExprM'.
foldExpr :: SMTType a => (forall t. SMTType t => s -> SMTExpr t -> (s,SMTExpr t))
            -> s -> SMTExpr a -> (s,SMTExpr a)
foldExpr f s expr = case runIdentity $ foldExprM (\s' expr' -> let (ns,r) = f s' expr'
                                                               in return (ns,[r])) s expr of
                      (ns,[r]) -> (ns,r)


foldExprMux :: SMTType a => (forall t. SMTType t => s -> SMTExpr t -> (s,[SMTExpr t]))
               -> s -> SMTExpr a -> (s,[SMTExpr a])
foldExprMux f s expr = runIdentity $ foldExprM (\s' expr' -> return $ f s' expr') s expr

-- | Recursively fold a function over all sub-expressions of the argument.
--   It is implemented as a special case of 'foldArgsM'.
foldArgs :: Args a => (forall t. SMTType t => s -> SMTExpr t -> (s,SMTExpr t))
            -> s -> a -> (s,a)
foldArgs f s expr = case runIdentity $ foldArgsM (\s' expr' -> let (ns,expr'') = f s' expr'
                                                               in return (ns,[expr''])) s expr of
                      (ns,[r]) -> (ns,r)


foldArgsMux :: Args a => (forall t. SMTType t => s -> SMTExpr t -> (s,[SMTExpr t]))
            -> s -> a -> (s,[a])
foldArgsMux f s expr = runIdentity $ foldArgsM (\s' expr' -> return $ f s' expr') s expr

instance Args arg => Eq (SMTFunction arg res) where
  (==) f1 f2 = compareFun f1 f2 == EQ

instance Args arg => Ord (SMTFunction arg res) where
  compare = compareFun
  
compareFun :: (Args a1,Args a2) => SMTFunction a1 r1 -> SMTFunction a2 r2 -> Ordering
compareFun SMTEq SMTEq = EQ
compareFun SMTEq _ = LT
compareFun _ SMTEq = GT
compareFun (SMTMap f1) (SMTMap f2) = compareFun f1 f2
compareFun (SMTMap _) _ = LT
compareFun _ (SMTMap _) = GT
compareFun (SMTFun i _) (SMTFun j _) = compare i j
compareFun (SMTFun _ _) _ = LT
compareFun _ (SMTFun _ _) = GT
compareFun (SMTBuiltIn n1 _) (SMTBuiltIn n2 _) = compare n1 n2
compareFun (SMTBuiltIn _ _) _ = LT
compareFun _ (SMTBuiltIn _ _) = GT
compareFun (SMTOrd op1) (SMTOrd op2) = compare op1 op2
compareFun (SMTOrd _) _ = LT
compareFun _ (SMTOrd _) = GT
compareFun (SMTArith op1) (SMTArith op2) = compare op1 op2
compareFun SMTMinus SMTMinus = EQ
compareFun SMTMinus _ = LT
compareFun _ SMTMinus = GT
compareFun (SMTIntArith op1) (SMTIntArith op2) = compare op1 op2
compareFun (SMTIntArith _) _ = LT
compareFun _ (SMTIntArith _) = GT
compareFun SMTDivide SMTDivide = EQ
compareFun SMTDivide _ = LT
compareFun _ SMTDivide = GT
compareFun SMTNeg SMTNeg = EQ
compareFun SMTNeg _ = LT
compareFun _ SMTNeg = GT
compareFun SMTAbs SMTAbs = EQ
compareFun SMTAbs _ = LT
compareFun _ SMTAbs = GT
compareFun SMTNot SMTNot = EQ
compareFun SMTNot _ = LT
compareFun _ SMTNot = GT
compareFun (SMTLogic op1) (SMTLogic op2) = compare op1 op2
compareFun (SMTLogic _) _ = LT
compareFun _ (SMTLogic _) = GT
compareFun SMTDistinct SMTDistinct = EQ
compareFun SMTDistinct _ = LT
compareFun _ SMTDistinct = GT
compareFun SMTToReal SMTToReal = EQ
compareFun SMTToReal _ = LT
compareFun _ SMTToReal = GT
compareFun SMTToInt SMTToInt = EQ
compareFun SMTToInt _ = LT
compareFun _ SMTToInt = GT
compareFun SMTITE SMTITE = EQ
compareFun SMTITE _ = LT
compareFun _ SMTITE = GT
compareFun (SMTBVComp op1) (SMTBVComp op2) = compare op1 op2
compareFun (SMTBVComp _) _ = LT
compareFun _ (SMTBVComp _) = GT
compareFun (SMTBVBin op1) (SMTBVBin op2) = compare op1 op2
compareFun (SMTBVBin _) _ = LT
compareFun _ (SMTBVBin _) = GT
compareFun (SMTBVUn op1) (SMTBVUn op2) = compare op1 op2
compareFun (SMTBVUn _) _ = LT
compareFun _ (SMTBVUn _) = GT
compareFun SMTSelect SMTSelect = EQ
compareFun SMTSelect _ = LT
compareFun _ SMTSelect = GT
compareFun SMTStore SMTStore = EQ
compareFun SMTStore _ = LT
compareFun _ SMTStore = GT
compareFun (SMTConstArray _) (SMTConstArray _) = EQ
compareFun (SMTConstArray _) _ = LT
compareFun _ (SMTConstArray _) = GT
compareFun SMTConcat SMTConcat = EQ
compareFun SMTConcat _ = LT
compareFun _ SMTConcat = GT
compareFun (SMTExtract (_::Proxy start1) (_::Proxy len1)) (SMTExtract (_::Proxy start2) (_::Proxy len2))
  = compare (typeOf (undefined::start1),typeOf (undefined::len1))
    (typeOf (undefined::start2),typeOf (undefined::len2))
compareFun (SMTExtract _ _) _ = LT
compareFun _ (SMTExtract _ _) = GT
compareFun (SMTConstructor con1) (SMTConstructor con2)
  = compareConstructor con1 con2
compareFun (SMTConstructor _) _ = LT
compareFun _ (SMTConstructor _) = GT
compareFun (SMTConTest con1) (SMTConTest con2)
  = compareConstructor con1 con2
compareFun (SMTConTest _) _ = LT
compareFun _ (SMTConTest _) = GT
compareFun (SMTFieldSel f1) (SMTFieldSel f2) = compareField f1 f2
compareFun (SMTFieldSel _) _ = LT
compareFun _ (SMTFieldSel _) = GT
compareFun (SMTDivisible x) (SMTDivisible y) = compare x y
compareFun (SMTDivisible _) _ = LT
compareFun _ (SMTDivisible _) = GT

compareConstructor :: Constructor arg1 res1 -> Constructor arg2 res2 -> Ordering
compareConstructor (Constructor p1 dt1 con1) (Constructor p2 dt2 con2)
  = case compare (dataTypeName dt1) (dataTypeName dt2) of
  EQ -> case compare p1 p2 of
    EQ -> compare (conName con1) (conName con2)
    r -> r
  r -> r

compareField :: Field a1 f1 -> Field a2 f2 -> Ordering
compareField (Field p1 dt1 con1 f1) (Field p2 dt2 con2 f2)
  = case compare (dataTypeName dt1) (dataTypeName dt2) of
  EQ -> case compare p1 p2 of
    EQ -> case compare (conName con1) (conName con2) of
      EQ -> compare (fieldName f1) (fieldName f2)
      r -> r
    r -> r
  r -> r

compareArgs :: (Args a1,Args a2) => a1 -> a2 -> Ordering
compareArgs x y = compare (fromArgs x) (fromArgs y)

compareExprs :: (SMTType t1,SMTType t2) => SMTExpr t1 -> SMTExpr t2 -> Ordering
compareExprs (UntypedExpr e1) e2 = compareExprs e1 e2
compareExprs e1 (UntypedExpr e2) = compareExprs e1 e2
compareExprs (UntypedExprValue e1) e2 = compareExprs e1 e2
compareExprs e1 (UntypedExprValue e2) = compareExprs e1 e2
compareExprs (Var i _) (Var j _) = compare i j
compareExprs (Var _ _) _ = LT
compareExprs _ (Var _ _) = GT
compareExprs (QVar lvl1 i1 _) (QVar lvl2 i2 _) = case compare lvl1 lvl2 of
  EQ -> compare i1 i2
  r -> r
compareExprs (QVar _ _ _) _ = LT
compareExprs _ (QVar _ _ _) = GT
compareExprs (FunArg i _) (FunArg j _) = compare i j
compareExprs (FunArg _ _) _ = LT
compareExprs _ (FunArg _ _) = GT
compareExprs (Const i _) (Const j _) = case cast j of
      Just j' -> compare i j'
      Nothing -> compare (typeOf i) (typeOf j)
compareExprs (Const _ _) _ = LT
compareExprs _ (Const _ _) = GT
compareExprs (AsArray f1 _) (AsArray f2 _) = compareFun f1 f2
compareExprs (AsArray _ _) _ = LT
compareExprs _ (AsArray _ _) = GT
compareExprs (Forall lvl1 args1 f1) (Forall lvl2 args2 f2)
  = case compare lvl1 lvl2 of
     EQ -> case compare args1 args2 of
       EQ -> compareExprs f1 f2
       r -> r
     r -> r
compareExprs (Forall _ _ _) _ = LT
compareExprs _ (Forall _ _ _) = GT
compareExprs (Exists lvl1 args1 f1) (Exists lvl2 args2 f2)
  = case compare lvl1 lvl2 of
     EQ -> case compare args1 args2 of
       EQ -> compareExprs f1 f2
       r -> r
     r -> r
compareExprs (Exists _ _ _) _ = LT
compareExprs _ (Exists _ _ _) = GT
compareExprs (Let lvl1 arg1 f1) (Let lvl2 arg2 f2)
  = case compare lvl1 lvl2 of
     EQ -> case compare arg1 arg2 of
       EQ -> compareExprs f1 f2
       r -> r
     r -> r
compareExprs (Let _ _ _) _ = LT
compareExprs _ (Let _ _ _) = GT
compareExprs (App f1 arg1) (App f2 arg2) = case compareFun f1 f2 of
  EQ -> compareArgs arg1 arg2
  x -> x
compareExprs (App _ _) _ = LT
compareExprs _ (App _ _) = GT
compareExprs (Named _ i1) (Named _ i2) = compare i1 i2
compareExprs (Named _ _) _ = LT
compareExprs _ (Named _ _) = GT
compareExprs (InternalObj o1 ann1) (InternalObj o2 ann2) = case compare (typeOf o1) (typeOf o2) of
      EQ -> case compare (typeOf ann1) (typeOf ann2) of
        EQ -> case cast (o2,ann2) of
          Just (o2',ann2') -> compare (o1,ann1) (o2',ann2')
        r -> r
      r -> r
compareExprs (InternalObj _ _) _ = LT
compareExprs _ (InternalObj _ _) = GT

instance Eq a => Eq (SMTExpr a) where
  (==) x y = case eqExpr x y of
    Just True -> True
    _ -> False

instance SMTType t => Ord (SMTExpr t) where
  compare = compareExprs

eqExpr :: SMTExpr a -> SMTExpr a -> Maybe Bool
eqExpr lhs rhs = case (lhs,rhs) of
  (Var v1 _,Var v2 _) -> if v1 == v2
                         then Just True
                         else Nothing
  (QVar l1 v1 _,QVar l2 v2 _) -> if l1==l2 && v1==v2
                                 then Just True
                                 else Nothing
  (FunArg v1 _,FunArg v2 _) -> if v1==v2
                               then Just True
                               else Nothing
  (Const v1 _,Const v2 _) -> Just $ v1 == v2
  (AsArray f1 arg1,AsArray f2 arg2) -> case cast f2 of
    Nothing -> Nothing
    Just f2' -> case cast arg2 of
      Nothing -> Nothing
      Just arg2' -> if f1 == f2' && arg1 == arg2'
                    then Just True
                    else Nothing
  (Forall l1 a1 f1,Forall l2 a2 f2) -> if l1==l2 && a1==a2
                                       then eqExpr f1 f2
                                       else Nothing
  (Exists l1 a1 f1,Exists l2 a2 f2) -> if l1==l2 && a1==a2
                                       then eqExpr f1 f2
                                       else Nothing
  (Let l1 a1 f1,Let l2 a2 f2) -> if l1==l2 && a1==a2
                                 then eqExpr f1 f2
                                 else Nothing
  (Named e1 i1,Named e2 i2) -> if i1==i2
                               then eqExpr e1 e2
                               else Nothing
  (App f1 arg1,App f2 arg2) -> case cast f2 of
      Nothing -> Nothing
      Just f2' -> case cast arg2 of
        Nothing -> Nothing
        Just arg2' -> if f1 == f2' && arg1 == arg2'
                      then Just True
                      else Nothing
  (InternalObj o1 ann1,InternalObj o2 ann2) -> case cast (o2,ann2) of
    Nothing -> Nothing
    Just (o2',ann2') -> Just $ (o1 == o2') && (ann1 == ann2')
  (UntypedExpr e1,UntypedExpr e2) -> case cast e2 of
    Just e2' -> eqExpr e1 e2'
    Nothing -> Just False
  (_,_) -> Nothing

instance Eq (Constructor arg res) where
  (Constructor p1 dt1 con1) == (Constructor p2 dt2 con2)
    = (dataTypeName dt1 == dataTypeName dt2) &&
      (p1 == p2) &&
      (conName con1 == conName con2)

instance Ord (Constructor arg res) where
  compare = compareConstructor

instance Eq (Field a f) where
  (Field p1 dt1 con1 f1) == (Field p2 dt2 con2 f2)
    = (dataTypeName dt1 == dataTypeName dt2) &&
      (p1 == p2) &&
      (conName con1 == conName con2) &&
      (fieldName f1 == fieldName f2)

instance Ord (Field a f) where
  compare = compareField

valueToConst :: DataTypeInfo -> Value -> (forall a. SMTType a => [ProxyArg] -> a -> SMTAnnotation a -> b) -> b
valueToConst _ (BoolValue c) app = app [] c ()
valueToConst _ (IntValue c) app = app [] c ()
valueToConst _ (RealValue c) app = app [] c ()
valueToConst _ (BVValue w v) app = reifyNat w (\(_::Proxy n) -> app [] (BitVector v::BitVector (BVTyped n)) ())
valueToConst dts (ConstrValue name args sort) app = case Map.lookup name (constructors dts) of
  Just (con,dt,tc) -> construct con (case sort of
                                      Nothing -> genericReplicate (argCount tc) Nothing
                                      Just (_,pars) -> [ Just $ withSort dts par ProxyArg
                                                       | par <- pars ])
                      (fmap (\val -> valueToConst dts val AnyValue) args)
                      app
