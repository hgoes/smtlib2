{- | Implements various instance declarations for 'Language.SMTLib2.SMTType',
     'Language.SMTLib2.SMTValue', etc. -}
{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,RankNTypes,TypeFamilies,GeneralizedNewtypeDeriving,DeriveDataTypeable,GADTs,FlexibleContexts,CPP,ScopedTypeVariables,TypeOperators #-}
module Language.SMTLib2.Internals.Instances where

import Language.SMTLib2.Internals
import Data.Ratio
import Data.Typeable
import Data.List (genericReplicate,zip4,zip5,zip6,genericIndex)
#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
import Data.Proxy
#endif
import Data.Fix
import qualified Data.Map as Map
import Data.Maybe (fromJust)

valueToHaskell :: DataTypeInfo
                  -> (forall t. SMTType t => t -> SMTAnnotation t -> r)
                  -> Maybe Sort
                  -> Value
                  -> r
valueToHaskell _ f _ (BoolValue v) = f v ()
valueToHaskell _ f _ (IntValue v) = f v ()
valueToHaskell _ f _ (RealValue v) = f v ()
valueToHaskell _ f (Just (Fix (BVSort { bvSortUntyped = True }))) (BVValue { bvValueWidth = w
                                                                             , bvValueValue = v })
  = f (BitVector v::BitVector BVUntyped) w
valueToHaskell _ f _ (BVValue { bvValueWidth = w
                                , bvValueValue = v })
  = reifyNat w (\(_::Proxy tp) -> f (BitVector v::BitVector (BVTyped tp)) ())
valueToHaskell dtInfo f sort (ConstrValue name args sort')
  = case Map.lookup name (constructors dtInfo) of
  Just (con,dt,struct)
    -> let sort'' = case sort of
             Just s -> Just s
             Nothing -> sort'
           argPrx = case sort'' of
             Nothing -> Nothing
             Just (Fix (NamedSort _ sortArgs))
               -> Just $ fmap (\s -> withSort dtInfo s ProxyArg) sortArgs
           sorts' = fmap (\field -> argumentSortToSort
                                    (\i -> case sort'' of
                                        Just (Fix (NamedSort _ sortArgs))
                                          -> Just $ sortArgs `genericIndex` i
                                        _ -> Nothing) (fieldSort field)
                         ) (conFields con)
           rargs :: [AnyValue]
           rargs = fmap (\(val,s) -> valueToHaskell dtInfo AnyValue s val) (zip args sorts')
       in construct con argPrx rargs f

-- | Reconstruct the type annotation for a given SMT expression.
extractAnnotation :: SMTExpr a -> SMTAnnotation a
extractAnnotation (Var _ ann) = ann
extractAnnotation (Const _ ann) = ann
extractAnnotation (AsArray f arg) = (arg,inferResAnnotation f arg)
extractAnnotation (Forall _ _) = ()
extractAnnotation (Exists _ _) = ()
extractAnnotation (Let _ x f) = extractAnnotation (f x)
extractAnnotation (Named x _) = extractAnnotation x
extractAnnotation (App f arg) = inferResAnnotation f (extractArgAnnotation arg)

inferResAnnotation :: SMTFunction arg res -> ArgAnnotation arg -> SMTAnnotation res
inferResAnnotation SMTEq _ = ()
inferResAnnotation x@(SMTMap f) ann
  = withUndef f x (\ua ui -> let (i_ann,a_ann) = inferLiftedAnnotation ua ui ann
                             in (i_ann,inferResAnnotation f a_ann))
  where
    withUndef :: SMTFunction arg res -> SMTFunction (Lifted arg i) (SMTArray i res) -> (arg -> i -> b) -> b
    withUndef _ _ f' = f' undefined undefined
inferResAnnotation (SMTFun _ ann) _ = ann
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
--inferResAnnotation (SMTConstructor (Constructor name)) ann = 
inferResAnnotation (SMTConTest _) _ = ()
inferResAnnotation (SMTFieldSel f) ann = getFieldAnn f ann

-- Bool

instance SMTType Bool where
  type SMTAnnotation Bool = ()
  getSort _ _ = Fix BoolSort
  annotationFromSort _ _ = ()
  asValueType x f = Just $ f x

instance SMTValue Bool where
  unmangle (BoolValue v) _ = Just v
  unmangle _ _ = Nothing
  mangle v _ = BoolValue v

-- Integer

instance SMTType Integer where
  type SMTAnnotation Integer = ()
  getSort _ _ = Fix IntSort
  annotationFromSort _ _ = ()
  asValueType x f = Just $ f x

instance SMTValue Integer where
  unmangle (IntValue v) _ = Just v
  unmangle _ _ = Nothing
  mangle v _ = IntValue v

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
  asValueType x f = Just $ f x

instance SMTValue (Ratio Integer) where
  unmangle (RealValue v) _ = Just v
  unmangle _ _ = Nothing
  mangle v _ = RealValue v

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
  asValueType _ _ = Nothing

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

instance Args () where
  type ArgAnnotation () = ()
  foldExprs _ s _ _ = (s,())
  foldsExprs _ s args = (s,fmap (const ()) args)
  extractArgAnnotation _ = ()
  toArgs x = Just ((),x)
  getSorts _ _ = []
  getArgAnnotation _ xs = ((),xs)

instance (SMTType a) => Args (SMTExpr a) where
  type ArgAnnotation (SMTExpr a) = SMTAnnotation a
  foldExprs f = f
  foldsExprs f = f
  extractArgAnnotation = extractAnnotation
  toArgs (x:xs) = do
    r <- entype gcast x
    return (r,xs)
  toArgs [] = Nothing
  getSorts (_::SMTExpr a) ann = [getSort (undefined::a) ann]
  getArgAnnotation u (s:rest) = (annotationFromSort (getUndef u) s,rest)
  getArgAnnotation _ [] = error "smtlib2: To few sorts provided."

instance (Args a,Args b) => Args (a,b) where
  type ArgAnnotation (a,b) = (ArgAnnotation a,ArgAnnotation b)
  foldExprs f s ~(e1,e2) ~(ann1,ann2) = let ~(s1,e1') = foldExprs f s e1 ann1
                                            ~(s2,e2') = foldExprs f s1 e2 ann2
                                        in (s2,(e1',e2'))
  foldsExprs f s args = let ~(s1,e1) = foldsExprs f s (fmap (\((e1,_),(ann1,_)) -> (e1,ann1)) args)
                            ~(s2,e2) = foldsExprs f s1 (fmap (\((_,e2),(_,ann2)) -> (e2,ann2)) args)
                        in (s2,zip e1 e2)
  extractArgAnnotation ~(x,y) = (extractArgAnnotation x,
                                 extractArgAnnotation y)
  toArgs x = do
    (r1,x1) <- toArgs x
    (r2,x2) <- toArgs x1
    return ((r1,r2),x2)
  getSorts ~(x1,x2) (ann1,ann2) = getSorts x1 ann1 ++ getSorts x2 ann2
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
  foldExprs f s ~(e1,e2,e3) ~(ann1,ann2,ann3) = let ~(s1,e1') = foldExprs f s e1 ann1
                                                    ~(s2,e2') = foldExprs f s1 e2 ann2
                                                    ~(s3,e3') = foldExprs f s2 e3 ann3
                                                in (s3,(e1',e2',e3'))
  foldsExprs f s args = let ~(s1,e1) = foldsExprs f s (fmap (\((e1,_,_),(ann1,_,_)) -> (e1,ann1)) args)
                            ~(s2,e2) = foldsExprs f s1 (fmap (\((_,e2,_),(_,ann2,_)) -> (e2,ann2)) args)
                            ~(s3,e3) = foldsExprs f s2 (fmap (\((_,_,e3),(_,_,ann3)) -> (e3,ann3)) args)
                        in (s3,zip3 e1 e2 e3)
  extractArgAnnotation ~(e1,e2,e3)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3)
  toArgs x = do
    (r1,x1) <- toArgs x
    (r2,x2) <- toArgs x1
    (r3,x3) <- toArgs x2
    return ((r1,r2,r3),x3)
  getArgAnnotation (_::(a1,a2,a3)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
      in ((ann1,ann2,ann3),r3)
  getSorts ~(x1,x2,x3) (ann1,ann2,ann3) = getSorts x1 ann1 ++ getSorts x2 ann2 ++ getSorts x3 ann3

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
  foldExprs f s ~(e1,e2,e3,e4) ~(ann1,ann2,ann3,ann4) = let ~(s1,e1') = foldExprs f s e1 ann1
                                                            ~(s2,e2') = foldExprs f s1 e2 ann2
                                                            ~(s3,e3') = foldExprs f s2 e3 ann3
                                                            ~(s4,e4') = foldExprs f s3 e4 ann4
                                                        in (s4,(e1',e2',e3',e4'))
  foldsExprs f s args = let ~(s1,e1) = foldsExprs f s (fmap (\((e1,_,_,_),(ann1,_,_,_)) -> (e1,ann1)) args)
                            ~(s2,e2) = foldsExprs f s1 (fmap (\((_,e2,_,_),(_,ann2,_,_)) -> (e2,ann2)) args)
                            ~(s3,e3) = foldsExprs f s2 (fmap (\((_,_,e3,_),(_,_,ann3,_)) -> (e3,ann3)) args)
                            ~(s4,e4) = foldsExprs f s3 (fmap (\((_,_,_,e4),(_,_,_,ann4)) -> (e4,ann4)) args)
                        in (s4,zip4 e1 e2 e3 e4)
  extractArgAnnotation ~(e1,e2,e3,e4)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3,
       extractArgAnnotation e4)
  toArgs x = do
    (r1,x1) <- toArgs x
    (r2,x2) <- toArgs x1
    (r3,x3) <- toArgs x2
    (r4,x4) <- toArgs x3
    return ((r1,r2,r3,r4),x4)
  getArgAnnotation (_::(a1,a2,a3,a4)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
          (ann4,r4) = getArgAnnotation (undefined::a4) r3
      in ((ann1,ann2,ann3,ann4),r4)
  getSorts ~(x1,x2,x3,x4) (ann1,ann2,ann3,ann4)
    = getSorts x1 ann1 ++
      getSorts x2 ann2 ++
      getSorts x3 ann3 ++
      getSorts x4 ann4

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
  foldExprs f s ~(e1,e2,e3,e4,e5) ~(ann1,ann2,ann3,ann4,ann5)
    = let ~(s1,e1') = foldExprs f s e1 ann1
          ~(s2,e2') = foldExprs f s1 e2 ann2
          ~(s3,e3') = foldExprs f s2 e3 ann3
          ~(s4,e4') = foldExprs f s3 e4 ann4
          ~(s5,e5') = foldExprs f s4 e5 ann5
      in (s5,(e1',e2',e3',e4',e5'))
  foldsExprs f s args = let ~(s1,e1) = foldsExprs f s (fmap (\((e1,_,_,_,_),(ann1,_,_,_,_)) -> (e1,ann1)) args)
                            ~(s2,e2) = foldsExprs f s1 (fmap (\((_,e2,_,_,_),(_,ann2,_,_,_)) -> (e2,ann2)) args)
                            ~(s3,e3) = foldsExprs f s2 (fmap (\((_,_,e3,_,_),(_,_,ann3,_,_)) -> (e3,ann3)) args)
                            ~(s4,e4) = foldsExprs f s3 (fmap (\((_,_,_,e4,_),(_,_,_,ann4,_)) -> (e4,ann4)) args)
                            ~(s5,e5) = foldsExprs f s4 (fmap (\((_,_,_,_,e5),(_,_,_,_,ann5)) -> (e5,ann5)) args)
                        in (s5,zip5 e1 e2 e3 e4 e5)
  extractArgAnnotation ~(e1,e2,e3,e4,e5)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3,
       extractArgAnnotation e4,
       extractArgAnnotation e5)
  toArgs x = do
    (r1,x1) <- toArgs x
    (r2,x2) <- toArgs x1
    (r3,x3) <- toArgs x2
    (r4,x4) <- toArgs x3
    (r5,x5) <- toArgs x4
    return ((r1,r2,r3,r4,r5),x5)
  getArgAnnotation (_::(a1,a2,a3,a4,a5)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
          (ann4,r4) = getArgAnnotation (undefined::a4) r3
          (ann5,r5) = getArgAnnotation (undefined::a5) r4
      in ((ann1,ann2,ann3,ann4,ann5),r5)
  getSorts ~(x1,x2,x3,x4,x5) (ann1,ann2,ann3,ann4,ann5)
    = getSorts x1 ann1 ++
      getSorts x2 ann2 ++
      getSorts x3 ann3 ++
      getSorts x4 ann4 ++
      getSorts x5 ann5

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
  foldExprs f s ~(e1,e2,e3,e4,e5,e6) ~(ann1,ann2,ann3,ann4,ann5,ann6)
    = let ~(s1,e1') = foldExprs f s e1 ann1
          ~(s2,e2') = foldExprs f s1 e2 ann2
          ~(s3,e3') = foldExprs f s2 e3 ann3
          ~(s4,e4') = foldExprs f s3 e4 ann4
          ~(s5,e5') = foldExprs f s4 e5 ann5
          ~(s6,e6') = foldExprs f s5 e6 ann6
      in (s6,(e1',e2',e3',e4',e5',e6'))
  foldsExprs f s args = let ~(s1,e1) = foldsExprs f s (fmap (\((e1,_,_,_,_,_),(ann1,_,_,_,_,_)) -> (e1,ann1)) args)
                            ~(s2,e2) = foldsExprs f s1 (fmap (\((_,e2,_,_,_,_),(_,ann2,_,_,_,_)) -> (e2,ann2)) args)
                            ~(s3,e3) = foldsExprs f s2 (fmap (\((_,_,e3,_,_,_),(_,_,ann3,_,_,_)) -> (e3,ann3)) args)
                            ~(s4,e4) = foldsExprs f s3 (fmap (\((_,_,_,e4,_,_),(_,_,_,ann4,_,_)) -> (e4,ann4)) args)
                            ~(s5,e5) = foldsExprs f s4 (fmap (\((_,_,_,_,e5,_),(_,_,_,_,ann5,_)) -> (e5,ann5)) args)
                            ~(s6,e6) = foldsExprs f s5 (fmap (\((_,_,_,_,_,e6),(_,_,_,_,_,ann6)) -> (e6,ann6)) args)
                        in (s6,zip6 e1 e2 e3 e4 e5 e6)
  extractArgAnnotation ~(e1,e2,e3,e4,e5,e6)
    = (extractArgAnnotation e1,
       extractArgAnnotation e2,
       extractArgAnnotation e3,
       extractArgAnnotation e4,
       extractArgAnnotation e5,
       extractArgAnnotation e6)
  toArgs x = do
    (r1,x1) <- toArgs x
    (r2,x2) <- toArgs x1
    (r3,x3) <- toArgs x2
    (r4,x4) <- toArgs x3
    (r5,x5) <- toArgs x4
    (r6,x6) <- toArgs x5
    return ((r1,r2,r3,r4,r5,r6),x6)
  getArgAnnotation (_::(a1,a2,a3,a4,a5,a6)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
          (ann3,r3) = getArgAnnotation (undefined::a3) r2
          (ann4,r4) = getArgAnnotation (undefined::a4) r3
          (ann5,r5) = getArgAnnotation (undefined::a5) r4
          (ann6,r6) = getArgAnnotation (undefined::a6) r5
      in ((ann1,ann2,ann3,ann4,ann5,ann6),r6)
  getSorts ~(x1,x2,x3,x4,x5,x6) (ann1,ann2,ann3,ann4,ann5,ann6)
    = getSorts x1 ann1 ++
      getSorts x2 ann2 ++
      getSorts x3 ann3 ++
      getSorts x4 ann4 ++
      getSorts x5 ann5 ++
      getSorts x6 ann6

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
  foldExprs _ s _ [] = (s,[])
  foldExprs f s ~(x:xs) (ann:anns) = let (s',x') = foldExprs f s x ann
                                         (s'',xs') = foldExprs f s' xs anns
                                     in (s'',x':xs')
  foldsExprs f s args = case head args of
    (_,[]) -> (s,fmap (const []) args)
    _ -> let args_heads = fmap (\(xs,anns) -> (head xs,head anns)) args
             args_tails = fmap (\(xs,anns) -> (tail xs,tail anns)) args
             ~(s1,res_heads) = foldsExprs f s args_heads
             ~(s2,res_tails) = foldsExprs f s1 args_tails
         in (s2,zipWith (:) res_heads res_tails)
  extractArgAnnotation = fmap extractArgAnnotation
  toArgs [] = Just ([],[])
  toArgs x = do
    (r,x') <- toArgs x
    (rs,x'') <- toArgs x'
    return (r:rs,x'')
  getArgAnnotation _ [] = ([],[])
  getArgAnnotation (_::[a]) sorts = let (x,r1) = getArgAnnotation (undefined::a) sorts
                                        (xs,r2) = getArgAnnotation (undefined::[a]) r1
                                    in (x:xs,r2)
  getSorts _ [] = []
  getSorts ~(x:xs) (ann:anns) = getSorts x ann ++ getSorts xs anns

instance LiftArgs a => LiftArgs [a] where
  type Unpacked [a] = [Unpacked a]
  liftArgs _ [] = []
  liftArgs ~(x:xs) (ann:anns) = liftArgs x ann:liftArgs xs anns
  unliftArgs [] _ = return []
  unliftArgs (x:xs) f = do
    x' <- unliftArgs x f
    xs' <- unliftArgs xs f
    return (x':xs')

instance SMTType a => SMTType (Maybe a) where
  type SMTAnnotation (Maybe a) = SMTAnnotation a
  getSort u ann = Fix $ NamedSort "Maybe" [getSort (undefArg u) ann]
  asDataType _ = Just ("Maybe",
                       TypeCollection { argCount = 1
                                      , dataTypes = [mbTp]
                                      })
    where
      mbTp = DataType { dataTypeName = "Maybe"
                      , dataTypeConstructors = [conNothing,
                                                conJust]
                      , dataTypeGetUndefined = \sorts f -> case sorts of
                        [s] -> withProxyArg s $
                               \(_::t) ann -> f (undefined::Maybe t) ann
                      }
      conNothing = Constr { conName = "Nothing"
                          , conFields = []
                          , construct = \args [] f
                                        -> case args of
                                          Just [prx]
                                            -> withProxyArg prx $
                                               \(_::t) ann -> f (Nothing::Maybe t) ann
                          , conTest = \args x -> case args of
                            [s] -> withProxyArg s $
                                   \(_::t) _ -> case cast x of
                                     Just (Nothing::Maybe t) -> True
                                     _ -> False
                          }
      conJust = Constr { conName = "Just"
                       , conFields = [DataField { fieldName = "fromJust"
                                                , fieldSort = Fix $ ArgumentSort 0
                                                , fieldGet = \args x f
                                                             -> case args of
                                                               [s] -> withProxyArg s $
                                                                      \(_::t) ann
                                                                      -> case cast x of
                                                                        Just (arg::Maybe t) -> f (fromJust arg) ann
                                                }]
                       , construct = \sort args f -> case args of
                         [v] -> withAnyValue v $
                                \rv ann -> f (Just rv) ann
                       , conTest = \args x -> case args of
                         [s] -> withProxyArg s $
                                \(_::t) _ -> case cast x of
                                  Just (Just (_::t)) -> True
                                  _ -> False
                       }
  getProxyArgs (_::Maybe t) ann = [ProxyArg (undefined::t) ann]
  annotationFromSort u (Fix (NamedSort "Maybe" [argSort])) = annotationFromSort (undefArg u) argSort
  asValueType (_::Maybe x) f = asValueType (undefined::x) $
                               \(_::y) -> f (undefined::Maybe y)

instance SMTValue a => SMTValue (Maybe a) where
  unmangle (ConstrValue "Nothing" [] sort) _ = Just Nothing
  unmangle (ConstrValue "Just" [arg] _) ann = case unmangle arg ann of
    Just v -> Just (Just v)
    Nothing -> Nothing
  --unmangle (AsValue v (Fix (NamedSort "Maybe" _))) ann = unmangle v ann
  unmangle _ _ = Nothing
  mangle u@Nothing ann = ConstrValue "Nothing" [] (Just $ getSort u ann)
  mangle u@(Just x) ann = ConstrValue "Just" [mangle x ann] (Just $ getSort u ann)

-- | Get an undefined value of the type argument of a type.
undefArg :: b a -> a
undefArg _ = undefined

instance (Typeable a,SMTType a) => SMTType [a] where
  type SMTAnnotation [a] = SMTAnnotation a
  getSort u ann = Fix (NamedSort "List" [getSort (undefArg u) ann])
  asDataType _ = Just ("List",
                       TypeCollection { argCount = 1
                                      , dataTypes = [tpList] })
    where
      tpList = DataType { dataTypeName = "List"
                        , dataTypeConstructors = [conNil,conCons]
                        , dataTypeGetUndefined = \args f -> case args of
                          [s] -> withProxyArg s (\(_::t) ann -> f (undefined::[t]) ann)
                        }
      conNil = Constr { conName = "nil"
                      , conFields = []
                      , construct = \sort args f -> case sort of
                        Just [s] -> withProxyArg s $
                                    \(_::t) ann -> f ([]::[t]) ann
                      , conTest = \args x -> case args of
                        [s] -> withProxyArg s $
                               \(_::t) _ -> case cast x of
                                 Just ([]::[t]) -> True
                                 _ -> False
                      }
      conCons = Constr { conName = "cons"
                       , conFields = [DataField { fieldName = "head"
                                                , fieldSort = Fix (ArgumentSort 0)
                                                , fieldGet = \args x f -> case args of
                                                  [s] -> withProxyArg s $
                                                         \(_::t) ann
                                                         -> case cast x of
                                                           Just (ys::[t]) -> f (head ys) ann }
                                     ,DataField { fieldName = "tail"
                                                , fieldSort = Fix (NormalSort (NamedSort "List" [Fix (ArgumentSort 0)]))
                                                , fieldGet = \args x f -> case args of
                                                  [s] -> withProxyArg s $
                                                         \(_::t) ann
                                                         -> case cast x of
                                                           Just (ys::[t]) -> f (tail ys) ann }]
                       , construct = \sort args f
                                     -> case args of
                                       [h,t] -> withAnyValue h $
                                                \v ann
                                                -> withAnyValue t $
                                                   \vs _ -> case cast vs of
                                                     Just vs' -> f (v:vs') ann
                       , conTest = \args x -> case args of
                         [s] -> withProxyArg s $
                                \(_::t) _ -> case cast x of
                                  Just ((_:_)::[t]) -> True
                                  _ -> False
                       }
  getProxyArgs (_::[t]) ann = [ProxyArg (undefined::t) ann]
  annotationFromSort u (Fix (NamedSort "List" [sort])) = annotationFromSort (undefArg u) sort
  asValueType (_::[a]) f = asValueType (undefined::a) $
                           \(_::b) -> f (undefined::[b])

instance (Typeable a,SMTValue a) => SMTValue [a] where
  unmangle (ConstrValue "nil" [] _) _ = Just []
  unmangle (ConstrValue "insert" [h,t] _) ann = do
    h' <- unmangle h ann
    t' <- unmangle t ann
    return (h':t')
  unmangle _ _ = Nothing
  mangle u@[] ann = ConstrValue "nil" [] (Just $ getSort u ann)
  mangle u@(x:xs) ann = ConstrValue "insert" [mangle x ann,mangle xs ann] (Just $ getSort u ann)

-- BitVector implementation

instance SMTType (BitVector BVUntyped) where
  type SMTAnnotation (BitVector BVUntyped) = Integer
  getSort _ l = Fix (BVSort l True)
  annotationFromSort _ (Fix (BVSort l _)) = l
  asValueType x f = Just $ f x

instance IsBitVector BVUntyped where
  getBVSize _ = id

instance SMTValue (BitVector BVUntyped) where
  unmangle (BVValue _ v) _ = Just (BitVector v)
  unmangle _ _ = Nothing
  mangle (BitVector v) l = BVValue l v

instance TypeableNat n => SMTType (BitVector (BVTyped n)) where
  type SMTAnnotation (BitVector (BVTyped n)) = ()
  getSort _ _ = Fix (BVSort (reflectNat (Proxy::Proxy n) 0) False)
  annotationFromSort _ _ = ()
  asValueType x f = Just $ f x

instance TypeableNat n => IsBitVector (BVTyped n) where
  getBVSize (_::Proxy (BVTyped n)) _ = reflectNat (Proxy::Proxy n) 0

instance TypeableNat n => SMTValue (BitVector (BVTyped n)) where
  unmangle (BVValue w v) _
    | (reflectNat (Proxy::Proxy n) 0)==w = Just (BitVector v)
    | otherwise = Nothing
  unmangle _ _ = Nothing
  mangle (BitVector v) _ = BVValue (reflectNat (Proxy::Proxy n) 0) v

bvUnsigned :: IsBitVector a => BitVector a -> SMTAnnotation (BitVector a) -> Integer
bvUnsigned (BitVector x) _ = x

bvSigned :: IsBitVector a => BitVector a -> SMTAnnotation (BitVector a) -> Integer
bvSigned (BitVector x::BitVector a) ann
  = let sz = getBVSize (Proxy::Proxy a) ann
    in if x < 2^(sz-1)
       then x
       else x-2^sz

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
