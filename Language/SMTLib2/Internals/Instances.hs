{- | Implements various instance declarations for 'Language.SMTLib2.SMTType',
     'Language.SMTLib2.SMTValue', etc. -}
{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,RankNTypes,TypeFamilies,GeneralizedNewtypeDeriving,DeriveDataTypeable,GADTs,FlexibleContexts,CPP,ScopedTypeVariables,TypeOperators #-}
module Language.SMTLib2.Internals.Instances where

import Language.SMTLib2.Internals
import Language.SMTLib2.Functions
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Word
import Data.Int
import Numeric
import Data.Bits
import qualified Data.Text as T
import Data.Ratio
import Data.Typeable
import qualified Data.ByteString as BS
import Data.Map
import Data.List (genericLength,genericReplicate)
import Data.Traversable
#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
import Data.Proxy
#endif

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

withSort :: Sort -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withSort (Sort u ann) f = f u ann
withSort (ArraySort i v) f = withArraySort i v f
#ifdef SMTLIB2_WITH_DATAKINDS
withSort (BVSort i) f = reifyNat i $ \(_::Proxy n) -> f (undefined::BitVector (BVTyped n)) ()
#else
withSort (BVSort i) f = reifyNat i $ \(_::n) -> f (undefined::BitVector (BVTyped n)) ()
#endif

withArraySort :: [Sort] -> Sort -> (forall i v. (Liftable i,SMTType v) => SMTArray i v -> (ArgAnnotation i,SMTAnnotation v) -> a) -> a
withArraySort idx v f
  = withArgSort idx $
    \(_::i) anni 
    -> withSort v $
       \(_::vt) annv -> f (undefined::SMTArray i vt) (anni,annv)

withArgSort :: [Sort] -> (forall i. Liftable i => i -> ArgAnnotation i -> a) -> a
withArgSort [] f = f () ()
withArgSort [i] f = withSort i $
                    \(_::ti) anni -> f (undefined::SMTExpr ti) anni
withArgSort [i1,i2] f
  = withSort i1 $
    \(_::t1) ann1
     -> withSort i2 $
        \(_::t2) ann2 -> f (undefined::(SMTExpr t1,SMTExpr t2)) (ann1,ann2)
withArgSort [i1,i2,i3] f
  = withSort i1 $
    \(_::t1) ann1
     -> withSort i2 $
        \(_::t2) ann2 
        -> withSort i3 $
           \(_::t3) ann3 -> f (undefined::(SMTExpr t1,SMTExpr t2,SMTExpr t3)) (ann1,ann2,ann3)
withArgSort _ _ = error $ "smtlib2: Please provide more cases for withArgSort."

withBVSort :: Sort -> (Integer -> a) -> Maybe a
withBVSort (BVSort i) f = Just (f i)
withBVSort _ _ = Nothing

instance Show Sort where
  show sort = withSort sort (\u _ -> show (typeOf u))

-- Bool

instance SMTType Bool where
  type SMTAnnotation Bool = ()
  getSortBase _ = L.Symbol "Bool"
  declareType = defaultDeclareValue
  fromSort _ = SortParser $ \sym _ -> case sym of
    L.Symbol "Bool" -> Just $ Sort (undefined::Bool) ()
    _ -> Nothing

instance SMTValue Bool where
  unmangle (L.Symbol "true") _ = Just True
  unmangle (L.Symbol "false") _ = Just False
  unmangle _ _ = Nothing
  mangle True _ = L.Symbol "true"
  mangle False _ = L.Symbol "false"

-- Integer

instance SMTType Integer where
  type SMTAnnotation Integer = ()
  getSortBase _ = L.Symbol "Int"
  declareType = defaultDeclareValue
  fromSort _ = SortParser $ \sym _ -> case sym of
    L.Symbol "Int" -> Just $ Sort (undefined::Integer) ()
    _ -> Nothing

instance SMTValue Integer where
  unmangle (L.Number (L.I v)) _ = Just v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) _ = Just $ - v
  unmangle _ _ = Nothing
  mangle v _
    | v < 0 = L.List [L.Symbol "-"
                     ,L.toLisp (-v)]
    | otherwise = L.toLisp v

instance SMTArith Integer

instance Num (SMTExpr Integer) where
  fromInteger x = Const x ()
  (+) x y = App Plus [x,y]
  (-) x y = App Minus (x,y)
  (*) x y = App Mult [x,y]
  negate x = App Neg x
  abs x = App Abs x
  signum x = App ITE (App Ge (x,Const 0 ()),Const 1 (),Const (-1) ())

instance SMTOrd Integer where
  (.<.) x y = App Lt (x,y)
  (.<=.) x y = App Le (x,y)
  (.>.) x y = App Gt (x,y)
  (.>=.) x y = App Ge (x,y)

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
  getSortBase _ = L.Symbol "Real"
  declareType = defaultDeclareValue
  fromSort _ = SortParser $ \sym _ -> case sym of
    L.Symbol "Real" -> Just (toSort (undefined::Ratio Integer) ())
    _ -> Nothing

instance SMTValue (Ratio Integer) where
  unmangle (L.Number (L.I v)) _ = Just $ fromInteger v
  unmangle (L.Number (L.D v)) _ = Just $ realToFrac v
  unmangle (L.List [L.Symbol "/"
                   ,x
                   ,y]) _ = do
                          q <- unmangle x ()
                          r <- unmangle y ()
                          return (q / r)
  unmangle (L.List [L.Symbol "-",r]) _ = do
    res <- unmangle r ()
    return (-res)
  unmangle _ _ = Nothing
  mangle v _ = L.List [L.Symbol "/"
                      ,L.Symbol $ T.pack $ (show $ numerator v)++".0"
                      ,L.Symbol $ T.pack $ (show $ denominator v)++".0"]

instance SMTArith (Ratio Integer)

instance Num (SMTExpr (Ratio Integer)) where
  fromInteger x = Const (fromInteger x) ()
  (+) x y = App Plus [x,y]
  (-) x y = App Minus (x,y)
  (*) x y = App Mult [x,y]
  negate = App Neg
  abs x = App ITE (App Ge (x,Const 0 ()),x,App Neg x)
  signum x = App ITE (App Ge (x,Const 0 ()),Const 1 (),Const (-1) ())

instance Fractional (SMTExpr (Ratio Integer)) where
  (/) x y = App Divide (x,y)
  fromRational x = Const x ()

instance SMTOrd (Ratio Integer) where
  (.<.) x y = App Lt (x,y)
  (.<=.) x y = App Le (x,y)
  (.>.) x y = App Gt (x,y)
  (.>=.) x y = App Ge (x,y)

-- Arrays

instance (Args idx,SMTType val) => SMTType (SMTArray idx val) where
  type SMTAnnotation (SMTArray idx val) = (ArgAnnotation idx,SMTAnnotation val)
  getSort u (anni,annv) = L.List $ L.Symbol "Array":(argSorts (getIdx u) anni++[getSort (getVal u) annv])
    where
      getIdx :: SMTArray i v -> i
      getIdx _ = undefined
      getVal :: SMTArray i v -> v
      getVal _ = undefined
  getSortBase _ = L.Symbol "Array"
  declareType u (anni,annv) = do
      declareArgTypes (getIdx u) anni
      declareType (getVal u) annv
      defaultDeclareType u (anni,annv)
    where
      getIdx :: SMTArray i v -> i
      getIdx _ = undefined
      getVal :: SMTArray i v -> v
      getVal _ = undefined
  toSort (_::SMTArray i v) (anni,annv) = ArraySort (toSorts (undefined::i) anni) (toSort (undefined::v) annv)
  fromSort _ = SortParser $ \sym rec -> case sym of
    L.List (L.Symbol "Array":args')
      -> let (idx,v) = splitLast sym $ fmap 
                       (\arg -> case parseSort rec arg rec of
                           Nothing -> error $ "smtlib2: Failed to parse array argument sort "++show arg
                           Just s -> s
                       ) args'
         in Just $ ArraySort idx v
    _ -> Nothing
    where
      splitLast :: L.Lisp -> [a] -> ([a],a)
      splitLast sym [] = error $ "smtlib2: Invalid array type: "++show sym
      splitLast _ [x] = ([],x)
      splitLast sym (x:xs) = let ~(xs',x') = splitLast sym xs
                             in (x:xs',x')

instance Liftable () where
  type Lifted () i = ()
  getLiftedArgumentAnn _ _ _ _ = ()
#ifdef SMTLIB2_WITH_CONSTRAINTS
  getConstraint _ = Dict
#endif  

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

-- BitVectors

-- | Create a SMT representation of a bitvector type with /n/ bits.
bv :: Integral i => i -- ^ The number of bits (/n/)
      -> L.Lisp
bv n = L.List [L.Symbol "_"
              ,L.Symbol "BitVec"
              ,L.Number $ L.I (fromIntegral n)]

-- | Helper function which applies a given function to the 'undefined' value.
withUndef1 :: (a -> g a) -> g a
withUndef1 f = f undefined

-- | Parses a given SMT bitvector value into a numerical value within the SMT monad.
getBVValue :: (Num a,Bits a,Read a) => L.Lisp -- ^ The SMT expression
              -> b -- ^ Ignored
              -> Maybe a
getBVValue arg _ = withUndef1 $ \u -> getBVValue' (bitSize u) arg

-- | Parses a given SMT bitvector value into a numerical value.
getBVValue' :: (Num a,Bits a,Read a,Integral i) => i -- ^ The number of bits of the value.
               -> L.Lisp -- ^ The SMT expression representing the value.
               -> Maybe a
getBVValue' _ (L.Number (L.I v)) = Just (fromInteger v)
getBVValue' len (L.Symbol s) = case T.unpack s of
  '#':'b':rest -> if genericLength rest == len
                  then (case readInt 2
                                 (\x -> x=='0' || x=='1')
                                 (\x -> if x=='0' then 0 else 1) 
                                 rest of
                          [(v,_)] -> Just v
                          _ -> Nothing)
                  else Nothing
  '#':'x':rest -> if (genericLength rest,0) == (len `divMod` 4)
                  then (case readHex rest of
                          [(v,_)] -> Just v
                          _ -> Nothing)
                  else Nothing
  _ -> Nothing
getBVValue' len (L.List [L.Symbol "_",L.Symbol val,L.Number (L.I bits)])
  = if bits == (fromIntegral len)
    then (case T.unpack val of
            'b':'v':num -> Just (read num)
            _ -> Nothing)
    else Nothing
getBVValue' _ _ = Nothing

-- | Helper function to help the formulation of 'Language.SMTLib2.Internals.mangle' functions for bitvectors.
putBVValue :: (Bits a,Ord a,Integral a,Show a) => a -> b -> L.Lisp
putBVValue x _ = putBVValue' (bitSize x) x

-- | Convert a numerical value into its SMT bitvector representation
putBVValue' :: (Bits a,Ord a,Integral a,Show a,Integral i) 
               => i -- ^ The number of bits used for the representation
               -> a -- ^ The numerical value
               -> L.Lisp
putBVValue' len x
  | len `mod` 4 == 0 = let v' = if x < 0
                                then complement (x-1)
                                else x
                           enc = showHex v' "" 
                           l = genericLength enc
                       in L.Symbol $ T.pack $ '#':'x':((genericReplicate ((len `div` 4)-l) '0')++enc)
  | otherwise = L.Symbol (T.pack ('#':'b':[ if testBit x (fromIntegral i)
                                            then '1'
                                            else '0'
                                            | i <- Prelude.reverse [0..(len-1)] ]))

-- Arguments

instance Args () where
  type ArgAnnotation () = ()
  foldExprs _ s _ _ = (s,())
  extractArgAnnotation _ = ()
  toArgs x = Just ((),x)
  toSorts _ _ = []
  getArgAnnotation _ xs = ((),xs)

instance (SMTType a) => Args (SMTExpr a) where
  type ArgAnnotation (SMTExpr a) = SMTAnnotation a
  foldExprs f = f
  extractArgAnnotation = extractAnnotation
  toArgs (x:xs) = do
    r <- entype gcast x
    return (r,xs)
  toArgs [] = Nothing
  toSorts (_::SMTExpr a) ann = [toSort (undefined::a) ann]
  getArgAnnotation _ (s:rest) = withSort s $ \_ ann -> case cast ann of
    Nothing -> error "smtlib2: Sort provided to getArgAnnotation doesn't fit."
    Just r -> (r,rest)

instance (Args a,Args b) => Args (a,b) where
  type ArgAnnotation (a,b) = (ArgAnnotation a,ArgAnnotation b)
  foldExprs f s ~(e1,e2) ~(ann1,ann2) = let ~(s1,e1') = foldExprs f s e1 ann1
                                            ~(s2,e2') = foldExprs f s1 e2 ann2
                                        in (s2,(e1',e2'))
  extractArgAnnotation ~(x,y) = (extractArgAnnotation x,
                                 extractArgAnnotation y)
  toArgs x = do
    (r1,x1) <- toArgs x
    (r2,x2) <- toArgs x1
    return ((r1,r2),x2)
  toSorts ~(x1,x2) (ann1,ann2) = toSorts x1 ann1 ++ toSorts x2 ann2
  getArgAnnotation (_::(a1,a2)) sorts
    = let (ann1,r1) = getArgAnnotation (undefined::a1) sorts
          (ann2,r2) = getArgAnnotation (undefined::a2) r1
      in ((ann1,ann2),r2)

instance (LiftArgs a,LiftArgs b) => LiftArgs (a,b) where
  type Unpacked (a,b) = (Unpacked a,Unpacked b)
  liftArgs (x,y) ~(a1,a2) = (liftArgs x a1,liftArgs y a2)
  unliftArgs (x,y) = do
    rx <- unliftArgs x
    ry <- unliftArgs y
    return (rx,ry)

instance (Args a,Args b,Args c) => Args (a,b,c) where
  type ArgAnnotation (a,b,c) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c)
  foldExprs f s ~(e1,e2,e3) ~(ann1,ann2,ann3) = let ~(s1,e1') = foldExprs f s e1 ann1
                                                    ~(s2,e2') = foldExprs f s1 e2 ann2
                                                    ~(s3,e3') = foldExprs f s2 e3 ann3
                                                in (s3,(e1',e2',e3'))
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

instance (LiftArgs a,LiftArgs b,LiftArgs c) => LiftArgs (a,b,c) where
  type Unpacked (a,b,c) = (Unpacked a,Unpacked b,Unpacked c)
  liftArgs (x,y,z) ~(a1,a2,a3) = (liftArgs x a1,liftArgs y a2,liftArgs z a3)
  unliftArgs (x,y,z) = do
    rx <- unliftArgs x
    ry <- unliftArgs y
    rz <- unliftArgs z
    return (rx,ry,rz)

instance (Args a,Args b,Args c,Args d) => Args (a,b,c,d) where
  type ArgAnnotation (a,b,c,d) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c,ArgAnnotation d)
  foldExprs f s ~(e1,e2,e3,e4) ~(ann1,ann2,ann3,ann4) = let ~(s1,e1') = foldExprs f s e1 ann1
                                                            ~(s2,e2') = foldExprs f s1 e2 ann2
                                                            ~(s3,e3') = foldExprs f s2 e3 ann3
                                                            ~(s4,e4') = foldExprs f s3 e4 ann4
                                                        in (s4,(e1',e2',e3',e4'))
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

instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d) => LiftArgs (a,b,c,d) where
  type Unpacked (a,b,c,d) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d)
  liftArgs (x1,x2,x3,x4) ~(a1,a2,a3,a4) = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4)
  unliftArgs (x1,x2,x3,x4) = do
    r1 <- unliftArgs x1
    r2 <- unliftArgs x2
    r3 <- unliftArgs x3
    r4 <- unliftArgs x4
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

instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d,LiftArgs e) => LiftArgs (a,b,c,d,e) where
  type Unpacked (a,b,c,d,e) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d,Unpacked e)
  liftArgs (x1,x2,x3,x4,x5) ~(a1,a2,a3,a4,a5) = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4,liftArgs x5 a5)
  unliftArgs (x1,x2,x3,x4,x5) = do
    r1 <- unliftArgs x1
    r2 <- unliftArgs x2
    r3 <- unliftArgs x3
    r4 <- unliftArgs x4
    r5 <- unliftArgs x5
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
    
instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d,LiftArgs e,LiftArgs f) => LiftArgs (a,b,c,d,e,f) where
  type Unpacked (a,b,c,d,e,f) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d,Unpacked e,Unpacked f)
  liftArgs (x1,x2,x3,x4,x5,x6) ~(a1,a2,a3,a4,a5,a6)
    = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4,liftArgs x5 a5,liftArgs x6 a6)
  unliftArgs (x1,x2,x3,x4,x5,x6) = do
    r1 <- unliftArgs x1
    r2 <- unliftArgs x2
    r3 <- unliftArgs x3
    r4 <- unliftArgs x4
    r5 <- unliftArgs x5
    r6 <- unliftArgs x6
    return (r1,r2,r3,r4,r5,r6)

instance Args a => Args [a] where
  type ArgAnnotation [a] = [ArgAnnotation a]
  foldExprs _ s _ [] = (s,[])
  foldExprs f s ~(x:xs) (ann:anns) = let (s',x') = foldExprs f s x ann
                                         (s'',xs') = foldExprs f s' xs anns
                                     in (s'',x':xs')
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

instance LiftArgs a => LiftArgs [a] where
  type Unpacked [a] = [Unpacked a]
  liftArgs _ [] = []
  liftArgs ~(x:xs) (ann:anns) = liftArgs x ann:liftArgs xs anns
  unliftArgs [] = return []
  unliftArgs (x:xs) = do
    x' <- unliftArgs x
    xs' <- unliftArgs xs
    return (x':xs')

instance (Ord a,Typeable a,Args b) => Args (Map a b) where
  type ArgAnnotation (Map a b) = Map a (ArgAnnotation b)
  foldExprs f s mp anns = mapAccumWithKey (\s1 key ann -> foldExprs f s1 (mp!key) ann) s anns
  extractArgAnnotation = fmap extractArgAnnotation
  toArgs _ = error "smtlib2: Don't use Map as argument type for functions you want to read back."
  getArgAnnotation _ = error "smtlib2: Don't use Map as argument type for functions you want to read back."

instance (Ord a,Typeable a,LiftArgs b) => LiftArgs (Map a b) where
  type Unpacked (Map a b) = Map a (Unpacked b)
  liftArgs mp anns = mapWithKey (\key ann -> liftArgs (mp!key) ann) anns
  unliftArgs = Data.Traversable.mapM unliftArgs

instance SMTType a => SMTType (Maybe a) where
  type SMTAnnotation (Maybe a) = SMTAnnotation a
  getSort u ann = L.List [L.Symbol "Maybe",getSort (undef u) ann]
    where
      undef :: Maybe a -> a
      undef _ = undefined
  getSortBase _ = L.Symbol "Maybe"
  declareType u ann = do
    declareType (undef u) ann
    declareType' (DeclaredType u ann)
      (declareDatatypes ["a"] [("Maybe",[("Nothing",[]),("Just",[("fromJust",L.Symbol "a")])])])
    where
      undef :: Maybe a -> a
      undef _ = undefined

instance SMTValue a => SMTValue (Maybe a) where
  unmangle (L.Symbol "Nothing") _ = Just Nothing
  unmangle (L.List [L.Symbol "as"
                   ,L.Symbol "Nothing"
                   ,_]) _ = Just Nothing
  unmangle (L.List [L.Symbol "Just"
                   ,res]) ann = do
    r <- unmangle res ann
    return (Just r)
  unmangle _ _ = Nothing
  mangle u@Nothing ann = L.List [L.Symbol "as"
                                ,L.Symbol "Nothing"
                                ,getSort u ann]
  mangle (Just x) ann = L.List [L.Symbol "Just"
                               ,mangle x ann]

-- | Get an undefined value of the type argument of a type.
undefArg :: b a -> a
undefArg _ = undefined

instance (Typeable a,SMTType a) => SMTType [a] where
  type SMTAnnotation [a] = SMTAnnotation a
  getSort u ann = L.List [L.Symbol "List",getSort (undefArg u) ann]
  declareType u ann = do
    declareType (undefArg u) ann
    defaultDeclareType u ann
  getSortBase _ = L.Symbol "List"

instance (Typeable a,SMTValue a) => SMTValue [a] where
  unmangle (L.Symbol "nil") _ = Just []
  unmangle (L.List [L.Symbol "insert",h,t]) ann = do
    h' <- unmangle h ann
    t' <- unmangle t ann
    return (h':t')
  unmangle _ _ = Nothing
  mangle [] _ = L.Symbol "nil"
  mangle (x:xs) ann = L.List [L.Symbol "insert"
                             ,mangle x ann
                             ,mangle xs ann]

-- BitVector implementation

instance SMTType (BitVector BVUntyped) where
  type SMTAnnotation (BitVector BVUntyped) = Integer
  getSort _ l = bv l
  getSortBase _ = error "smtlib2: No getSortBase implementation for BitVector"
  declareType = defaultDeclareValue
  toSort _ l = BVSort l
  fromSort _ = SortParser $ \l _ -> case l of
    L.List [L.Symbol "_"
           ,L.Symbol "BitVec"
           ,L.Number (L.I w)] -> Just (BVSort w)
    _ -> Nothing

instance SMTValue (BitVector BVUntyped) where
  unmangle v l = fmap BitVector $ getBVValue' l v
  mangle (BitVector v) l = putBVValue' l v

instance TypeableNat n => SMTType (BitVector (BVTyped n)) where
  type SMTAnnotation (BitVector (BVTyped n)) = ()
#ifdef SMTLIB2_WITH_DATAKINDS
  getSort _ _ = bv (reflectNat (Proxy::Proxy n) 0)
#else
  getSort _ _ = bv (reflectNat (undefined::n) 0)
#endif
  getSortBase _ = error "smtlib2: No getSortBase implementation for BitVector"
  declareType = defaultDeclareValue
#ifdef SMTLIB2_WITH_DATAKINDS
  toSort _ _ = BVSort (reflectNat (Proxy::Proxy n) 0)
#else
  toSort _ _ = BVSort (reflectNat (undefined::n) 0)
#endif
  fromSort _ = SortParser $ \l _ -> case l of
    L.List [L.Symbol "_"
           ,L.Symbol "BitVec"
#ifdef SMTLIB2_WITH_DATAKINDS            
           ,L.Number (L.I w)] -> if w == reflectNat (Proxy::Proxy n) 0
#else
           ,L.Number (L.I w)] -> if w == reflectNat (undefined::n) 0
#endif
                                 then Just (BVSort w)
                                 else Nothing
    _ -> Nothing

instance TypeableNat n => SMTValue (BitVector (BVTyped n)) where
#ifdef SMTLIB2_WITH_DATAKINDS
  unmangle v _ = fmap BitVector $ getBVValue' (reflectNat (Proxy::Proxy n) 0) v
  mangle (BitVector v) _ = putBVValue' (reflectNat (Proxy::Proxy n) 0) v
#else
  unmangle v _ = fmap BitVector $ getBVValue' (reflectNat (undefined::n) 0) v
  mangle (BitVector v) _ = putBVValue' (reflectNat (undefined::n) 0) v
#endif

instance TypeableNat n => Num (SMTExpr (BitVector (BVTyped n))) where
  (+) (x::SMTExpr (BitVector (BVTyped n))) y = App (BVAdd::SMTBVBinOp (BVTyped n)) (x,y)
  (-) (x::SMTExpr (BitVector (BVTyped n))) y = App (BVSub::SMTBVBinOp (BVTyped n)) (x,y)
  (*) (x::SMTExpr (BitVector (BVTyped n))) y = App (BVMul::SMTBVBinOp (BVTyped n)) (x,y)
  negate (x::SMTExpr (BitVector (BVTyped n))) = App (BVNeg::SMTBVUnOp (BVTyped n)) x
  signum (x::SMTExpr (BitVector (BVTyped n))) = App ITE (App (BVUGT::SMTBVComp (BVTyped n)) (x,Const (BitVector 0) ()),Const (BitVector 1) (),Const (BitVector (-1)) ())
  fromInteger i = Const (BitVector i) ()

-- Functions

instance SMTType a => SMTFunction (SMTEq a) where
  type SMTFunArg (SMTEq a) = [SMTExpr a]
  type SMTFunRes (SMTEq a) = Bool
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "="
  inferResAnnotation _ _ = ()

instance (SMTFunction f,Liftable r,r ~ Lifted (SMTFunArg f) i,
          Args i,
          Args r)
         => SMTFunction (SMTMap f i r) where
  type SMTFunArg (SMTMap f i r) = r
  type SMTFunRes (SMTMap f i r) = SMTArray i (SMTFunRes f)
  isOverloaded _ = True
  getFunctionSymbol x@(SMTMap f) arg_ann
    = withUndef x $
      \ua ui -> let (i_ann,a_ann) = inferLiftedAnnotation ua ui arg_ann
                    (sargs,sres) = functionGetSignature f a_ann (inferResAnnotation f a_ann)
                    sym = getFunctionSymbol f a_ann
                in L.List [L.Symbol "_"
                          ,L.Symbol "map"
                          ,if isOverloaded f
                           then L.List [sym,L.List sargs,sres]
                           else sym]
    where
      withUndef :: SMTMap f i r -> (SMTFunArg f -> i -> b) -> b
      withUndef _ f = f undefined undefined
  inferResAnnotation x@(SMTMap f) arg_ann
    = withUndef x $ \ua ui 
                    -> let (i_ann,a_ann) = inferLiftedAnnotation ua ui arg_ann
                       in (i_ann,inferResAnnotation f a_ann)
    where
      withUndef :: SMTMap f i r -> (SMTFunArg f -> i -> b) -> b
      withUndef _ f = f undefined undefined

instance SMTType a => SMTFunction (SMTOrdOp a) where
  type SMTFunArg (SMTOrdOp a) = (SMTExpr a,SMTExpr a)
  type SMTFunRes (SMTOrdOp a) = Bool
  isOverloaded _ = True
  getFunctionSymbol Ge _ = L.Symbol ">="
  getFunctionSymbol Gt _ = L.Symbol ">"
  getFunctionSymbol Le _ = L.Symbol "<="
  getFunctionSymbol Lt _ = L.Symbol "<"
  inferResAnnotation _ _ = ()

instance SMTType a => SMTFunction (SMTArithOp a) where
  type SMTFunArg (SMTArithOp a) = [SMTExpr a]
  type SMTFunRes (SMTArithOp a) = a
  isOverloaded _ = True
  getFunctionSymbol Plus _ = L.Symbol "+"
  getFunctionSymbol Mult _ = L.Symbol "*"
  inferResAnnotation _ = head

instance SMTType a => SMTFunction (SMTMinus a) where
  type SMTFunArg (SMTMinus a) = (SMTExpr a,SMTExpr a)
  type SMTFunRes (SMTMinus a) = a
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "-"
  inferResAnnotation _ = fst

instance SMTFunction SMTIntArith where
  type SMTFunArg SMTIntArith = (SMTExpr Integer,SMTExpr Integer)
  type SMTFunRes SMTIntArith = Integer
  isOverloaded _ = False
  getFunctionSymbol Div _ = L.Symbol "div"
  getFunctionSymbol Mod _ = L.Symbol "mod"
  getFunctionSymbol Rem _ = L.Symbol "rem"
  inferResAnnotation _ _ = ()

instance SMTFunction SMTDivide where
  type SMTFunArg SMTDivide = (SMTExpr Rational,SMTExpr Rational)
  type SMTFunRes SMTDivide = Rational
  isOverloaded _ = False
  getFunctionSymbol _ _ = L.Symbol "/"
  inferResAnnotation _ _ = ()

instance SMTType a => SMTFunction (SMTNeg a) where
  type SMTFunArg (SMTNeg a) = SMTExpr a
  type SMTFunRes (SMTNeg a) = a
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "-"
  inferResAnnotation _ = id

instance SMTType a => SMTFunction (SMTAbs a) where
  type SMTFunArg (SMTAbs a) = SMTExpr a
  type SMTFunRes (SMTAbs a) = a
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "abs"
  inferResAnnotation _ = id

instance SMTFunction SMTNot where
  type SMTFunArg SMTNot = SMTExpr Bool
  type SMTFunRes SMTNot = Bool
  isOverloaded _ = False
  getFunctionSymbol _ _ = L.Symbol "not"
  inferResAnnotation _ _ = ()

instance SMTFunction SMTLogic where
  type SMTFunArg SMTLogic = [SMTExpr Bool]
  type SMTFunRes SMTLogic = Bool
  isOverloaded _ = False
  getFunctionSymbol And _ = L.Symbol "and"
  getFunctionSymbol Or _ = L.Symbol "or"
  getFunctionSymbol XOr _ = L.Symbol "xor"
  getFunctionSymbol Implies _ = L.Symbol "=>"
  inferResAnnotation _ _ = ()

instance (Liftable a,SMTType r) => SMTFunction (SMTFun a r) where
  type SMTFunArg (SMTFun a r) = a
  type SMTFunRes (SMTFun a r) = r
  isOverloaded _ = False
  getFunctionSymbol (SMTFun name _) _ = L.Symbol name
  inferResAnnotation (SMTFun _ r) _ = r

instance SMTType a => SMTFunction (SMTDistinct a) where
  type SMTFunArg (SMTDistinct a) = [SMTExpr a]
  type SMTFunRes (SMTDistinct a) = Bool
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "distinct"
  inferResAnnotation _ _ = ()

instance SMTFunction SMTToReal where
  type SMTFunArg SMTToReal = SMTExpr Integer
  type SMTFunRes SMTToReal = Rational
  isOverloaded _ = False
  getFunctionSymbol _ _ = L.Symbol "to_real"
  inferResAnnotation _ _ = ()

instance SMTFunction SMTToInt where
  type SMTFunArg SMTToInt = SMTExpr Rational
  type SMTFunRes SMTToInt = Integer
  isOverloaded _ = False
  getFunctionSymbol _ _ = L.Symbol "to_int"
  inferResAnnotation _ _ = ()

instance SMTType a => SMTFunction (SMTITE a) where
  type SMTFunArg (SMTITE a) = (SMTExpr Bool,SMTExpr a,SMTExpr a)
  type SMTFunRes (SMTITE a) = a
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "ite"
  inferResAnnotation _ ~(_,ann,_) = ann

instance SMTFunction (SMTBVComp BVUntyped) where
  type SMTFunArg (SMTBVComp BVUntyped) = (SMTExpr (BitVector BVUntyped),SMTExpr (BitVector BVUntyped))
  type SMTFunRes (SMTBVComp BVUntyped) = Bool
  isOverloaded _ = True
  getFunctionSymbol s _ = bvCompSymbol s
  inferResAnnotation _ _ = ()

instance TypeableNat a => SMTFunction (SMTBVComp (BVTyped a)) where
  type SMTFunArg (SMTBVComp (BVTyped a)) = (SMTExpr (BitVector (BVTyped a)),SMTExpr (BitVector (BVTyped a)))
  type SMTFunRes (SMTBVComp (BVTyped a)) = Bool
  isOverloaded _ = True
  getFunctionSymbol s _ = bvCompSymbol s
  inferResAnnotation _ _ = ()

bvCompSymbol :: SMTBVComp a -> L.Lisp
bvCompSymbol BVULE = L.Symbol "bvule"
bvCompSymbol BVULT = L.Symbol "bvult"
bvCompSymbol BVUGE = L.Symbol "bvuge"
bvCompSymbol BVUGT = L.Symbol "bvugt"
bvCompSymbol BVSLE = L.Symbol "bvsle"
bvCompSymbol BVSLT = L.Symbol "bvslt"
bvCompSymbol BVSGE = L.Symbol "bvsge"
bvCompSymbol BVSGT = L.Symbol "bvsgt"

instance SMTFunction (SMTBVBinOp BVUntyped) where
  type SMTFunArg (SMTBVBinOp BVUntyped) = (SMTExpr (BitVector BVUntyped),SMTExpr (BitVector BVUntyped))
  type SMTFunRes (SMTBVBinOp BVUntyped) = BitVector BVUntyped
  isOverloaded _ = True
  getFunctionSymbol s _ = bvBinOpSymbol s
  inferResAnnotation _ ~(ann,_) = ann

instance TypeableNat a => SMTFunction (SMTBVBinOp (BVTyped a)) where
  type SMTFunArg (SMTBVBinOp (BVTyped a)) = (SMTExpr (BitVector (BVTyped a)),SMTExpr (BitVector (BVTyped a)))
  type SMTFunRes (SMTBVBinOp (BVTyped a)) = BitVector (BVTyped a)
  isOverloaded _ = True
  getFunctionSymbol s _ = bvBinOpSymbol s
  inferResAnnotation _ ~(ann,_) = ann

bvBinOpSymbol :: SMTBVBinOp a -> L.Lisp
bvBinOpSymbol BVAdd = L.Symbol "bvadd"
bvBinOpSymbol BVSub = L.Symbol "bvsub"
bvBinOpSymbol BVMul = L.Symbol "bvmul"
bvBinOpSymbol BVURem = L.Symbol "bvurem"
bvBinOpSymbol BVSRem = L.Symbol "bvsrem"
bvBinOpSymbol BVUDiv = L.Symbol "bvudiv"
bvBinOpSymbol BVSDiv = L.Symbol "bvsdiv"
bvBinOpSymbol BVSHL = L.Symbol "bvshl"
bvBinOpSymbol BVLSHR = L.Symbol "bvlshr"
bvBinOpSymbol BVASHR = L.Symbol "bvashr"
bvBinOpSymbol BVXor = L.Symbol "bvxor"
bvBinOpSymbol BVAnd = L.Symbol "bvand"
bvBinOpSymbol BVOr = L.Symbol "bvor"

instance SMTFunction (SMTBVUnOp BVUntyped) where
  type SMTFunArg (SMTBVUnOp BVUntyped) = SMTExpr (BitVector BVUntyped)
  type SMTFunRes (SMTBVUnOp BVUntyped) = BitVector BVUntyped
  isOverloaded _ = True
  getFunctionSymbol BVNot _ = L.Symbol "bvnot"
  getFunctionSymbol BVNeg _ = L.Symbol "bvneg"
  inferResAnnotation _ x = x

instance TypeableNat a => SMTFunction (SMTBVUnOp (BVTyped a)) where
  type SMTFunArg (SMTBVUnOp (BVTyped a)) = SMTExpr (BitVector (BVTyped a))
  type SMTFunRes (SMTBVUnOp (BVTyped a)) = BitVector (BVTyped a)
  isOverloaded _ = True
  getFunctionSymbol BVNot _ = L.Symbol "bvnot"
  getFunctionSymbol BVNeg _ = L.Symbol "bvneg"
  inferResAnnotation _ x = x

instance (Liftable i,SMTType v) => SMTFunction (SMTSelect i v) where
  type SMTFunArg (SMTSelect i v) = (SMTExpr (SMTArray i v),i)
  type SMTFunRes (SMTSelect i v) = v
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "select"
  inferResAnnotation _ ~(~(_,ann),_) = ann

instance (Liftable i,SMTType v) => SMTFunction (SMTStore i v) where
  type SMTFunArg (SMTStore i v) = (SMTExpr (SMTArray i v),i,SMTExpr v)
  type SMTFunRes (SMTStore i v) = SMTArray i v
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "store"
  inferResAnnotation _ ~(ann,_,_) = ann

instance (Args i,SMTType v) => SMTFunction (SMTConstArray i v) where
  type SMTFunArg (SMTConstArray i v) = SMTExpr v
  type SMTFunRes (SMTConstArray i v) = SMTArray i v
  isOverloaded _ = True
  getFunctionSymbol f@(ConstArray i_ann) v_ann
    = withUndef f $
      \u_arr -> L.List [L.Symbol "as"
                       ,L.Symbol "const"
                       ,getSort u_arr (i_ann,v_ann)]
    where
      withUndef :: SMTConstArray i v -> (SMTArray i v -> a) -> a
      withUndef _ f = f undefined
  inferResAnnotation (ConstArray i_ann) v_ann = (i_ann,v_ann)

instance SMTFunction (SMTConcat BVUntyped BVUntyped) where
  type SMTFunArg (SMTConcat BVUntyped BVUntyped) = (SMTExpr (BitVector BVUntyped),SMTExpr (BitVector BVUntyped))
  type SMTFunRes (SMTConcat BVUntyped BVUntyped) = BitVector BVUntyped
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "concat"
  inferResAnnotation _ ~(ann1,ann2) = ann1+ann2

instance (TypeableNat n1,TypeableNat n2
         ,TypeableNat (Add n1 n2)) => 
         SMTFunction (SMTConcat (BVTyped n1) (BVTyped n2)) where
  type SMTFunArg (SMTConcat (BVTyped n1) (BVTyped n2)) = (SMTExpr (BitVector (BVTyped n1)),SMTExpr (BitVector (BVTyped n2)))
  type SMTFunRes (SMTConcat (BVTyped n1) (BVTyped n2)) = BitVector (BVTyped (Add n1 n2))
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "concat"
  inferResAnnotation _ _ = ()

instance (TypeableNat n1,TypeableNat n2) 
         => SMTFunction (SMTExtract BVUntyped n1 n2 BVUntyped) where
  type SMTFunArg (SMTExtract BVUntyped n1 n2 BVUntyped) = SMTExpr (BitVector BVUntyped)
  type SMTFunRes (SMTExtract BVUntyped n1 n2 BVUntyped) = BitVector BVUntyped
  isOverloaded _ = True
  getFunctionSymbol (_ :: SMTExtract BVUntyped n1 n2 BVUntyped) _
#ifdef SMTLIB2_WITH_DATAKINDS
    = L.List [L.Symbol "_"
             ,L.Symbol "extract"
             ,L.toLisp $ reflectNat (Proxy::Proxy n1) 0
             ,L.toLisp $ reflectNat (Proxy::Proxy n2) 0]
#else
    = L.List [L.Symbol "_"
             ,L.Symbol "extract"
             ,L.toLisp $ reflectNat (undefined::n1) 0
             ,L.toLisp $ reflectNat (undefined::n2) 0]
#endif
  inferResAnnotation (_::SMTExtract BVUntyped n1 n2 BVUntyped) _
#ifdef SMTLIB2_WITH_DATAKINDS
    = (reflectNat (Proxy::Proxy n2) 0) - (reflectNat (Proxy::Proxy n1) 0) + 1
#else
    = (reflectNat (undefined::n2) 0) - (reflectNat (undefined::n1) 0) + 1
#endif

-- bvextract t l u = r
-- r = u - l + 1
-- r + l = u + 1

instance (TypeableNat n1,TypeableNat n2,TypeableNat n3,TypeableNat n4
         ,Add n4 n2 ~ S n3)
         => SMTFunction (SMTExtract (BVTyped n1) n2 n3 (BVTyped n4)) where
  type SMTFunArg (SMTExtract (BVTyped n1) n2 n3 (BVTyped n4)) = SMTExpr (BitVector (BVTyped n1))
  type SMTFunRes (SMTExtract (BVTyped n1) n2 n3 (BVTyped n4)) = BitVector (BVTyped n4)
  isOverloaded _ = True
  getFunctionSymbol (_ :: SMTExtract (BVTyped n1) n2 n3 (BVTyped n4)) _
#ifdef SMTLIB2_WITH_DATAKINDS
    = L.List [L.Symbol "_"
             ,L.Symbol "extract"
             ,L.toLisp $ reflectNat (Proxy::Proxy n2) 0
             ,L.toLisp $ reflectNat (Proxy::Proxy n3) 0]
#else
    = L.List [L.Symbol "_"
             ,L.Symbol "extract"
             ,L.toLisp $ reflectNat (undefined::n2) 0
             ,L.toLisp $ reflectNat (undefined::n3) 0]
#endif
  inferResAnnotation _ _ = ()

instance SMTType a => SMTFunction (SMTConTest a) where
  type SMTFunArg (SMTConTest a) = SMTExpr a
  type SMTFunRes (SMTConTest a) = Bool
  isOverloaded _ = False
  getFunctionSymbol (ConTest (Constructor name)) _
    = L.Symbol $ T.append "is-" name
  inferResAnnotation _ _ = ()

instance (SMTRecordType a,SMTType f) => SMTFunction (SMTFieldSel a f) where
  type SMTFunArg (SMTFieldSel a f) = SMTExpr a
  type SMTFunRes (SMTFieldSel a f) = f
  isOverloaded _ = False
  getFunctionSymbol (FieldSel (Field name)) _ = L.Symbol name
  inferResAnnotation (FieldSel field) ann 
    = getFieldAnn field ann

instance SMTType a => SMTFunction (SMTHead a) where
  type SMTFunArg (SMTHead a) = SMTExpr [a]
  type SMTFunRes (SMTHead a) = a
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "head"
  inferResAnnotation _ ann = ann

instance SMTType a => SMTFunction (SMTTail a) where
  type SMTFunArg (SMTTail a) = SMTExpr [a]
  type SMTFunRes (SMTTail a) = [a]
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "tail"
  inferResAnnotation _ ann = ann

instance SMTType a => SMTFunction (SMTInsert a) where
  type SMTFunArg (SMTInsert a) = (SMTExpr a,SMTExpr [a])
  type SMTFunRes (SMTInsert a) = [a]
  isOverloaded _ = True
  getFunctionSymbol _ _ = L.Symbol "insert"
  inferResAnnotation _ = fst