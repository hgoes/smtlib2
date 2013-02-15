{- | Implements various instance declarations for 'Language.SMTLib2.SMTType',
     'Language.SMTLib2.SMTValue', etc. -}
{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,TemplateHaskell,RankNTypes,TypeFamilies,GeneralizedNewtypeDeriving,DeriveDataTypeable #-}
module Language.SMTLib2.Internals.Instances where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.SMTMonad
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

-- Bool

instance SMTType Bool where
  type SMTAnnotation Bool = ()
  getSortBase _ = L.Symbol "Bool"
  declareType _ _ = return ()

instance SMTValue Bool where
  unmangle (L.Symbol "true") _ = return $ Just True
  unmangle (L.Symbol "false") _ = return $ Just False
  unmangle _ _ = return Nothing
  mangle True _ = L.Symbol "true"
  mangle False _ = L.Symbol "false"

-- Integer

instance SMTType Integer where
  type SMTAnnotation Integer = ()
  getSortBase _ = L.Symbol "Int"
  declareType _ _ = return ()

instance SMTValue Integer where
  unmangle (L.Number (L.I v)) _ = return $ Just v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) _ = return $ Just $ - v
  unmangle _ _ = return Nothing
  mangle v _
    | v < 0 = L.List [L.Symbol "-"
                     ,L.toLisp (-v)]
    | otherwise = L.toLisp v

instance SMTArith Integer

instance Num (SMTExpr Integer) where
  fromInteger x = Const x ()
  (+) x y = Plus [x,y]
  (-) = Minus
  (*) x y = Mult [x,y]
  negate = Neg
  abs x = ITE (Ge x (Const 0 ())) x (Neg x)
  signum x = ITE (Ge x (Const 0 ())) (Const 1 ()) (Const (-1) ())

instance SMTOrd Integer where
  (.<.) = Lt
  (.<=.) = Le
  (.>.) = Gt
  (.>=.) = Ge

-- Real

instance SMTType (Ratio Integer) where
  type SMTAnnotation (Ratio Integer) = ()
  getSortBase _ = L.Symbol "Real"
  declareType _ _ = return ()

instance SMTValue (Ratio Integer) where
  unmangle (L.Number (L.I v)) _ = return $ Just $ fromInteger v
  unmangle (L.Number (L.D v)) _ = return $ Just $ realToFrac v
  unmangle (L.List [L.Symbol "/"
                   ,x
                   ,y]) _ = do
                          q <- unmangle x ()
                          r <- unmangle y ()
                          return (do
                                     qq <- q
                                     rr <- r
                                     return $ qq / rr)
  unmangle (L.List [L.Symbol "-",r]) _ = do
    res <- unmangle r ()
    return (fmap (\x -> -x) res)
  unmangle _ _ = return Nothing
  mangle v _ = L.List [L.Symbol "/"
                      ,L.Symbol $ T.pack $ (show $ numerator v)++".0"
                      ,L.Symbol $ T.pack $ (show $ denominator v)++".0"]

instance SMTArith (Ratio Integer)

instance Num (SMTExpr (Ratio Integer)) where
  fromInteger x = Const (fromInteger x) ()
  (+) x y = Plus [x,y]
  (-) = Minus
  (*) x y = Mult [x,y]
  negate = Neg
  abs x = ITE (Ge x (Const 0 ())) x (Neg x)
  signum x = ITE (Ge x (Const 0 ())) (Const 1 ()) (Const (-1) ())

instance Fractional (SMTExpr (Ratio Integer)) where
  (/) = Divide
  fromRational x = Const x ()

instance SMTOrd (Ratio Integer) where
  (.<.) = Lt
  (.<=.) = Le
  (.>.) = Gt
  (.>=.) = Ge

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
    where
      getIdx :: SMTArray i v -> i
      getIdx _ = undefined
      getVal :: SMTArray i v -> v
      getVal _ = undefined

-- BitVectors

-- | Create a SMT representation of a bitvector type with /n/ bits.
bv :: Integral i => i -- ^ The number of bits (/n/)
      -> L.Lisp
bv n = L.List [L.Symbol "_"
              ,L.Symbol "BitVec"
              ,L.Number $ L.I (fromIntegral n)]

instance SMTType Word8 where
  type SMTAnnotation Word8 = ()
  getSortBase _ = bv (8::Integer)
  declareType _ _ = return ()

instance SMTType Int8 where
  type SMTAnnotation Int8 = ()
  getSortBase _ = bv (8::Integer)
  declareType _ _ = return ()

-- | Helper function which applies a given function to the 'undefined' value.
withUndef1 :: (a -> g a) -> g a
withUndef1 f = f undefined

-- | Parses a given SMT bitvector value into a numerical value within the SMT monad.
getBVValue :: (Num a,Bits a,Read a) => L.Lisp -- ^ The SMT expression
              -> b -- ^ Ignored
              -> SMT (Maybe a)
getBVValue arg _ = return $ withUndef1 $ \u -> getBVValue' (bitSize u) arg

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

instance SMTValue Word8 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTValue Int8 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word8
instance SMTBV Int8

instance SMTOrd Word8 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTOrd Int8 where
  (.<.) = BVSLT
  (.<=.) = BVSLE
  (.>.) = BVSGT
  (.>=.) = BVSGE

instance SMTType Word16 where
  type SMTAnnotation Word16 = ()
  getSortBase _ = bv (16::Integer)
  declareType _ _ = return ()

instance SMTType Int16 where
  type SMTAnnotation Int16 = ()
  getSortBase _ = bv (16::Integer)
  declareType _ _ = return ()

instance SMTValue Word16 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTValue Int16 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word16
instance SMTBV Int16

instance SMTOrd Word16 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTOrd Int16 where
  (.<.) = BVSLT
  (.<=.) = BVSLE
  (.>.) = BVSGT
  (.>=.) = BVSGE

instance SMTType Word32 where
  type SMTAnnotation Word32 = ()
  getSortBase _ = bv (32::Integer)
  declareType _ _ = return ()

instance SMTType Int32 where
  type SMTAnnotation Int32 = ()
  getSortBase _ = bv (32::Integer)
  declareType _ _ = return ()

instance SMTValue Word32 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTValue Int32 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word32
instance SMTBV Int32

instance SMTOrd Word32 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTOrd Int32 where
  (.<.) = BVSLT
  (.<=.) = BVSLE
  (.>.) = BVSGT
  (.>=.) = BVSGE

instance SMTType Word64 where
  type SMTAnnotation Word64 = ()
  getSortBase _ = bv (64::Integer)
  declareType _ _ = return ()
  
instance SMTType Int64 where
  type SMTAnnotation Int64 = ()
  getSortBase _ = bv (64::Integer)
  declareType _ _ = return ()

instance SMTValue Word64 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTValue Int64 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word64
instance SMTBV Int64

instance SMTOrd Word64 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTOrd Int64 where
  (.<.) = BVSLT
  (.<=.) = BVSLE
  (.>.) = BVSGT
  (.>=.) = BVSGE

instance Num (SMTExpr Word8) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = x
  signum _ = Const 1 ()

instance Num (SMTExpr Int8) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = ITE (BVSGE x (Const 0 ())) x (BVSub (Const 0 ()) x)
  signum x = ITE (BVSGE x (Const 0 ())) (Const 1 ()) (Const (-1) ())

instance Num (SMTExpr Word16) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = x
  signum _ = Const 1 ()

instance Num (SMTExpr Int16) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = ITE (BVSGE x (Const 0 ())) x (BVSub (Const 0 ()) x)
  signum x = ITE (BVSGE x (Const 0 ())) (Const 1 ()) (Const (-1) ())

instance Num (SMTExpr Word32) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = x
  signum _ = Const 1 ()

instance Num (SMTExpr Int32) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = ITE (BVSGE x (Const 0 ())) x (BVSub (Const 0 ()) x)
  signum x = ITE (BVSGE x (Const 0 ())) (Const 1 ()) (Const (-1) ())

instance Num (SMTExpr Word64) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = x
  signum _ = Const 1 ()

instance Num (SMTExpr Int64) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = ITE (BVSGE x (Const 0 ())) x (BVSub (Const 0 ()) x)
  signum x = ITE (BVSGE x (Const 0 ())) (Const 1 ()) (Const (-1) ())

-- Arguments

instance Args () where
  type ArgAnnotation () = ()
  foldExprs _ s _ _ = (s,())

instance (SMTType a) => Args (SMTExpr a) where
  type ArgAnnotation (SMTExpr a) = SMTAnnotation a
  foldExprs f = f

instance (Args a,Args b) => Args (a,b) where
  type ArgAnnotation (a,b) = (ArgAnnotation a,ArgAnnotation b)
  foldExprs f s ~(e1,e2) ~(ann1,ann2) = let ~(s1,e1') = foldExprs f s e1 ann1
                                            ~(s2,e2') = foldExprs f s1 e2 ann2
                                        in (s2,(e1',e2'))

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

instance (LiftArgs a,LiftArgs b,LiftArgs c,LiftArgs d) => LiftArgs (a,b,c,d) where
  type Unpacked (a,b,c,d) = (Unpacked a,Unpacked b,Unpacked c,Unpacked d)
  liftArgs (x1,x2,x3,x4) ~(a1,a2,a3,a4) = (liftArgs x1 a1,liftArgs x2 a2,liftArgs x3 a3,liftArgs x4 a4)
  unliftArgs (x1,x2,x3,x4) = do
    r1 <- unliftArgs x1
    r2 <- unliftArgs x2
    r3 <- unliftArgs x3
    r4 <- unliftArgs x4
    return (r1,r2,r3,r4)

instance Args a => Args [a] where
  type ArgAnnotation [a] = [ArgAnnotation a]
  foldExprs _ s _ [] = (s,[])
  foldExprs f s ~(x:xs) (ann:anns) = let (s',x') = foldExprs f s x ann
                                         (s'',xs') = foldExprs f s' xs anns
                                     in (s'',x':xs')

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
    declareType' (typeOf u)
      (declareDatatypes ["a"] [("Maybe",[("Nothing",[]),("Just",[("fromJust",L.Symbol "a")])])])
    where
      undef :: Maybe a -> a
      undef _ = undefined

instance SMTValue a => SMTValue (Maybe a) where
  unmangle (L.Symbol "Nothing") _ = return $ Just Nothing
  unmangle (L.List [L.Symbol "as"
                   ,L.Symbol "Nothing"
                   ,_]) _ = return $ Just Nothing
  unmangle (L.List [L.Symbol "Just"
                   ,res]) ann = do
    r <- unmangle res ann
    return (fmap Just r)
  unmangle _ _ = return Nothing
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
  declareType u ann = declareType (undefArg u) ann
  getSortBase _ = L.Symbol "List"

instance (Typeable a,SMTValue a) => SMTValue [a] where
  unmangle (L.Symbol "nil") _ = return $ Just []
  unmangle (L.List [L.Symbol "insert",h,t]) ann = do
    h' <- unmangle h ann
    t' <- unmangle t ann
    return (do
               hh <- h'
               tt <- t'
               return $ hh:tt)
  unmangle _ _ = return Nothing
  mangle [] _ = L.Symbol "nil"
  mangle (x:xs) ann = L.List [L.Symbol "insert"
                             ,mangle x ann
                             ,mangle xs ann]

-- Bitvector implementations for ByteString

-- | Encodes the length of a `ByteString` to be used as a type annotation.
newtype ByteStringLen = ByteStringLen Int deriving (Show,Eq,Ord,Num,Typeable)

instance SMTType BS.ByteString where
    type SMTAnnotation BS.ByteString = ByteStringLen
    getSort _ (ByteStringLen l) = bv (l*8)
    getSortBase _ = error "smtlib2: No getSortBase implementation for ByteString"
    declareType _ _ = return ()

instance SMTValue BS.ByteString where
    unmangle v (ByteStringLen l) = return $ fmap int2bs (getBVValue' (l*8) v)
        where
          int2bs :: Integer -> BS.ByteString
          int2bs cv = BS.pack $ fmap (\i -> fromInteger $ cv `shiftR` i) (reverse [0..(l-1)])
    mangle v (ByteStringLen l) = putBVValue' (l*8) (bs2int v)
        where
          bs2int :: BS.ByteString -> Integer
          bs2int = BS.foldl (\cv w -> (cv `shiftL` 8) .|. (fromIntegral w)) 0

instance Concatable BS.ByteString BS.ByteString where
    type ConcatResult BS.ByteString BS.ByteString = BS.ByteString
    concat' b1 _ b2 _ = BS.append b1 b2
    concatAnn _ _ = (+)

-- BitVector implementation

-- | A bitvector is a list of bits which can be used to represent binary numbers.
--   It is represented as an `Integer`, which represents the value of the bitvector.
newtype BitVector = BitVector Integer deriving (Eq,Ord,Num,Show,Typeable)

instance SMTType BitVector where
  type SMTAnnotation BitVector = Integer
  getSort _ l = bv l
  getSortBase _ = error "smtlib2: No getSortBase implementation for BitVector"
  declareType _ _ = return ()

instance SMTValue BitVector where
  unmangle v l = return $ fmap BitVector $ getBVValue' l v
  mangle (BitVector v) l = putBVValue' l v

instance Concatable BitVector BitVector where
  type ConcatResult BitVector BitVector = BitVector
  concat' (BitVector x) _ (BitVector y) l2 = BitVector $ (x `shiftL` (fromIntegral l2)) .|. y
  concatAnn _ _ = (+)

instance Concatable BitVector Word8 where
  type ConcatResult BitVector Word8 = BitVector
  concat' (BitVector x) _ w () = BitVector $ (x `shiftL` 8) .|. (fromIntegral w)
  concatAnn _ _ l () = l+8

instance Concatable BitVector Word16 where
  type ConcatResult BitVector Word16 = BitVector
  concat' (BitVector x) _ w () = BitVector $ (x `shiftL` 16) .|. (fromIntegral w)
  concatAnn _ _ l () = l+16

instance Concatable BitVector Word32 where
  type ConcatResult BitVector Word32 = BitVector
  concat' (BitVector x) _ w () = BitVector $ (x `shiftL` 32) .|. (fromIntegral w)
  concatAnn _ _ l () = l+32

instance Concatable BitVector Word64 where
  type ConcatResult BitVector Word64 = BitVector
  concat' (BitVector x) _ w () = BitVector $ (x `shiftL` 64) .|. (fromIntegral w)
  concatAnn _ _ l () = l+64

instance Extractable BitVector BitVector where
  extract' _ _ u l _ = u-l+1

instance Extractable BitVector Word8 where
  extract' _ _ _ _ _ = ()

instance Extractable BitVector Word16 where
  extract' _ _ _ _ _ = ()

instance Extractable BitVector Word32 where
  extract' _ _ _ _ _ = ()

instance Extractable BitVector Word64 where
  extract' _ _ _ _ _ = ()

instance SMTBV BitVector

-- Concat instances

instance Concatable Word8 Word8 where
    type ConcatResult Word8 Word8 = Word16
    concat' x _ y _ = ((fromIntegral x) `shiftL` 8) .|. (fromIntegral y)
    concatAnn _ _ _ _ = ()

instance Concatable Int8 Word8 where
    type ConcatResult Int8 Word8 = Int16
    concat' x _ y _ = ((fromIntegral x) `shiftL` 8) .|. (fromIntegral y)
    concatAnn _ _ _ _ = ()

instance Concatable Word16 Word16 where
    type ConcatResult Word16 Word16 = Word32
    concat' x _ y _ = ((fromIntegral x) `shiftL` 16) .|. (fromIntegral y)
    concatAnn _ _ _ _ = ()

instance Concatable Int16 Word16 where
    type ConcatResult Int16 Word16 = Int32
    concat' x _ y _ = ((fromIntegral x) `shiftL` 16) .|. (fromIntegral y)
    concatAnn _ _ _ _ = ()

instance Concatable Word32 Word32 where
    type ConcatResult Word32 Word32 = Word64
    concat' x _ y _ = ((fromIntegral x) `shiftL` 32) .|. (fromIntegral y)
    concatAnn _ _ _ _ = ()

instance Concatable Int32 Word32 where
    type ConcatResult Int32 Word32 = Int64
    concat' x _ y _ = ((fromIntegral x) `shiftL` 32) .|. (fromIntegral y)
    concatAnn _ _ _ _ = ()

-- Extract instances
instance Extractable Word16 Word8 where
    extract' _ _ _ _ _ = ()
instance Extractable Word32 Word16 where
    extract' _ _ _ _ _ = ()
instance Extractable Word32 Word8 where
    extract' _ _ _ _ _ = ()
instance Extractable Word64 Word32 where
    extract' _ _ _ _ _ = ()
instance Extractable Word64 Word16 where
    extract' _ _ _ _ _ = ()
instance Extractable Word64 Word8 where
    extract' _ _ _ _ _ = ()