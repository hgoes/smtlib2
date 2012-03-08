{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,TemplateHaskell,RankNTypes,TypeFamilies,GeneralizedNewtypeDeriving #-}
module Language.SMTLib2.Internals.Instances where

import Language.SMTLib2.Internals
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
import qualified Data.Bitstream as BitS

-- Bool

instance SMTType Bool where
  type SMTAnnotation Bool = ()
  getSort _ _ = L.Symbol "Bool"
  declareType u _ = [(typeOf u,return ())]

instance SMTValue Bool where
  unmangle (L.Symbol "true") _ = return $ Just True
  unmangle (L.Symbol "false") _ = return $ Just False
  unmangle _ _ = return Nothing
  mangle True _ = L.Symbol "true"
  mangle False _ = L.Symbol "false"

-- Integer

instance SMTType Integer where
  type SMTAnnotation Integer = ()
  getSort _ _ = L.Symbol "Int"
  declareType u _ = [(typeOf u,return ())]

instance SMTValue Integer where
  unmangle (L.Number (L.I v)) _ = return $ Just v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) _ = return $ Just $ - v
  unmangle e _ = return Nothing
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
  getSort _ _ = L.Symbol "Real"
  declareType u _ = [(typeOf u,return ())]

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
  declareType u (anni,annv) = [(mkTyConApp (mkTyCon "Data.Array.Array") [],return ())] ++
                              declareArgTypes (getIdx u) anni ++
                              declareType (getVal u) annv
    where
      getIdx :: SMTArray i v -> i
      getIdx _ = undefined
      getVal :: SMTArray i v -> v
      getVal _ = undefined

-- BitVectors

bv :: Int -> L.Lisp
bv n = L.List [L.Symbol "_"
              ,L.Symbol "BitVec"
              ,L.Number $ L.I (fromIntegral n)]

instance SMTType Word8 where
  type SMTAnnotation Word8 = ()
  getSort _ _ = bv 8
  declareType u _ = [(typeOf u,return ())]

instance SMTType Int8 where
  type SMTAnnotation Int8 = ()
  getSort _ _ = bv 8
  declareType u _ = [(typeOf u,return ())]

withUndef1 :: (a -> g a) -> g a
withUndef1 f = f undefined

getBVValue :: (Num a,Bits a,Read a) => L.Lisp -> b -> SMT (Maybe a)
getBVValue arg _ = return $ withUndef1 $ \u -> getBVValue' (fromIntegral $ bitSize u) arg

getBVValue' :: (Num a,Bits a,Read a) => Int -> L.Lisp -> Maybe a
getBVValue' _ (L.Number (L.I v)) = Just (fromInteger v)
getBVValue' len (L.Symbol s) = case T.unpack s of
  '#':'b':rest -> if Prelude.length rest == len
                  then (case readInt 2
                                 (\x -> x=='0' || x=='1')
                                 (\x -> if x=='0' then 0 else 1) 
                                 rest of
                          [(v,_)] -> Just v
                          _ -> Nothing)
                  else Nothing
  '#':'x':rest -> if (Prelude.length rest,0) == (len `divMod` 4)
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

putBVValue :: (Bits a,Ord a,Integral a) => a -> b -> L.Lisp
putBVValue x _ = putBVValue' (fromIntegral $ bitSize x) x

putBVValue' :: (Bits a,Ord a,Integral a) => Int -> a -> L.Lisp
putBVValue' len x
  | len `mod` 4 == 0 = let v' = if x < 0
                                then complement (x-1)
                                else x
                           enc = showHex v' "" 
                           l = Prelude.length enc
                       in L.Symbol $ T.pack $ '#':'x':((Prelude.replicate ((len `div` 4)-l) '0')++enc)
  | otherwise = L.Symbol (T.pack ('#':'b':[ if testBit x i
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
  getSort _ _ = bv 16
  declareType u _ = [(typeOf u,return ())]

instance SMTType Int16 where
  type SMTAnnotation Int16 = ()
  getSort _ _ = bv 16
  declareType u _ = [(typeOf u,return ())]

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
  getSort _ _ = bv 32
  declareType u _ = [(typeOf u,return ())]

instance SMTType Int32 where
  type SMTAnnotation Int32 = ()
  getSort _ _ = bv 32
  declareType u _ = [(typeOf u,return ())]

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
  getSort _ _ = bv 64
  declareType u _ = [(typeOf u,return ())]
  
instance SMTType Int64 where
  type SMTAnnotation Int64 = ()
  getSort _ _ = bv 64
  declareType u _ = [(typeOf u,return ())]

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
  signum x = Const 1 ()

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
  signum x = Const 1 ()

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
  signum x = Const 1 ()

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
  signum x = Const 1 ()

instance Num (SMTExpr Int64) where
  fromInteger x = Const (fromInteger x) ()
  (+) = BVAdd
  (-) = BVSub
  (*) = BVMul
  abs x = ITE (BVSGE x (Const 0 ())) x (BVSub (Const 0 ()) x)
  signum x = ITE (BVSGE x (Const 0 ())) (Const 1 ()) (Const (-1) ())

-- Arguments

instance (SMTType a,SMTAnnotation a ~ ()) => Args (SMTExpr a) where
  type Unpacked (SMTExpr a) = a
  type ArgAnnotation (SMTExpr a) = SMTAnnotation a
  foldExprs f s x = f s x

instance (Args a,Args b) => Args (a,b) where
  type Unpacked (a,b) = (Unpacked a,Unpacked b)
  type ArgAnnotation (a,b) = (ArgAnnotation a,ArgAnnotation b)
  foldExprs f s ~(e1,e2) ~(ann1,ann2) = let ~(s1,e1') = foldExprs f s e1 ann1
                                            ~(s2,e2') = foldExprs f s1 e2 ann2
                                        in (s2,(e1',e2'))

instance (LiftArgs a,LiftArgs b) => LiftArgs (a,b) where
  liftArgs (x,y) = (liftArgs x,liftArgs y)
  unliftArgs (x,y) = do
    rx <- unliftArgs x
    ry <- unliftArgs y
    return (rx,ry)

instance (Args a,Args b,Args c) => Args (a,b,c) where
  type Unpacked (a,b,c) = (Unpacked a,Unpacked b,Unpacked c)
  type ArgAnnotation (a,b,c) = (ArgAnnotation a,ArgAnnotation b,ArgAnnotation c)
  foldExprs f s ~(e1,e2,e3) ~(ann1,ann2,ann3) = let ~(s1,e1') = foldExprs f s e1 ann1
                                                    ~(s2,e2') = foldExprs f s1 e2 ann2
                                                    ~(s3,e3') = foldExprs f s2 e3 ann3
                                                in (s3,(e1',e2',e3'))

instance (LiftArgs a,LiftArgs b,LiftArgs c) => LiftArgs (a,b,c) where
  liftArgs (x,y,z) = (liftArgs x,liftArgs y,liftArgs z)
  unliftArgs (x,y,z) = do
    rx <- unliftArgs x
    ry <- unliftArgs y
    rz <- unliftArgs z
    return (rx,ry,rz)

instance SMTType a => SMTType (Maybe a) where
  type SMTAnnotation (Maybe a) = SMTAnnotation a
  getSort u ann = L.List [L.Symbol "Maybe",getSort (undef u) ann]
    where
      undef :: Maybe a -> a
      undef _ = undefined
  declareType u ann = let rec = declareType (undef u) ann
                      in [(mkTyConApp (mkTyCon "Maybe") [],
                           declareDatatypes ["a"] [("Maybe",[("Nothing",[]),("Just",[("fromJust",L.Symbol "a")])])])] ++
                                        rec
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

undefArg :: b a -> a
undefArg _ = undefined

instance (Typeable a,SMTType a) => SMTType [a] where
  type SMTAnnotation [a] = SMTAnnotation a
  getSort u ann = L.List [L.Symbol "List",getSort (undefArg u) ann]
  declareType u ann = (typeOf u,return ()):declareType (undefArg u) ann

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
newtype ByteStringLen = ByteStringLen Int deriving (Show,Eq,Ord,Num)

instance SMTType BS.ByteString where
    type SMTAnnotation BS.ByteString = ByteStringLen
    getSort _ (ByteStringLen l) = bv (l*8)
    declareType u _ = [(typeOf u,return ())]

instance SMTValue BS.ByteString where
    unmangle v (ByteStringLen l) = return $ fmap (int2bs l) (getBVValue' (l*8) v)
        where
          int2bs :: Int -> Integer -> BS.ByteString
          int2bs l v = BS.pack $ fmap (\i -> fromInteger $ v `shiftR` i) (reverse [0..(l-1)])
    mangle v (ByteStringLen l) = putBVValue' (l*8) (bs2int v)
        where
          bs2int :: BS.ByteString -> Integer
          bs2int = BS.foldl (\v w -> (v `shiftL` 8) .|. (fromIntegral w)) 0

instance Concatable ByteStringLen ByteStringLen where
    type ConcatResult ByteStringLen ByteStringLen = ByteStringLen
    concat' (ByteStringLen l1) (ByteStringLen l2) = ByteStringLen (l1+l2)

instance Concatable BS.ByteString BS.ByteString where
    type ConcatResult BS.ByteString BS.ByteString = BS.ByteString
    concat' b1 b2 = BS.append b1 b2

-- BitStream implementation

newtype BitstreamLen = BitstreamLen Int deriving (Show,Eq,Ord,Num)

instance SMTType (BitS.Bitstream BitS.Left) where
    type SMTAnnotation (BitS.Bitstream BitS.Left) = BitstreamLen
    getSort _ (BitstreamLen l) = bv l
    declareType u _ = [(typeOf u,return ())]

instance SMTType (BitS.Bitstream BitS.Right) where
    type SMTAnnotation (BitS.Bitstream BitS.Right) = BitstreamLen
    getSort _ (BitstreamLen l) = bv l
    declareType u _ = [(typeOf u,return ())]

instance SMTValue (BitS.Bitstream BitS.Left) where
    unmangle v (BitstreamLen l) = return $ fmap (BitS.fromNBits l) (getBVValue' l v :: Maybe Integer)
    mangle v (BitstreamLen l) = putBVValue' l (BitS.toBits v :: Integer)

instance SMTValue (BitS.Bitstream BitS.Right) where
    unmangle v (BitstreamLen l) = return $ fmap (BitS.fromNBits l) (getBVValue' l v :: Maybe Integer)
    mangle v (BitstreamLen l) = putBVValue' l (BitS.toBits v :: Integer)

instance Concatable BitstreamLen BitstreamLen where
    type ConcatResult BitstreamLen BitstreamLen = BitstreamLen
    concat' (BitstreamLen l1) (BitstreamLen l2) = BitstreamLen (l1+l2)

instance Concatable (BitS.Bitstream BitS.Left) (BitS.Bitstream BitS.Left) where
    type ConcatResult (BitS.Bitstream BitS.Left) (BitS.Bitstream BitS.Left) = BitS.Bitstream BitS.Left
    concat' = BitS.append

instance Concatable (BitS.Bitstream BitS.Right) (BitS.Bitstream BitS.Right) where
    type ConcatResult (BitS.Bitstream BitS.Right) (BitS.Bitstream BitS.Right) = BitS.Bitstream BitS.Right
    concat' = BitS.append

instance Extractable (BitS.Bitstream BitS.Left) (BitS.Bitstream BitS.Left) where
    extract' _ _ u l _ = BitstreamLen (fromIntegral $ u-l+1)
instance Extractable (BitS.Bitstream BitS.Right) (BitS.Bitstream BitS.Right) where
    extract' _ _ u l _ = BitstreamLen (fromIntegral $ u-l+1)

-- Concat instances

instance Concatable () () where
    type ConcatResult () () = ()
    concat' _ _ = ()

instance Concatable Word8 Word8 where
    type ConcatResult Word8 Word8 = Word16
    concat' x y = ((fromIntegral x) `shiftL` 8) .|. (fromIntegral y)

instance Concatable Int8 Word8 where
    type ConcatResult Int8 Word8 = Int16
    concat' x y = ((fromIntegral x) `shiftL` 8) .|. (fromIntegral y)

instance Concatable Word16 Word16 where
    type ConcatResult Word16 Word16 = Word32
    concat' x y = ((fromIntegral x) `shiftL` 16) .|. (fromIntegral y)

instance Concatable Int16 Word16 where
    type ConcatResult Int16 Word16 = Int32
    concat' x y = ((fromIntegral x) `shiftL` 16) .|. (fromIntegral y)

instance Concatable Word32 Word32 where
    type ConcatResult Word32 Word32 = Word64
    concat' x y = ((fromIntegral x) `shiftL` 32) .|. (fromIntegral y)

instance Concatable Int32 Word32 where
    type ConcatResult Int32 Word32 = Int64
    concat' x y = ((fromIntegral x) `shiftL` 32) .|. (fromIntegral y)

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