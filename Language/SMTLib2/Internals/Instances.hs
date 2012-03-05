{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,TemplateHaskell,RankNTypes,TypeFamilies,GeneralizedNewtypeDeriving #-}
module Language.SMTLib2.Internals.Instances where

import Language.SMTLib2.Internals
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Array
import Data.Word
import Data.Int
import Numeric
import Data.Bits
import qualified Data.Text as T
import Data.Ratio
import Data.Typeable
import qualified Data.ByteString as BS

-- Bool

instance SMTType Bool where
  type SMTAnnotation Bool = ()
  getSort _ _ = L.Symbol "Bool"
  declareType u = [(typeOf u,return ())]

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
  declareType u = [(typeOf u,return ())]

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
  declareType u = [(typeOf u,return ())]

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

instance (Ix idx,SMTType idx,SMTType val) => SMTType (Array idx val) where
  type SMTAnnotation (Array idx val) = (SMTAnnotation idx,SMTAnnotation val)
  getSort u (anni,annv) = L.List [L.Symbol "Array"
                         ,getSort (getIdx u) anni
                         ,getSort (getVal u) annv]
    where
      getIdx :: Array i v -> i
      getIdx _ = undefined
      getVal :: Array i v -> v
      getVal _ = undefined
  declareType u = [(mkTyConApp (mkTyCon "Data.Array.Array") [],return ())] ++
                  declareType (getIdx u) ++
                  declareType (getVal u)
    where
      getIdx :: Array i v -> i
      getIdx _ = undefined
      getVal :: Array i v -> v
      getVal _ = undefined


-- BitVectors

bv :: Int -> L.Lisp
bv n = L.List [L.Symbol "_"
              ,L.Symbol "BitVec"
              ,L.Number $ L.I (fromIntegral n)]

instance SMTType Word8 where
  type SMTAnnotation Word8 = ()
  getSort _ _ = bv 8
  declareType u = [(typeOf u,return ())]

instance SMTType Int8 where
  type SMTAnnotation Int8 = ()
  getSort _ _ = bv 8
  declareType u = [(typeOf u,return ())]

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
  declareType u = [(typeOf u,return ())]

instance SMTType Int16 where
  type SMTAnnotation Int16 = ()
  getSort _ _ = bv 16
  declareType u = [(typeOf u,return ())]

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
  declareType u = [(typeOf u,return ())]

instance SMTType Int32 where
  type SMTAnnotation Int32 = ()
  getSort _ _ = bv 32
  declareType u = [(typeOf u,return ())]

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
  declareType u = [(typeOf u,return ())]
  
instance SMTType Int64 where
  type SMTAnnotation Int64 = ()
  getSort _ _ = bv 64
  declareType u = [(typeOf u,return ())]

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
  createArgs c = let n1 = T.pack $ "f"++show c
                     v1 = Var n1 ()
                     t1 = getSort (getUndef v1) ()
                 in (v1,[(n1,t1)],c+1)
  unpackArgs f e _ c = let (e',c') = f e c
                       in ([e'],c)
  foldExprs f s x = f s x
  allOf x = x

instance (SMTType a,SMTType b,SMTAnnotation a ~ (),SMTAnnotation b ~ ()) => Args (SMTExpr a,SMTExpr b) where
  type Unpacked (SMTExpr a,SMTExpr b) = (a,b)
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     v1 = Var n1 ()
                     v2 = Var n2 ()
                     t1 = getSort (getUndef v1) ()
                     t2 = getSort (getUndef v2) ()
                 in ((v1,v2),[(n1,t1),(n2,t2)],c+2)
  unpackArgs f (e1,e2) _ c = let (r1,c1) = f e1 c
                                 (r2,c2) = f e2 c1
                             in ([r1,r2],c2)
  foldExprs f s (e1,e2) = let (s1,e1') = f s e1
                              (s2,e2') = f s1 e2
                          in (s2,(e1',e2'))
  allOf x = (x,x)

instance (SMTType a,SMTType b,SMTType c,SMTAnnotation a ~ (),SMTAnnotation b ~ (),SMTAnnotation c ~ ()) => Args (SMTExpr a,SMTExpr b,SMTExpr c) where
  type Unpacked (SMTExpr a,SMTExpr b,SMTExpr c) = (a,b,c)
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     n3 = T.pack $ "f"++show (c+2)
                     v1 = Var n1 ()
                     v2 = Var n2 ()
                     v3 = Var n3 ()
                     t1 = getSort (getUndef v1) ()
                     t2 = getSort (getUndef v2) ()
                     t3 = getSort (getUndef v3) ()
                 in ((v1,v2,v3),[(n1,t1),(n2,t2),(n3,t3)],c+3)
  unpackArgs f (e1,e2,e3) _ c = let (r1,c1) = f e1 c
                                    (r2,c2) = f e2 c1
                                    (r3,c3) = f e3 c2
                              in ([r1,r2,r3],c3)
  foldExprs f s (e1,e2,e3) = let (s1,e1') = f s e1
                                 (s2,e2') = f s1 e2
                                 (s3,e3') = f s2 e3
                             in (s3,(e1',e2',e3'))
  allOf x = (x,x,x)

instance SMTType a => SMTType (Maybe a) where
  type SMTAnnotation (Maybe a) = SMTAnnotation a
  getSort u ann = L.List [L.Symbol "Maybe",getSort (undef u) ann]
    where
      undef :: Maybe a -> a
      undef _ = undefined
  declareType u = let rec = declareType (undef u)
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
  declareType u = (typeOf u,return ()):declareType (undefArg u)

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
    declareType u = [(typeOf u,return ())]

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