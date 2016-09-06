module Language.SMTLib2.Composite.Singleton where

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Composite.Class hiding (defaultEq)
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Null

import Data.GADT.Compare
import Data.GADT.Show
import Control.Lens
import Data.Maybe
import Data.Constraint

newtype Comp (tp :: Type) e = Comp { _comp :: e tp }

makeLenses ''Comp

instance Composite (Comp tp) where
  type RevComp (Comp tp) = (:~:) tp
  foldExprs f (Comp e) = do
    ne <- f Refl e
    return (Comp ne)
  accessComposite Refl = maybeLens comp
  compCombine f (Comp x) (Comp y) = fmap (Just . Comp) $ f x y
  compCompare (Comp x) (Comp y) = defaultCompare x y
  compShow p (Comp x) = gshowsPrec p x

instance CompositeExtract (Comp tp) where
  type CompExtract (Comp tp) = Value tp
  compExtract f (Comp e) = f e

instance GShow e => Show (Comp tp e) where
  showsPrec p (Comp e) = gshowsPrec p e

compDescr :: Repr tp -> CompDescr (Comp tp)
compDescr = Comp

instance IsSingleton (Comp tp) where
  type SingletonType (Comp tp) = tp
  getSingleton = pure._comp

instance IsConstant (Comp tp)
instance IsRanged (Comp tp)

instance IsNumeric (Comp IntType) where
  compositeFromValue = fmap Comp . constant
  compositePlus (Comp x) (Comp y) = fmap Comp (x .+. y)
  compositeMinus (Comp x) (Comp y) = fmap Comp (x .-. y)
  compositeSum = fmap Comp . plus . fmap _comp
  compositeMult (Comp x) (Comp y) = fmap Comp (x .*. y)
  compositeGEQ (Comp x) (Comp y) = x .>=. y

instance IsNatural bw => IsNumeric (Comp (BitVecType bw)) where
  compositeFromValue = fmap Comp . constant
  compositePlus (Comp x) (Comp y) = fmap Comp $ bvadd x y
  compositeMinus (Comp x) (Comp y) = fmap Comp $ bvsub x y
  compositeMult (Comp x) (Comp y) = fmap Comp $ bvmul x y
  compositeGEQ (Comp x) (Comp y) = bvsge x y

instance IsNumeric idx => ByteWidth (Comp (BitVecType bw)) idx where
  byteWidth (Comp e) = do
    tp <- embedTypeOf
    case tp e of
      BitVecRepr bw -> compositeFromValue (fromInteger (naturalToInteger bw `div` 8))

instance StaticByteWidth (Comp (BitVecType bw)) where
  staticByteWidth (Comp e) = case getType e of
    BitVecRepr bw -> naturalToInteger bw `div` 8

data CompBV e = forall bw. CompBV { _compBV :: e (BitVecType bw) }

makeLenses ''CompBV

data RevBV tp where
  RevBV :: Natural bw -> RevBV (BitVecType bw)

instance GEq RevBV where
  geq (RevBV x) (RevBV y) = do
    Refl <- geq x y
    return Refl

instance GCompare RevBV where
  gcompare (RevBV x) (RevBV y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

deriving instance Show (RevBV tp)
instance GShow RevBV where
  gshowsPrec = showsPrec

instance Composite CompBV where
  type RevComp CompBV = RevBV
  foldExprs f (CompBV e) = case getType e of
    BitVecRepr bw -> do
      ne <- f (RevBV bw) e
      return $ CompBV ne
  accessComposite (RevBV bw) = lens (\(CompBV e) -> case getType e of
                                        BitVecRepr bw' -> do
                                          Refl <- geq bw bw'
                                          return e)
                               (\_ new -> Just $ CompBV new)
  compCombine f (CompBV e1) (CompBV e2) = case geq (getType e1) (getType e2) of
    Just Refl -> do
      ne <- f e1 e2
      return $ Just $ CompBV ne
    Nothing -> return Nothing
  compCompare (CompBV e1) (CompBV e2) = defaultCompare e1 e2
  compShow p (CompBV e) = gshowsPrec p e

instance IsNumeric i => ByteWidth CompBV i where
  byteWidth (CompBV e) = do
    tp <- embedTypeOf
    case tp e of
      BitVecRepr bw -> compositeFromValue (fromInteger (naturalToInteger bw `div` 8))

instance (IsRanged i,IsNumeric i,Integral (Value (SingletonType i)))
         => ByteAccess (Comp (BitVecType bw)) i CompBV where
  byteRead = fromStaticByteRead
  byteWrite = fromStaticByteWrite

instance StaticByteAccess (Comp (BitVecType bw)) CompBV where
  staticByteRead (Comp e) off len = do
    tp <- embedTypeOf
    case tp e of
      BitVecRepr bw -> reifyNat (fromInteger off) $
        \roff -> reifyNat (fromInteger len) $
        \rlen -> case naturalLEQ (naturalAdd roff rlen) bw of
          Just Dict -> case naturalLEQ roff bw of -- Redundant, but neccessary for the typechecker
            Just Dict -> do
              split <- splitBV roff rlen e
              return $ Just $ CompBV $ splitBVGet split
          Nothing -> return Nothing
  staticByteWrite (Comp trg) off (CompBV src) = reifyNat (fromInteger off) $
    \roff -> do
      ntrg <- bvWrite roff src trg
      return $ fmap Comp ntrg

data BVSplit start len size e where
  NoSplit   :: e (BitVecType size) -> BVSplit Z size size e
  NoPrefix  :: e (BitVecType len) -> e (BitVecType diff) -> BVSplit Z len (len+diff) e
  NoPostfix :: e (BitVecType start) -> e (BitVecType len) -> BVSplit start len (start+len) e
  Split     :: e (BitVecType start) -> e (BitVecType len) -> e (BitVecType diff)
            -> BVSplit start len (start + len + diff) e

bvWrite :: (Embed m e,Monad m) => Natural start
        -> e (BitVecType src)
        -> e (BitVecType trg)
        -> m (Maybe (e (BitVecType trg)))
bvWrite (off :: Natural start) (src :: e (BitVecType src)) (trg :: e (BitVecType trg)) = do
  tp <- embedTypeOf
  case tp src of
    BitVecRepr (srcSize :: Natural src) -> do
      split <- splitBVMaybe off srcSize trg
      case split of
        Nothing -> return Nothing
        Just split' -> do
          ntrg <- unsplitBV (splitBVSet split' src)
          return $ Just ntrg
            
splitBVMaybe :: (Embed m e,Monad m)
             => Natural start -> Natural len -> e (BitVecType size)
             -> m (Maybe (BVSplit start len size e))
splitBVMaybe start len e = do
  tp <- embedTypeOf
  case tp e of
    BitVecRepr size -> case naturalLEQ (naturalAdd start len) size of
      Just Dict -> case naturalLEQ start size of
        Just Dict -> fmap Just $ splitBV start len e
      Nothing -> return Nothing

splitBV :: (Embed m e,Monad m,(start + len <= size) ~ True,(start <= size) ~ True)
        => Natural start -> Natural len -> e (BitVecType size)
        -> m (BVSplit start len size e)
splitBV start len e = do
  tp <- embedTypeOf
  case tp e of
    BitVecRepr size
      -> case start of
           Zero -> case geq len size of
             Just Refl -> return $ NoSplit e
             Nothing -> case naturalLEQ size size of -- XXX: This should be obvious, but not to the typechecker
               Just Dict -> naturalSub' size len $
                            \diff -> do
                              obj <- extract' Zero len e
                              post <- extract' len diff e
                              return $ NoPrefix obj post
           _ -> case geq (naturalAdd start len) size of
             Just Refl -> do
               pre <- extract' Zero start e
               obj <- extract' start len e
               return $ NoPostfix pre obj
             Nothing -> naturalSub' size (naturalAdd start len) $
               \diff -> case naturalLEQ size size of -- XXX: See above
                 Just Dict -> do
                   pre <- extract' Zero start e
                   obj <- extract' start len e
                   post <- extract' (naturalAdd start len) diff e
                   return $ Split pre obj post

unsplitBV :: (Embed m e,Monad m) => BVSplit start len size e -> m (e (BitVecType size))
unsplitBV (NoSplit x) = return x
unsplitBV (NoPrefix x post) = concat' x post
unsplitBV (NoPostfix pre x) = concat' pre x
unsplitBV (Split pre x post) = concat' (concat' pre x) post

splitBVGet :: BVSplit start len size e -> e (BitVecType len)
splitBVGet (NoSplit x) = x
splitBVGet (NoPrefix x _) = x
splitBVGet (NoPostfix _ x) = x
splitBVGet (Split _ x _) = x

splitBVSet :: BVSplit start len size e -> e (BitVecType len) -> BVSplit start len size e
splitBVSet (NoSplit _) x = NoSplit x
splitBVSet (NoPrefix _ post) x = NoPrefix x post
splitBVSet (NoPostfix pre _) x = NoPostfix pre x
splitBVSet (Split pre _ post) x = Split pre x post

{-data BVSplitRest start len size e where
  NoRest    :: BVSplit start len size e -> BVSplitRest start len size e
  SplitRest :: BVSplit start len size e -> Natural rest -> BVSplitRest start (len + rest) size e

data BoundedNat x y where
  InBound  :: ((x <= y) ~ True) => BoundedNat x y
  OutBound :: ((y + diff) ~ x) => Natural diff -> BoundedNat x y

boundedNat :: Natural x -> Natural y -> BoundedNat x y
boundedNat Zero _ = InBound
boundedNat (Succ n) (Succ m) = case boundedNat n m of
  InBound -> InBound
  OutBound diff -> OutBound diff
boundedNat (Succ n) Zero = OutBound (Succ n)

splitBVRest :: (Embed m e,Monad m,(start <= size) ~ True)
            => Natural start -> Natural len -> e (BitVecType size)
            -> m (BVSplitRest start len size e)
splitBVRest start len e = do
  tp <- embedTypeOf
  case tp e of
    BitVecRepr size
      -> case boundedNat (naturalAdd start len) size of
      InBound -> do
        split <- splitBV start len e
        return $ NoRest split
      OutBound diff -> naturalSub' size start $
                       \rlen -> case naturalLEQ size size of
                         Just Dict -> do
                           split <- splitBV start rlen e
                           return $ SplitRest split diff-}
{-      case naturalLEQ (naturalAdd start len) size of
      Just Dict -> do
        split <- splitBV start len e
        return $ NoRest split
      Nothing -> naturalSub' (naturalAdd start len) size $
                 \rest -> naturalSub' size start $
                 \rlen -> case naturalLEQ size size of
                   Just Dict -> do
                     split <- splitBV start rlen e
                     return $ SplitRest split rest-}

--instance (IsRanged idx,IsNumeric idx,Integral (Value (SingletonType idx)))
--         => ByteAccess (Comp


{-instance (IsRanged idx,IsNumeric idx,Integral (Value (SingletonType idx)))
         => ByteAccess (Comp (BitVecType bw)) idx where
  byteRead (Comp e) idx sz = do
    tp <- embedTypeOf
    case tp e of
      BitVecRepr bw -> do
        rangeStart <- getRange idx
        rangeSize <- getRange sz
        let allRange = rangeFromTo (fromInteger 0) (fromInteger (naturalToInteger bw `div` 8))
            rangeStart' = intersectionRange rangeStart allRange
            rangeSize' = intersectionRange rangeSize allRange
            vbw = fromInteger (naturalToInteger bw `div` 8)
        case asFiniteRange rangeStart' of
          Just starts -> case asFiniteRange rangeSize' of
            Just sizes -> do
              mbReads <- sequence [ do
                                      cond1 <- getSingleton idx .==. constant start
                                      cond2 <- getSingleton sz .==. constant size
                                      cond <- cond1 .&. cond2
                                      if start==0 && size==vbw
                                        then return $ Just $ ByteRead (Comp e) cond
                                        else reifyNat (fromIntegral start) $
                                             \rstart -> reifyNat (fromIntegral size) $
                                             \rsize -> return Nothing -- XXX: Implement this
                                  | start <- starts, size <- sizes ]
              return $ Just $ catMaybes mbReads
            Nothing -> return Nothing
          Nothing -> return Nothing
  byteWrite (Comp e) idx -}
