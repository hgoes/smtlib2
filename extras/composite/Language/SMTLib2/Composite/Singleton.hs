module Language.SMTLib2.Composite.Singleton where

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Composite.Class hiding (defaultEq)
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Null

import Data.GADT.Compare
import Data.GADT.Show
import Data.Maybe
import Data.Constraint
import qualified Data.Map as Map
import Data.Foldable

newtype Comp (tp :: Type) e = Comp { comp :: e tp }

instance Composite (Comp tp) where
  type RevComp (Comp tp) = (:~:) tp
  foldExprs f (Comp e) = do
    ne <- f Refl e
    return (Comp ne)
  getRev Refl (Comp x) = Just x
  setRev Refl x _ = Just (Comp x)
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
  getSingleton = pure.comp
  compositeFromValue = fmap Comp . constant

instance IsConstant (Comp tp)
instance IsRanged (Comp tp)

instance IsNumeric (Comp BoolType) where
  compositeFromInteger 0 _ = Just $ Comp (BoolValue False)
  compositeFromInteger 1 _ = Just $ Comp (BoolValue True)
  compositeFromInteger _ _ = Nothing
  compositePlus _ _ = return Nothing
  compositeMinus _ _ = return Nothing
  compositeSum _ = return Nothing
  compositeMult _ _ = return Nothing
  compositeGEQ _ _ = return Nothing
  compositeDiv _ _ = return Nothing
  compositeMod _ _ = return Nothing

instance IsNumeric (Comp IntType) where
  compositeFromInteger i _ = Just $ Comp (IntValue i)
  compositeToInteger (Comp (IntValue i)) = i
  compositePlus (Comp x) (Comp y) = fmap (Just . Comp) (x .+. y)
  compositeMinus (Comp x) (Comp y) = fmap (Just . Comp) (x .-. y)
  compositeSum = fmap (Just . Comp) . plus . fmap comp
  compositeMult (Comp x) (Comp y) = fmap (Just . Comp) (x .*. y)
  compositeGEQ (Comp x) (Comp y) = fmap Just $ x .>=. y
  compositeDiv (Comp x) (Comp y) = fmap (Just . Comp) $ div' x y
  compositeMod (Comp x) (Comp y) = fmap (Just . Comp) $ mod' x y

instance IsNumSingleton (Comp IntType)

instance IsNatural bw => IsNumeric (Comp (BitVecType bw)) where
  compositeFromInteger i (Comp (BitVecRepr bw)) = Just $ Comp (BitVecValue i bw)
  compositeToInteger (Comp (BitVecValue i _)) = i
  compositePlus (Comp x) (Comp y) = fmap (Just . Comp) $ bvadd x y
  compositeMinus (Comp x) (Comp y) = fmap (Just . Comp) $ bvsub x y
  compositeMult (Comp x) (Comp y) = fmap (Just . Comp) $ bvmul x y
  compositeGEQ (Comp x) (Comp y) = fmap Just $ bvsge x y

instance (IsSingleton idx,Integral (Value (SingletonType idx)),IsNumeric idx) => ByteWidth (Comp (BitVecType bw)) idx where
  byteWidth (Comp e) r = do
    tp <- embedTypeOf
    case tp e of
      BitVecRepr bw -> let Just bw' = compositeFromInteger
                                      (naturalToInteger bw `div` 8) r
                       in foldExprs (const constant) bw'

instance StaticByteWidth (Comp (BitVecType bw)) where
  staticByteWidth (Comp e) = case getType e of
    BitVecRepr bw -> naturalToInteger bw `div` 8

data CompBV e = forall bw. CompBV { compBV :: e (BitVecType bw)
                                  , compBVWidth :: !Integer }

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
  foldExprs f (CompBV e w) = case getType e of
    BitVecRepr bw -> do
      ne <- f (RevBV bw) e
      return $ CompBV ne w
  getRev (RevBV bw) (CompBV e _) = case getType e of
    BitVecRepr bw' -> do
      Refl <- geq bw bw'
      return e
  setRev (RevBV bw) e _ = Just (CompBV e (naturalToInteger bw))
  compCombine f (CompBV e1 w) (CompBV e2 _) = case geq (getType e1) (getType e2) of
    Just Refl -> do
      ne <- f e1 e2
      return $ Just $ CompBV ne w
    Nothing -> return Nothing
  compCompare (CompBV e1 _) (CompBV e2 _) = defaultCompare e1 e2
  compShow p (CompBV e _) = gshowsPrec p e

instance (IsNumSingleton i) => ByteWidth CompBV i where
  byteWidth (CompBV _ w) r = foldExprs (const constant) bw
    where
      Just bw = compositeFromInteger (w `div` 8) r

instance (IsRanged i,IsNumSingleton i)
         => ByteAccess (Comp (BitVecType bw)) i CompBV where
  byteRead = fromStaticByteRead
  byteWrite = fromStaticByteWrite

instance CanConcat CompBV where
  compConcat (x:xs) = do
    res <- foldlM (\(CompBV cur wcur) (CompBV n wn) -> do
                      r <- concat' cur n
                      return $ CompBV r (wcur+wn)) x xs
    return $ Just res

instance StaticByteAccess (Comp (BitVecType bw)) CompBV where
  staticByteRead (Comp e :: Comp (BitVecType bw) e) off len = do
    tp <- embedTypeOf
    case tp e of
      BitVecRepr bw -> do
        let bw' = naturalToInteger bw
            (len',over) = if off+bw' > len
                          then (bw'-off,Just $ len-(bw'-off))
                          else (len,Nothing)
        if off >= bw'
          then return Nothing
          else reifyNat (fromInteger off) $
               \roff -> reifyNat (fromInteger len') $
               \rlen -> case naturalLEQ (naturalAdd roff rlen) bw of
                 Just Dict -> case naturalLEQ roff bw of -- Redundant, but neccessary for the typechecker
                   Just Dict -> do
                     split <- splitBV roff rlen e
                     let result = CompBV (splitBVGet split) len'
                     case over of
                       Nothing -> return $ Just (result,0)
                       Just ov -> return $ Just (result,ov)
  staticByteWrite (Comp trg :: Comp (BitVecType bw) e) off (CompBV src wsrc) = do
    tp <- embedTypeOf
    case tp src of
      BitVecRepr srcWidth -> do
          let srcWidth' = wsrc
          trgWidth' <- bvSize trg
          if off >= trgWidth'
            then return Nothing
            else if off+srcWidth' > trgWidth'
                 then (do
                          let len = trgWidth' - off
                              rest = srcWidth' - len
                          reifyNat (fromInteger off) $
                            \roff -> reifyNat (fromInteger len) $
                            \rlen -> do
                              Just splitTrg <- splitBVMaybe roff rlen trg
                              Just (NoPrefix wr wrRest) <- splitBVMaybe Zero rlen src
                              ntrg <- unsplitBV $ splitBVSet splitTrg wr
                              return $ Just (Comp ntrg,Just (CompBV wrRest rest)))
                 else (reifyNat (fromInteger off) $
                       \roff -> do
                         Just splitTrg <- splitBVMaybe roff srcWidth trg
                         ntrg <- unsplitBV $ splitBVSet splitTrg src
                         return $ Just (Comp ntrg,Nothing))

bvSize :: Embed m e => e (BitVecType bw) -> m Integer
bvSize e = (\tp -> case tp e of
               BitVecRepr bw -> naturalToInteger bw) <$> embedTypeOf

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
