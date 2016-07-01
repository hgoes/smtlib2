module Language.SMTLib2.Composite.Array.Bounded where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Array as Array

import Data.GADT.Show
import Data.GADT.Compare

data CompArrayBounded idx c e = CompArrayBounded { boundedArray :: CompArray '[idx] c e
                                                 , lowerBound :: Either (Value idx) (e idx)
                                                 , upperBound :: Either (Value idx) (e idx) }

data RevArrayBounded idx c tp where
  RevArrayBounded :: RevComp (CompArray '[idx] c) tp -> RevArrayBounded idx c tp
  RevLowerBound :: RevArrayBounded idx c idx
  RevUpperBound :: RevArrayBounded idx c idx

data CompArrayBoundedDescr idx c = CompArrayBoundedDescr { boundedArrayDescr :: CompDescr (CompArray '[idx] c)
                                                         , constantLowerBound :: Maybe (Value idx)
                                                         , constantUpperBound :: Maybe (Value idx)
                                                         }

deriving instance Composite c => Eq (CompArrayBoundedDescr idx c)
deriving instance Composite c => Ord (CompArrayBoundedDescr idx c)

instance Composite c => Composite (CompArrayBounded idx c) where
  type CompDescr (CompArrayBounded idx c) = CompArrayBoundedDescr idx c
  type RevComp (CompArrayBounded idx c) = RevArrayBounded idx c
  compositeType descr = CompArrayBounded { boundedArray = compositeType (boundedArrayDescr descr)
                                         , lowerBound = case constantLowerBound descr of
                                             Just rl -> Left rl
                                             Nothing -> Right (case fst $ boundedArrayDescr descr of
                                                                 i ::: Nil -> i)
                                         , upperBound = case constantUpperBound descr of
                                             Just ru -> Left ru
                                             Nothing -> Right (case fst $ boundedArrayDescr descr of
                                                                 i ::: Nil -> i) }
  foldExprs f arr = do
    narr <- foldExprs (\r -> f (RevArrayBounded r)) (boundedArray arr)
    nlower <- case lowerBound arr of
      Left v -> return (Left v)
      Right v -> do
        nv <- f RevLowerBound v
        return (Right nv)
    nupper <- case upperBound arr of
      Left v -> return (Left v)
      Right v -> do
        nv <- f RevUpperBound v
        return (Right nv)
    return CompArrayBounded { boundedArray = narr
                            , lowerBound = nlower
                            , upperBound = nupper }
  accessComposite (RevArrayBounded r) arr = accessComposite r (boundedArray arr)
  accessComposite RevLowerBound arr = case lowerBound arr of
                                        Left _ -> Nothing
                                        Right v -> Just v
  accessComposite RevUpperBound arr = case upperBound arr of
                                        Left _ -> Nothing
                                        Right v -> Just v

instance (CompositeExtract c,Enum (Value idx)) => CompositeExtract (CompArrayBounded idx c) where
  type CompExtract (CompArrayBounded idx c) = [(Value idx,CompExtract c)]
  compExtract f arr = do
    lower <- case lowerBound arr of
      Left v -> return v
      Right v -> f v
    upper <- case upperBound arr of
      Left v -> return v
      Right v -> f v
    mapM (\idx -> do
             cidx <- constant idx
             el <- Array.select (boundedArray arr) (cidx ::: Nil)
             res <- compExtract f el
             return (idx,res)
         ) [lower..upper]

instance Composite c => Show (RevArrayBounded idx c tp) where
  showsPrec p (RevArrayBounded r) = showParen (p>10) $
    showString "arr " . gshowsPrec 11 r
  showsPrec _ RevLowerBound = showString "lower-bound"
  showsPrec _ RevUpperBound = showString "upper-bound"

instance Composite c => GShow (RevArrayBounded idx c) where
  gshowsPrec = showsPrec

instance Composite c => GEq (RevArrayBounded idx c) where
  geq (RevArrayBounded r1) (RevArrayBounded r2) = do
    Refl <- geq r1 r2
    return Refl
  geq RevLowerBound RevLowerBound = return Refl
  geq RevUpperBound RevUpperBound = return Refl
  geq _ _ = Nothing

instance Composite c => GCompare (RevArrayBounded idx c) where
  gcompare (RevArrayBounded r1) (RevArrayBounded r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevArrayBounded _) _ = GLT
  gcompare _ (RevArrayBounded _) = GGT
  gcompare RevLowerBound RevLowerBound = GEQ
  gcompare RevLowerBound _ = GLT
  gcompare _ RevLowerBound = GGT
  gcompare RevUpperBound RevUpperBound = GEQ

consDescr :: Num (Value idx) => (CompDescr c -> CompDescr c -> CompDescr c)
          -> CompDescr c
          -> CompArrayBoundedDescr idx c
          -> CompArrayBoundedDescr idx c
consDescr f c descr
  = descr { boundedArrayDescr = case boundedArrayDescr descr of
              (idx,el) -> (idx,f el c)
          , constantLowerBound = case constantLowerBound descr of
                                   Just l -> Just (l-1)
                                   Nothing -> Nothing }

cons :: (Composite c,Embed m e,GetType e,Num (Value idx),Num (m (e idx))) => c e
     -> CompArrayBounded idx c e
     -> m (e idx,CompArrayBounded idx c e)
cons x xs = case lowerBound xs of
  Left c -> do
    idx <- constant c
    narr <- Array.store (boundedArray xs) (idx ::: Nil) x
    return (idx,xs { boundedArray = narr
                   , lowerBound = Left (c-1) })
  Right l -> do
    nl <- (return l) - 1
    narr <- Array.store (boundedArray xs) (l ::: Nil) x
    return (l,xs { boundedArray = narr
                 , lowerBound = Right nl })

snocDescr :: Num (Value idx) => (CompDescr c -> CompDescr c -> CompDescr c)
          -> CompDescr c
          -> CompArrayBoundedDescr idx c
          -> CompArrayBoundedDescr idx c
snocDescr f c descr
  = descr { boundedArrayDescr = case boundedArrayDescr descr of
              (idx,el) -> (idx,f el c)
          , constantUpperBound = case constantUpperBound descr of
                                   Just u -> Just (u+1)
                                   Nothing -> Nothing }

snoc :: (Composite c,Embed m e,GetType e,Num (Value idx),Num (m (e idx))) => c e
     -> CompArrayBounded idx c e
     -> m (e idx,CompArrayBounded idx c e)
snoc x xs = case upperBound xs of
  Left c -> do
    idx <- constant c
    narr <- Array.store (boundedArray xs) (idx ::: Nil) x
    return (idx,xs { boundedArray = narr
                   , upperBound = Left (c-1) })
  Right l -> do
    nl <- (return l) - 1
    narr <- Array.store (boundedArray xs) (l ::: Nil) x
    return (l,xs { boundedArray = narr
                 , upperBound = Right nl })

select :: (Embed m e,GetType e,Composite c) => CompArrayBounded idx c e -> e idx -> m (c e)
select arr idx = Array.select (boundedArray arr) (idx ::: Nil)

store :: (Embed m e,GetType e,Composite c) => CompArrayBounded idx c e -> e idx -> c e -> m (CompArrayBounded idx c e)
store arr idx el = do
  narr <- Array.store (boundedArray arr) (idx ::: Nil) el
  return arr { boundedArray = narr }
