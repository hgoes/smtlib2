module Language.SMTLib2.Composite.Map where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import Data.Map (Map)
import qualified Data.Map as Map
import Data.GADT.Show
import Data.GADT.Compare

data RevMap k a tp = RevMap k (RevComp a tp)

newtype CompMap k a (e :: Type -> *) = CompMap { compMap :: Map k (a e) } deriving Show

mapITE :: (Ord k,Embed m e,Monad m) => (e BoolType -> a e -> a e -> m (a e))
       -> e BoolType
       -> CompMap k a e
       -> CompMap k a e
       -> m (CompMap k a e)
mapITE f cond (CompMap mp1) (CompMap mp2) = do
  mp <- sequence $ Map.unionWith
    (\v1 v2 -> do
        r1 <- v1
        r2 <- v2
        f cond r1 r2)
    (fmap return mp1)
    (fmap return mp2)
  return (CompMap mp)

instance (Show k,Ord k,Composite a) => Composite (CompMap k a) where
  type CompDescr (CompMap k a) = Map k (CompDescr a)
  type RevComp (CompMap k a) = RevMap k a
  compositeType mp = CompMap (fmap compositeType mp)
  foldExprs f (CompMap mp) = do
    nmp <- sequence $ Map.mapWithKey
      (\k -> foldExprs (f . RevMap k)) mp
    return (CompMap nmp)
  accessComposite (RevMap k r) (CompMap mp) = case Map.lookup k mp of
    Just el -> accessComposite r el

instance (Show k,Ord k,CompositeExtract a) => CompositeExtract (CompMap k a) where
  type CompExtract (CompMap k a) = Map k (CompExtract a)
  compExtract f (CompMap mp) = mapM (compExtract f) mp

instance (Show k,Composite a) => Show (RevMap k a tp) where
  showsPrec p (RevMap k r)
    = showParen (p>10) $ showString "RevMap " . showsPrec 11 k . showChar ' ' . gshowsPrec 11 r

instance (Show k,Composite a) => GShow (RevMap k a) where
  gshowsPrec = showsPrec

instance (Eq k,Composite a) => GEq (RevMap k a) where
  geq (RevMap k1 r1) (RevMap k2 r2) = if k1==k2
                                      then do
    Refl <- geq r1 r2
    return Refl
                                      else Nothing

instance (Ord k,Composite a) => GCompare (RevMap k a) where
  gcompare (RevMap k1 r1) (RevMap k2 r2) = case compare k1 k2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
