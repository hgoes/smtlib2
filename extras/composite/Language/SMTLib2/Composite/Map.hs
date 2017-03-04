module Language.SMTLib2.Composite.Map where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Container
import Language.SMTLib2.Composite.Null

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.GADT.Show
import Data.GADT.Compare
import Text.Show
import Data.List (foldl')

data RevMap k a tp = RevMap !k !(RevComp a tp)

newtype CompMap k a (e :: Type -> *) = CompMap { compMap :: Map k (a e) }

instance (Show k,Ord k,Composite a) => Composite (CompMap k a) where
  type RevComp (CompMap k a) = RevMap k a
  foldExprs f (CompMap mp) = do
    nmp <- sequence $ Map.mapWithKey
      (\k -> foldExprs (f . RevMap k)) mp
    return (CompMap nmp)
  getRev (RevMap k r) (CompMap mp) = Map.lookup k mp >>= getRev r
  setRev (RevMap k r) x Nothing = do
    el <- setRev r x Nothing
    return $ CompMap $ Map.singleton k el
  setRev (RevMap k r) x (Just (CompMap mp)) = do
    nel <- setRev r x (Map.lookup k mp)
    return $ CompMap $ Map.insert k nel mp
  compCombine f (CompMap mp1) (CompMap mp2) = do
    nmp <- sequence $ Map.mergeWithKey (\_ x y -> Just $ compCombine f x y) (fmap $ return.Just) (fmap $ return.Just) mp1 mp2
    return $ fmap CompMap $ sequence nmp
  compCompare = compare
  compShow = showsPrec
  compInvariant (CompMap mp) = fmap concat $ mapM compInvariant $ Map.elems mp

instance (Ord k,Show k,Composite el) => Container (CompMap k el) where
  data Index (CompMap k el) el' e where
    MapIndex :: k -> Index (CompMap k el) el e

  elementGet (CompMap mp) (MapIndex k) = case Map.lookup k mp of
    Just r -> return r
    Nothing -> error $ "CompMap.elementGet: Key "++show k++" not in map."
  elementSet (CompMap mp) (MapIndex k) x = return $ CompMap $ Map.insert k x mp
  showIndex p (MapIndex k) = showsPrec p k

instance (Show k,Composite a,GShow e) => Show (CompMap k a e) where
  showsPrec p (CompMap mp)
    = showListWith (\(k,el) -> showsPrec 5 k . showString " -> " . compShow 5 el) (Map.toList mp)

instance (Ord k,Composite a,GCompare e) => Eq (CompMap k a e) where
  (==) (CompMap mp1) (CompMap mp2)
    = and $ Map.mergeWithKey (\_ x y -> Just $ case compCompare x y of
                                 EQ -> True
                                 _ -> False)
      (fmap $ const False) (fmap $ const False) mp1 mp2

instance (Ord k,Composite a,GCompare e) => Ord (CompMap k a e) where
  compare (CompMap mp1) (CompMap mp2)
    = mconcat $ Map.elems $ Map.mergeWithKey (\_ x y -> Just $ compCompare x y)
      (fmap $ const LT) (fmap $ const GT) mp1 mp2

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
