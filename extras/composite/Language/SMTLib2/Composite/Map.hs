module Language.SMTLib2.Composite.Map where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Lens

import Data.Map (Map)
import qualified Data.Map as Map
import Data.GADT.Show
import Data.GADT.Compare
import Text.Show
import Control.Lens

data RevMap k a tp = RevMap k (RevComp a tp)

newtype CompMap k a (e :: Type -> *) = CompMap { _compMap :: Map k (a e) }

makeLenses ''CompMap

instance (Show k,Ord k,Composite a) => Composite (CompMap k a) where
  type RevComp (CompMap k a) = RevMap k a
  foldExprs f (CompMap mp) = do
    nmp <- sequence $ Map.mapWithKey
      (\k -> foldExprs (f . RevMap k)) mp
    return (CompMap nmp)
  accessComposite (RevMap k r) = maybeLens compMap `composeMaybe` mapElement k `composeMaybe` accessComposite r
  compCombine f (CompMap mp1) (CompMap mp2) = do
    nmp <- sequence $ Map.mergeWithKey (\_ x y -> Just $ compCombine f x y) (fmap $ return.Just) (fmap $ return.Just) mp1 mp2
    return $ fmap CompMap $ sequence nmp
  compCompare (CompMap mp1) (CompMap mp2)
    = mconcat $ Map.elems $ Map.mergeWithKey (\_ x y -> Just $ compCompare x y)
      (fmap $ const LT) (fmap $ const GT) mp1 mp2
      
  compShow = showsPrec
  compInvariant (CompMap mp) = fmap concat $ mapM compInvariant $ Map.elems mp

instance (Show k,Composite a,GShow e) => Show (CompMap k a e) where
  showsPrec p (CompMap mp)
    = showListWith (\(k,el) -> showsPrec 5 k . showString " -> " . compShow 5 el) (Map.toList mp)

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

mapElement :: Ord k => k -> MaybeLens (Map k a) a
mapElement k = lens (\mp -> Map.lookup k mp) (\mp entr -> Just $ Map.insert k entr mp)
