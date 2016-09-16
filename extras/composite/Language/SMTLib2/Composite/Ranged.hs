{-# LANGUAGE KindSignatures,DataKinds,GADTs,TypeFamilies,StandaloneDeriving,MultiWayIf #-}
{- | A value bounded by static bounds. -}
module Language.SMTLib2.Composite.Ranged
  (Ranged(..),
   -- * Range
   Range(..),
   rangeType,
   unionRange,intersectionRange,
   rangeFixpoint,
   isConst,
   includes,
   fullRange,
   emptyRange,
   isEmptyRange,
   lowerBound,upperBound,
   singletonRange,
   ltRange,leqRange,gtRange,geqRange,
   betweenRange,
   -- * Functions
   rangedConst,
   rangeInvariant,
   Bounds,Inf(..),
   toBounds,fromBounds
  ) where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type (bvPred,bvSucc)
import Data.GADT.Compare
import Data.GADT.Show
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Constraint
import Control.Lens

data Ranged c (e :: Type -> *) = Ranged { _getRange :: Range (SingletonType c)
                                        , _ranged :: c e }

makeLenses ''Ranged

instance (Composite c,GShow e) => Show (Ranged c e) where
  showsPrec p (Ranged r c) = showParen (p>10) $
    showString "Ranged " . showsPrec 11 r . showChar ' ' .
    compShow 11 c

instance (Composite c,IsSingleton c) => Composite (Ranged c) where
  type RevComp (Ranged c) = RevComp c
  foldExprs f (Ranged r c) = do
    nc <- foldExprs f c
    return $ Ranged r nc
  accessComposite r = maybeLens ranged `composeMaybe` accessComposite r
  compCombine f (Ranged r1 c1) (Ranged r2 c2)
    = fmap (fmap (Ranged (unionRange r1 r2))) $ compCombine f c1 c2
  compCompare (Ranged r1 c1) (Ranged r2 c2) = case compare r1 r2 of
    EQ -> compCompare c1 c2
    r -> r
  compShow = showsPrec
  compInvariant (Ranged r c) = compInvariant c

instance (CompositeExtract c,IsSingleton c) => CompositeExtract (Ranged c) where
  type CompExtract (Ranged c) = CompExtract c
  compExtract f (Ranged _ x) = compExtract f x
