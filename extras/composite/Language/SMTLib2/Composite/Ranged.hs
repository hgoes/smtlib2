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

data Ranged c (e :: Type -> *) = Ranged { _range :: Range (SingletonType c)
                                        , _ranged :: c e }

makeLenses ''Ranged

instance (Composite c,GShow e) => Show (Ranged c e) where
  showsPrec p (Ranged r c) = showParen (p>10) $
    showString "Ranged " . showsPrec 11 r . showChar ' ' .
    compShow 11 c

instance IsSingleton c => Composite (Ranged c) where
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

instance IsSingleton c => IsSingleton (Ranged c) where
  type SingletonType (Ranged c) = SingletonType c
  getSingleton r = getSingleton (_ranged r)

instance IsSingleton c => IsRanged (Ranged c) where
  getRange r = return $ _range r

instance IsNumeric c => IsNumeric (Ranged c) where
  compositeFromValue v = do
    rv <- compositeFromValue v
    return $ Ranged (singletonRange v) rv
  compositePlus c1 c2 = do
    r <- compositePlus (_ranged c1) (_ranged c2)
    return $ Ranged (rangeAdd (_range c1) (_range c2)) r
  compositeMinus c1 c2 = do
    r <- compositeMinus (_ranged c1) (_ranged c2)
    return $ Ranged (rangeAdd (_range c1) (rangeNeg $ _range c2)) r
  compositeSum cs = do
    c <- compositeSum $ fmap _ranged cs
    let r = case cs of
              [] -> singletonRange 0
              _ -> foldl1 rangeAdd (fmap _range cs)
    return $ Ranged r c
  compositeNegate c = do
    nc <- compositeNegate $ _ranged c
    return $ Ranged (rangeNeg $ _range c) nc
  compositeMult c1 c2 = do
    c <- compositeMult (_ranged c1) (_ranged c2)
    return $ Ranged (rangeMult (_range c1) (_range c2)) c
  compositeGEQ c1 c2 = compositeGEQ (_ranged c1) (_ranged c2)
  compositeDiv c1 c2 = do
    c <- compositeDiv (_ranged c1) (_ranged c2)
    return $ Ranged (rangeDiv (_range c1) (_range c2)) c
  compositeMod c1 c2 = do
    c <- compositeMod (_ranged c1) (_ranged c2)
    return $ Ranged (rangeMod (_range c1) (_range c2)) c
