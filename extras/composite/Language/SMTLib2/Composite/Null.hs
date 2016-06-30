module Language.SMTLib2.Composite.Null where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import Data.GADT.Compare
import Data.GADT.Show

data NoComp (val :: *) (e :: Type -> *) = NoComp

data NoRev (tp :: Type)

instance Ord val => Composite (NoComp val) where
  type CompDescr (NoComp val) = val
  type RevComp (NoComp val) = NoRev
  compositeType _ = NoComp
  foldExprs _ NoComp = return NoComp
  accessComposite _ _ = error "accessComposite called for NoComp"
  createComposite _ _ = return NoComp

instance Ord val => CompositeExtract (NoComp val) where
  type CompExtract (NoComp val) = ()
  compExtract _ _ = return ()

instance GShow NoRev where
  gshowsPrec _ _ = error "gshowsPrec called for NoRev"
instance GEq NoRev where
  geq _ _ = error "geq called for NoRev"
instance GCompare NoRev where
  gcompare _ _ = error "gcompare called for NoRev"
