module Language.SMTLib2.Composite.Null where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains

import Data.GADT.Compare
import Data.GADT.Show

newtype NoComp (val :: *) (e :: Type -> *) = NoComp val

data NoRev (tp :: Type)

instance (Ord val,Show val) => Composite (NoComp val) where
  type RevComp (NoComp val) = NoRev
  foldExprs _ (NoComp x) = return (NoComp x)
  mapExprs _ (NoComp x) = return (NoComp x)
  getRev _ _ = Nothing
  setRev _ _ _ = Nothing
  compCombine _ (NoComp x) (NoComp y) = return $ if x==y
                                                 then Just $ NoComp x
                                                 else Nothing
  compCompare (NoComp x) (NoComp y) = compare x y
  compShow p (NoComp x) = showParen (p>10) $ showString "const " . showsPrec 11 x

instance (Ord val,Show val) => CompositeExtract (NoComp val) where
  type CompExtract (NoComp val) = ()
  compExtract _ _ = pure ()

instance GShow NoRev where
  gshowsPrec _ _ = error "gshowsPrec called for NoRev"
instance GEq NoRev where
  geq _ _ = error "geq called for NoRev"
instance GCompare NoRev where
  gcompare _ _ = error "gcompare called for NoRev"

instance IsSingleton (NoComp (Value tp)) where
  type SingletonType (NoComp (Value tp)) = tp
  getSingleton (NoComp x) = constant x

instance IsConstant (NoComp (Value tp)) where
  getConstant (NoComp x) = Just x

instance IsRanged (NoComp (Value tp)) where
  getRange (NoComp x) = return $ rangedConst x
