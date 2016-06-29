module Language.SMTLib2.Composite.Singleton where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import Data.GADT.Compare
import Data.GADT.Show

newtype Comp (tp :: Type) e = Comp { comp :: e tp }

instance Composite (Comp tp) where
  type CompDescr (Comp tp) = Repr tp
  type RevComp (Comp tp) = (:~:) tp
  compositeType tp = Comp tp
  foldExprs f (Comp e) = do
    ne <- f Refl e
    return (Comp ne)
  accessComposite Refl (Comp e) = Just e
  createComposite f tp = fmap Comp (f tp Refl)
  revType _ tp Refl = tp

instance GShow e => Show (Comp tp e) where
  showsPrec p (Comp e) = gshowsPrec p e
