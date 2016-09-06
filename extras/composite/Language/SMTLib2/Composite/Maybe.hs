module Language.SMTLib2.Composite.Maybe where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class hiding (defaultEq)
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2.Composite.Singleton

import Data.GADT.Compare
import Control.Lens

newtype CompMaybe a (e :: Type -> *) = CompMaybe { _compMaybe :: Maybe (a e) }

makeLenses ''CompMaybe

instance Composite a => Composite (CompMaybe a) where
  type RevComp (CompMaybe a) = RevComp a
  foldExprs f (CompMaybe Nothing) = return $ CompMaybe Nothing
  foldExprs f (CompMaybe (Just v)) = do
    nv <- foldExprs f v
    return (CompMaybe (Just nv))
  accessComposite r = maybeLens compMaybe `composeMaybe` just `composeMaybe` accessComposite r
  compCombine f (CompMaybe Nothing) (CompMaybe Nothing)
    = return $ Just $ CompMaybe Nothing
  compCombine f (CompMaybe (Just x)) (CompMaybe (Just y)) = do
    z <- compCombine f x y
    return $ fmap (CompMaybe . Just) z
  compCompare (CompMaybe Nothing) (CompMaybe Nothing) = EQ
  compCompare (CompMaybe Nothing) _ = LT
  compCompare _ (CompMaybe Nothing) = GT
  compCompare (CompMaybe (Just x)) (CompMaybe (Just y)) = compCompare x y
  compShow _ (CompMaybe Nothing) = showString "Nothing"
  compShow p (CompMaybe (Just x)) = showParen (p>10) $
    showString "Just " .
    compShow 11 x
  compInvariant (CompMaybe Nothing) = return []
  compInvariant (CompMaybe (Just x)) = compInvariant x

instance CompositeExtract a => CompositeExtract (CompMaybe a) where
  type CompExtract (CompMaybe a) = Maybe (CompExtract a)
  compExtract f (CompMaybe v) = case v of
    Nothing -> return Nothing
    Just c -> do
      res <- compExtract f c
      return (Just res)
