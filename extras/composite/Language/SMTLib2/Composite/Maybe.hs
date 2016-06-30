module Language.SMTLib2.Composite.Maybe where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Singleton

newtype CompMaybe a (e :: Type -> *) = CompMaybe { compMaybe :: Maybe (a e) } deriving Show

instance Composite a => Composite (CompMaybe a) where
  type CompDescr (CompMaybe a) = Maybe (CompDescr a)
  type RevComp (CompMaybe a) = RevComp a
  compositeType Nothing = CompMaybe Nothing
  compositeType (Just d) = CompMaybe (Just (compositeType d))
  foldExprs f (CompMaybe Nothing) = return $ CompMaybe Nothing
  foldExprs f (CompMaybe (Just v)) = do
    nv <- foldExprs f v
    return (CompMaybe (Just nv))
  accessComposite r (CompMaybe (Just v)) = accessComposite r v

instance CompositeExtract a => CompositeExtract (CompMaybe a) where
  type CompExtract (CompMaybe a) = Maybe (CompExtract a)
  compExtract f (CompMaybe v) = case v of
    Nothing -> return Nothing
    Just c -> do
      res <- compExtract f c
      return (Just res)
