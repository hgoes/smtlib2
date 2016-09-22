module Language.SMTLib2.Composite.Maybe where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class hiding (defaultEq)
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2.Composite.Domains

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

instance ByteWidth a idx => ByteWidth (CompMaybe a) idx where
  byteWidth (CompMaybe Nothing) = compositeFromValue 0
  byteWidth (CompMaybe (Just obj)) = byteWidth obj

instance StaticByteAccess a el => StaticByteAccess (CompMaybe a) el where
  staticByteRead (CompMaybe Nothing) _ _ = return Nothing
  staticByteRead (CompMaybe (Just obj)) idx sz = staticByteRead obj idx sz
  staticByteWrite (CompMaybe Nothing) _ _ = return Nothing
  staticByteWrite (CompMaybe (Just obj)) idx el = do
    res <- staticByteWrite obj idx el
    case res of
      Nothing -> return Nothing
      Just (res',rest) -> return $ Just (CompMaybe $ Just res',rest)

instance ByteAccess a idx el => ByteAccess (CompMaybe a) idx el where
  byteRead (CompMaybe Nothing) _ _ = do
    cond <- true
    return $ outsideRead cond
  byteRead (CompMaybe (Just obj)) idx sz = byteRead obj idx sz
  byteWrite (CompMaybe Nothing) _ _ = do
    cond <- true
    return $ outsideWrite cond
  byteWrite (CompMaybe (Just obj)) idx el = do
    res <- byteWrite obj idx el
    return res { fullWrite = fmap (CompMaybe . Just) (fullWrite res) }
