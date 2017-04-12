module Language.SMTLib2.Composite.Maybe where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class hiding (defaultEq)
import Language.SMTLib2.Composite.Domains

import Data.GADT.Compare
import Data.GADT.Show

newtype CompMaybe a (e :: Type -> *) = CompMaybe { compMaybe :: Maybe (a e) }

newtype RevMaybe a tp = RevMaybe (RevComp a tp)

instance Composite a => Composite (CompMaybe a) where
  type RevComp (CompMaybe a) = RevMaybe a
  foldExprs f (CompMaybe Nothing) = return $ CompMaybe Nothing
  foldExprs f (CompMaybe (Just v)) = do
    nv <- foldExprs (f . RevMaybe) v
    return (CompMaybe (Just nv))
  mapExprs f (CompMaybe Nothing) = return $ CompMaybe Nothing
  mapExprs f (CompMaybe (Just v)) = do
    nv <- mapExprs f v
    return (CompMaybe (Just nv))
  getRev (RevMaybe r) (CompMaybe x) = x >>= getRev r
  setRev (RevMaybe r) x mb = do
    nel <- setRev r x (do
                          CompMaybe mb' <- mb
                          mb')
    return $ CompMaybe $ Just nel
  compCombine f (CompMaybe (Just x)) (CompMaybe (Just y)) = do
    z <- compCombine f x y
    return $ fmap (CompMaybe . Just) z
  compCombine _ (CompMaybe Nothing) y = return $ Just y
  compCombine _ x (CompMaybe Nothing) = return $ Just x
  compCompare (CompMaybe Nothing) (CompMaybe Nothing) = EQ
  compCompare (CompMaybe Nothing) _ = LT
  compCompare _ (CompMaybe Nothing) = GT
  compCompare (CompMaybe (Just x)) (CompMaybe (Just y)) = compCompare x y
  compIsSubsetOf f (CompMaybe Nothing) _ = True
  compIsSubsetOf f (CompMaybe (Just x)) (CompMaybe (Just y))
    = compIsSubsetOf f x y
  compIsSubsetOf f _ (CompMaybe Nothing) = False
  compShow = showsPrec
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
  byteWidth (CompMaybe Nothing) r = let Just zero = compositeFromInteger 0 r
                                    in mapExprs constant zero
  byteWidth (CompMaybe (Just obj)) r = byteWidth obj r

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

instance (Composite a,GShow e) => Show (CompMaybe a e) where
  showsPrec _ (CompMaybe Nothing) = showString "Nothing"
  showsPrec p (CompMaybe (Just x))
    = showParen (p>10) $ showString "Just " . compShow 11 x

instance Composite a => GEq (RevMaybe a) where
  geq (RevMaybe r1) (RevMaybe r2) = geq r1 r2

instance Composite a => GCompare (RevMaybe a) where
  gcompare (RevMaybe r1) (RevMaybe r2) = gcompare r1 r2

instance Composite a => Show (RevMaybe a tp) where
  showsPrec p (RevMaybe r) = gshowsPrec p r

instance Composite a => GShow (RevMaybe a) where
  gshowsPrec = showsPrec
