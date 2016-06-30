module Language.SMTLib2.Composite.List where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import Data.List (genericIndex)
import Data.GADT.Show
import Data.GADT.Compare

data RevList a tp = RevList Integer (RevComp a tp)

newtype CompList a (e :: Type -> *) = CompList { compList :: [a e] } deriving Show

instance Composite a => Composite (CompList a) where
  type CompDescr (CompList a) = [CompDescr a]
  type RevComp (CompList a) = RevList a
  compositeType lst = CompList (fmap compositeType lst)
  foldExprs f (CompList lst) = do
    nlst <- mapM (\(n,el) -> foldExprs (f . RevList n) el) (zip [0..] lst)
    return (CompList nlst)
  accessComposite (RevList n r) (CompList lst)
    = accessComposite r (genericIndex lst n)

instance CompositeExtract a => CompositeExtract (CompList a) where
  type CompExtract (CompList a) = [CompExtract a]
  compExtract f (CompList xs) = mapM (compExtract f) xs

instance Composite a => Show (RevList a tp) where
  showsPrec p (RevList n r)
    = showParen (p>10) $ showString "RevList " .
      showsPrec 11 n . showChar ' ' . gshowsPrec 11 r

instance Composite a => GShow (RevList a) where
  gshowsPrec = showsPrec

instance Composite a => GEq (RevList a) where
  geq (RevList n1 r1) (RevList n2 r2) = if n1==n2
                                        then do
    Refl <- geq r1 r2
    return Refl
                                        else Nothing

instance Composite a => GCompare (RevList a) where
  gcompare (RevList n1 r1) (RevList n2 r2) = case compare n1 n2 of
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
