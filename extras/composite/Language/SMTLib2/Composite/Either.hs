module Language.SMTLib2.Composite.Either where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import Data.GADT.Show
import Data.GADT.Compare

newtype CompEither a b (e :: Type -> *) = CompEither { compEither :: Either (a e) (b e)
                                                     } deriving Show

data RevEither a b tp = RevLeft (RevComp a tp)
                      | RevRight (RevComp b tp)

instance (Composite a,Composite b) => Composite (CompEither a b) where
  type CompDescr (CompEither a b) = Either (CompDescr a) (CompDescr b)
  type RevComp (CompEither a b) = RevEither a b
  compositeType (Left d) = CompEither (Left (compositeType d))
  compositeType (Right d) = CompEither (Right (compositeType d))
  foldExprs f (CompEither (Left x)) = do
    nx <- foldExprs (f . RevLeft) x
    return (CompEither (Left nx))
  foldExprs f (CompEither (Right x)) = do
    nx <- foldExprs (f . RevRight) x
    return (CompEither (Right nx))
  accessComposite (RevLeft r) (CompEither (Left x)) = accessComposite r x
  accessComposite (RevRight r) (CompEither (Right x)) = accessComposite r x

instance (CompositeExtract a,CompositeExtract b)
  => CompositeExtract (CompEither a b) where
  type CompExtract (CompEither a b) = Either (CompExtract a) (CompExtract b)
  compExtract f (CompEither v) = case v of
    Left l -> do
      res <- compExtract f l
      return (Left res)
    Right r -> do
      res <- compExtract f r
      return (Right res)

instance (Composite a,Composite b) => Show (RevEither a b tp) where
  showsPrec p (RevLeft r) = showParen (p>10) $
    showString "left " . gshowsPrec 11 r
  showsPrec p (RevRight r) = showParen (p>10) $
    showString "right " . gshowsPrec 11 r

instance (Composite a,Composite b) => GShow (RevEither a b) where
  gshowsPrec = showsPrec

instance (Composite a,Composite b) => GEq (RevEither a b) where
  geq (RevLeft x) (RevLeft y) = do
    Refl <- geq x y
    return Refl
  geq (RevRight x) (RevRight y) = do
    Refl <- geq x y
    return Refl
  geq _ _ = Nothing

instance (Composite a,Composite b) => GCompare (RevEither a b) where
  gcompare (RevLeft x) (RevLeft y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevLeft _) _ = GLT
  gcompare _ (RevLeft _) = GGT
  gcompare (RevRight x) (RevRight y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
