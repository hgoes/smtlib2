module Language.SMTLib2.Composite.Tuple where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import Data.GADT.Show
import Data.GADT.Compare
import Data.Proxy

data CompTuple2 (a :: (Type -> *) -> *) (b :: (Type -> *) -> *) e
  = CompTuple2 { ctuple2_1 :: a e
               , ctuple2_2 :: b e }
  deriving Show

data CompTuple3 (a :: (Type -> *) -> *) (b :: (Type -> *) -> *) (c :: (Type -> *) -> *) e
  = CompTuple3 { ctuple3_1 :: a e
               , ctuple3_2 :: b e
               , ctuple3_3 :: c e }
  deriving Show

data RevTuple2 a b tp
  = RevTuple2_1 (RevComp a tp)
  | RevTuple2_2 (RevComp b tp)

data RevTuple3 a b c tp
  = RevTuple3_1 (RevComp a tp)
  | RevTuple3_2 (RevComp b tp)
  | RevTuple3_3 (RevComp c tp)

instance (Composite a,Composite b) => Composite (CompTuple2 a b) where
  type CompDescr (CompTuple2 a b) = (CompDescr a,CompDescr b)
  type RevComp (CompTuple2 a b) = RevTuple2 a b
  compositeType (a,b) = CompTuple2 (compositeType a) (compositeType b)
  foldExprs f tup = do
    n1 <- foldExprs (f . RevTuple2_1) (ctuple2_1 tup)
    n2 <- foldExprs (f . RevTuple2_2) (ctuple2_2 tup)
    return $ CompTuple2 n1 n2
  accessComposite (RevTuple2_1 r) tup = accessComposite r (ctuple2_1 tup)
  accessComposite (RevTuple2_2 r) tup = accessComposite r (ctuple2_2 tup)
  createComposite f (a,b) = do
    ta <- createComposite (\tp r -> f tp (RevTuple2_1 r)) a
    tb <- createComposite (\tp r -> f tp (RevTuple2_2 r)) b
    return $ CompTuple2 ta tb
  revType (_::Proxy (CompTuple2 a b)) (a,_) (RevTuple2_1 r) = revType (Proxy::Proxy a) a r
  revType (_::Proxy (CompTuple2 a b)) (_,b) (RevTuple2_2 r) = revType (Proxy::Proxy b) b r

instance (CompositeExtract a,CompositeExtract b)
  => CompositeExtract (CompTuple2 a b) where
  type CompExtract (CompTuple2 a b) = (CompExtract a,CompExtract b)
  compExtract f (CompTuple2 a b)
    = (\va vb -> (va,vb)) <$>
      compExtract f a <*>
      compExtract f b

instance (Composite a,Composite b,Composite c) => Composite (CompTuple3 a b c) where
  type CompDescr (CompTuple3 a b c) = (CompDescr a,CompDescr b,CompDescr c)
  type RevComp (CompTuple3 a b c) = RevTuple3 a b c
  compositeType (a,b,c) = CompTuple3 (compositeType a) (compositeType b) (compositeType c)
  foldExprs f tup = do
    n1 <- foldExprs (f . RevTuple3_1) (ctuple3_1 tup)
    n2 <- foldExprs (f . RevTuple3_2) (ctuple3_2 tup)
    n3 <- foldExprs (f . RevTuple3_3) (ctuple3_3 tup)
    return $ CompTuple3 n1 n2 n3
  accessComposite (RevTuple3_1 r) tup = accessComposite r (ctuple3_1 tup)
  accessComposite (RevTuple3_2 r) tup = accessComposite r (ctuple3_2 tup)
  accessComposite (RevTuple3_3 r) tup = accessComposite r (ctuple3_3 tup)
  createComposite f (a,b,c) = do
    ta <- createComposite (\tp r -> f tp (RevTuple3_1 r)) a
    tb <- createComposite (\tp r -> f tp (RevTuple3_2 r)) b
    tc <- createComposite (\tp r -> f tp (RevTuple3_3 r)) c
    return $ CompTuple3 ta tb tc
  revType (_::Proxy (CompTuple3 a b c)) (a,_,_) (RevTuple3_1 r) = revType (Proxy::Proxy a) a r
  revType (_::Proxy (CompTuple3 a b c)) (_,b,_) (RevTuple3_2 r) = revType (Proxy::Proxy b) b r
  revType (_::Proxy (CompTuple3 a b c)) (_,_,c) (RevTuple3_3 r) = revType (Proxy::Proxy c) c r

instance (CompositeExtract a,CompositeExtract b,CompositeExtract c)
  => CompositeExtract (CompTuple3 a b c) where
  type CompExtract (CompTuple3 a b c) = (CompExtract a,CompExtract b,CompExtract c)
  compExtract f (CompTuple3 a b c) = do
    va <- compExtract f a
    vb <- compExtract f b
    vc <- compExtract f c
    return (va,vb,vc)

instance (Composite a,Composite b) => Show (RevTuple2 a b tp) where
  showsPrec p (RevTuple2_1 r) = showParen (p>10) $
    showString "[1/2] " .
    gshowsPrec 0 r
  showsPrec p (RevTuple2_2 r) = showParen (p>10) $
    showString "[2/2] " .
    gshowsPrec 0 r

instance (Composite a,Composite b,Composite c) => Show (RevTuple3 a b c tp) where
  showsPrec p (RevTuple3_1 r) = showParen (p>10) $
    showString "[1/3] " .
    gshowsPrec 0 r
  showsPrec p (RevTuple3_2 r) = showParen (p>10) $
    showString "[2/3] " .
    gshowsPrec 0 r
  showsPrec p (RevTuple3_3 r) = showParen (p>10) $
    showString "[3/3] " .
    gshowsPrec 0 r

instance (Composite a,Composite b) => GShow (RevTuple2 a b) where
  gshowsPrec = showsPrec

instance (Composite a,Composite b,Composite c) => GShow (RevTuple3 a b c) where
  gshowsPrec = showsPrec

instance (Composite a,Composite b) => GEq (RevTuple2 a b) where
  geq (RevTuple2_1 r1) (RevTuple2_1 r2) = do
    Refl <- geq r1 r2
    return Refl
  geq (RevTuple2_2 r1) (RevTuple2_2 r2) = do
    Refl <- geq r1 r2
    return Refl
  geq _ _ = Nothing

instance (Composite a,Composite b,Composite c) => GEq (RevTuple3 a b c) where
  geq (RevTuple3_1 r1) (RevTuple3_1 r2) = do
    Refl <- geq r1 r2
    return Refl
  geq (RevTuple3_2 r1) (RevTuple3_2 r2) = do
    Refl <- geq r1 r2
    return Refl
  geq (RevTuple3_3 r1) (RevTuple3_3 r2) = do
    Refl <- geq r1 r2
    return Refl
  geq _ _ = Nothing

instance (Composite a,Composite b) => GCompare (RevTuple2 a b) where
  gcompare (RevTuple2_1 r1) (RevTuple2_1 r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevTuple2_1 _) _ = GLT
  gcompare _ (RevTuple2_1 _) = GGT
  gcompare (RevTuple2_2 r1) (RevTuple2_2 r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance (Composite a,Composite b,Composite c) => GCompare (RevTuple3 a b c) where
  gcompare (RevTuple3_1 r1) (RevTuple3_1 r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevTuple3_1 _) _ = GLT
  gcompare _ (RevTuple3_1 _) = GGT
  gcompare (RevTuple3_2 r1) (RevTuple3_2 r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevTuple3_2 _) _ = GLT
  gcompare _ (RevTuple3_2 _) = GGT
  gcompare (RevTuple3_3 r1) (RevTuple3_3 r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
