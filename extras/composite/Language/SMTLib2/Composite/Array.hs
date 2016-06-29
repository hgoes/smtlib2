module Language.SMTLib2.Composite.Array where

import Language.SMTLib2 as SMT
import Language.SMTLib2.Composite.Class

import Data.GADT.Show
import Data.GADT.Compare
import Data.Functor.Identity

newtype Arrayed idx e tp = Arrayed (e (ArrayType idx tp))

newtype CompArray idx c e = CompArray (c (Arrayed idx e))

data RevArray idx c tp where
  RevArray :: RevComp c tp -> RevArray idx c (ArrayType idx tp)

instance GetType e => GetType (Arrayed i e) where
  getType (Arrayed e) = case getType e of
    ArrayRepr _ tp -> tp

instance Composite c => Composite (CompArray i c) where
  type CompDescr (CompArray i c) = (List Repr i,CompDescr c)
  type RevComp (CompArray i c) = RevArray i c
  compositeType (i,d) = CompArray $ runIdentity $
    foldExprs (\_ tp -> return $ Arrayed (ArrayRepr i tp)
              ) (compositeType d)
  foldExprs f (CompArray c) = do
    nc <- foldExprs (\r (Arrayed e) -> do
                        ne <- f (RevArray r) e
                        return (Arrayed ne)
                    ) c
    return (CompArray nc)
  accessComposite (RevArray r) (CompArray c) = do
    Arrayed e <- accessComposite r c
    return e

instance Composite c => Show (RevArray i c tp) where
  showsPrec p (RevArray r) = showParen (p>10) $
    showString "arr " . gshowsPrec 11 r

instance Composite c => GShow (RevArray i c) where
  gshowsPrec = showsPrec

instance Composite c => GEq (RevArray i c) where
  geq (RevArray r1) (RevArray r2) = do
    Refl <- geq r1 r2
    return Refl

instance Composite c => GCompare (RevArray i c) where
  gcompare (RevArray r1) (RevArray r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

select :: (Composite c,Embed m e,GetType e) => CompArray i c e -> List e i -> m (c e)
select (CompArray c) i = foldExprs (\_ (Arrayed e) -> SMT.select e i) c

store :: (Composite c,Embed m e,GetType e) => CompArray i c e -> List e i -> c e -> m (CompArray i c e)
store (CompArray c) i el = do
  nc <- foldExprs (\rev (Arrayed arr) -> case accessComposite rev el of
                      Just nel -> do
                        narr <- SMT.store arr i nel
                        return (Arrayed narr)
                      Nothing -> return (Arrayed arr)
                  ) c
  return $ CompArray nc
