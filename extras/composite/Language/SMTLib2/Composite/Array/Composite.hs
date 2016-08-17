module Language.SMTLib2.Composite.Array.Composite
  (CompositeArray(..),
   RevCompositeArray(..),
   select,store) where

import Language.SMTLib2 hiding (select,store)
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Array (CompArray(..),RevArray(..))
import qualified Language.SMTLib2.Composite.Array as Array
import Language.SMTLib2.Composite.Ranged
import Language.SMTLib2.Composite.Data

import Control.Monad.State
import Data.Functor.Identity
import Data.GADT.Show
import Data.GADT.Compare
import Data.Proxy

data AnyList (e :: Type -> *) = forall tps. AnyList (List e tps)

allFields :: (Composite c,GetType e) => c e -> AnyList e
allFields c = execState (foldExprs (\_ e -> do
                                       AnyList xs <- get
                                       put $ AnyList (e ::: xs)
                                       return e
                                   ) c) (AnyList Nil)

allFieldDescr :: Composite c => Proxy c -> CompDescr c -> AnyList Repr
allFieldDescr (_::Proxy c) descr = allFields (compositeType descr :: c Repr)

data CompositeArray (idx :: (Type -> *) -> *) c e
  = forall ilst. CompositeArray (List Repr ilst) (CompArray ilst c e)

data RevCompositeArray (idx :: (Type -> *) -> *) c tp where
  RevCompositeArray :: RevComp c tp -> List Repr ilst -> RevCompositeArray idx c (ArrayType ilst tp)

instance (Composite idx,Composite c) => Composite (CompositeArray idx c) where
  type CompDescr (CompositeArray idx c) = (CompDescr idx,CompDescr c)
  type RevComp (CompositeArray idx c) = RevCompositeArray idx c
  compositeType (idx,c) = case allFieldDescr (Proxy::Proxy idx) idx of
    AnyList ilst -> CompositeArray ilst (compositeType (ilst,c)) :: CompositeArray idx c Repr
  foldExprs f (CompositeArray ilst arr) = do
    narr <- foldExprs (\(RevArray r) e -> f (RevCompositeArray r ilst) e
                      ) arr
    return (CompositeArray ilst narr)
  accessComposite (RevCompositeArray r ilst) (CompositeArray ilst' arr)
    = case geq ilst ilst' of
    Just Refl -> accessComposite (RevArray r) arr

instance (Composite idx,Composite c) => Show (RevCompositeArray idx c tp) where
  showsPrec p (RevCompositeArray rev idx)
    = showParen (p>10) $
      showString "RevCompositeArray " .
      gshowsPrec 11 rev . showChar ' ' .
      gshowsPrec 11 idx      

instance (Composite idx,Composite c) => GShow (RevCompositeArray idx c) where
  gshowsPrec = showsPrec

instance (Composite idx,Composite c) => GEq (RevCompositeArray idx c) where
  geq (RevCompositeArray r1 idx1) (RevCompositeArray r2 idx2) = do
    Refl <- geq r1 r2
    Refl <- geq idx1 idx2
    return Refl

instance (Composite idx,Composite c) => GCompare (RevCompositeArray idx c) where
  gcompare (RevCompositeArray r1 idx1) (RevCompositeArray r2 idx2)
    = case gcompare r1 r2 of
    GEQ -> case gcompare idx1 idx2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

select :: (Composite idx,Composite c,Embed m e,Monad m,GetType e) => CompositeArray idx c e -> idx e -> m (c e)
select (CompositeArray ilst arr) idx = case allFields idx of
  AnyList ilst' -> case geq ilst (runIdentity $ List.mapM (return.getType) ilst') of
    Just Refl -> Array.select arr ilst'

store :: (Composite idx,Composite c,Embed m e,Monad m,GetType e) => CompositeArray idx c e -> idx e -> c e -> m (CompositeArray idx c e)
store (CompositeArray ilst arr) idx el = case allFields idx of
  AnyList ilst' -> case geq ilst (runIdentity $ List.mapM (return.getType) ilst') of
    Just Refl -> do
      narr <- Array.store arr ilst' el
      return (CompositeArray ilst narr)
