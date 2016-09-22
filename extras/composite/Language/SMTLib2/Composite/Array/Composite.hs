module Language.SMTLib2.Composite.Array.Composite
  (CompositeArray(..),
   RevCompositeArray(..),
   select,store) where

import Language.SMTLib2 hiding (select,store)
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Array
import Language.SMTLib2.Composite.Ranged
import Language.SMTLib2.Composite.Data
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Lens

import Control.Monad.State
import Data.Functor.Identity
import Data.GADT.Show
import Data.GADT.Compare
import Control.Lens

data AnyList (e :: Type -> *) = forall tps. AnyList (List e tps)

allFields :: (Composite c,GetType e) => c e -> AnyList e
allFields c = execState (foldExprs (\_ e -> do
                                       AnyList xs <- get
                                       put $ AnyList (e ::: xs)
                                       return e
                                   ) c) (AnyList Nil)

allFieldDescr :: Composite c => CompDescr c -> AnyList Repr
allFieldDescr descr = allFields descr

data CompositeArray (idx :: (Type -> *) -> *) c e
  = forall ilst. CompositeArray (CompArray ilst c e)

data RevCompositeArray (idx :: (Type -> *) -> *) c tp where
  RevCompositeArray :: RevComp c tp -> List Repr ilst -> RevCompositeArray idx c (ArrayType ilst tp)

instance (Composite idx,Composite c) => Composite (CompositeArray idx c) where
  type RevComp (CompositeArray idx c) = RevCompositeArray idx c
  foldExprs f (CompositeArray arr) = do
    narr <- foldExprs (\(RevArray r) e -> f (RevCompositeArray r (_indexDescr arr)) e
                      ) arr
    return (CompositeArray narr)
  accessComposite (RevCompositeArray r ilst)
    = lens (\(CompositeArray arr) -> do
               Refl <- geq ilst (_indexDescr arr)
               arr `getMaybe` accessComposite (RevArray r))
      (\(CompositeArray arr) x -> do
          Refl <- geq ilst (_indexDescr arr)
          narr <- setMaybe arr (accessComposite (RevArray r)) x
          return (CompositeArray narr))
  compCombine f (CompositeArray arr1) (CompositeArray arr2) = case geq (_indexDescr arr1) (_indexDescr arr2) of
    Just Refl -> do
      res <- compCombine f arr1 arr2
      case res of
        Just narr -> return $ Just $ CompositeArray narr
        Nothing -> return Nothing
    Nothing -> return Nothing
  compCompare (CompositeArray arr1) (CompositeArray arr2) = case gcompare (_indexDescr arr1) (_indexDescr arr2) of
    GEQ -> compCompare arr1 arr2
    GLT -> LT
    GGT -> GT
  compShow p (CompositeArray arr) = compShow p arr

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

instance (Composite c,Composite idx) => Container (CompositeArray idx c) where
  type ElementType (CompositeArray idx c) = c
  elementType (CompositeArray arr) = elementType arr

instance (Composite idx,Composite c) => IsArray (CompositeArray idx c) idx where
  newArray idx el = case allFields idx of
    AnyList ilst -> do
      arr <- newConstantArray ilst el
      return $ CompositeArray arr
  select (CompositeArray arr) idx = case allFields idx of
    AnyList ilst' -> case geq (_indexDescr arr) (runIdentity $ List.mapM (return.getType) ilst') of
      Just Refl -> fmap Just $ selectArray arr ilst'
  store (CompositeArray arr) idx el = case allFields idx of
    AnyList ilst' -> case geq (_indexDescr arr) (runIdentity $ List.mapM (return.getType) ilst') of
      Just Refl -> do
        narr <- storeArray arr ilst' el
        case narr of
          Nothing -> return Nothing
          Just narr' -> return $ Just $ CompositeArray narr'

instance (StaticByteAccess el res,CanConcat res,IsNumeric idx,StaticByteWidth el)
         => StaticByteAccess (CompositeArray idx el) res where
  staticByteRead comp@(CompositeArray arr :: CompositeArray idx el e) off sz = do
    let elementSize = staticByteWidth (elementDescr (compType arr))
        (idx,rest) = off `divMod` elementSize
    res <- read idx rest sz
    case res of
      Nothing -> return Nothing
      Just (els,nsz) -> do
        el <- compConcat els
        case el of
          Nothing -> return Nothing
          Just el' -> return $ Just (el',nsz)
    where
      read idx off sz = do
        idx' <- compositeFromValue (fromInteger idx)
        el <- select comp (idx' :: idx e)
        case el of
          Nothing -> return Nothing
          Just el' -> do
            res <- staticByteRead el' off sz
            case res of
              Nothing -> return Nothing
              Just (rd,0) -> return $ Just ([rd],0)
              Just (rd,rest) -> do
                rds <- read (idx+1) 0 rest
                case rds of
                  Nothing -> return Nothing
                  Just (rds',rest') -> return $ Just (rd:rds',rest')
  staticByteWrite comp@(CompositeArray arr :: CompositeArray idx el e) off el = do
    let elementSize = staticByteWidth (elementDescr (compType arr))
        (idx,rest) = off `divMod` elementSize
    write comp idx rest el
    where
      write arr idx off el = do
        idx' <- compositeFromValue (fromInteger idx)
        rd <- select comp (idx' :: idx e)
        case rd of
          Nothing -> return Nothing
          Just rd' -> do
            res <- staticByteWrite rd' off el
            case res of
              Nothing -> return Nothing
              Just (nrd,rest) -> do
                narr <- store arr idx' nrd
                case narr of
                  Nothing -> return Nothing
                  Just narr' -> case rest of
                    Nothing -> return $ Just (narr',Nothing)
                    Just rest' -> write narr' (idx+1) 0 rest'
      
