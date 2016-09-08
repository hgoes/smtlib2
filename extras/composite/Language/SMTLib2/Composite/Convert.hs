module Language.SMTLib2.Composite.Convert where

import Language.SMTLib2 hiding (store,select)
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Lens

import Data.GADT.Show
import Data.GADT.Compare
import Control.Lens

class (Composite from,Composite to) => Convert from to where
  convert :: (Embed m e,Monad m,GetType e) => from e -> m (Maybe (to e))

data Fallback start alt (e :: Type -> *)
  = Start { _start :: start e }
  | Alternative { _alternative :: alt e }

start :: MaybeLens (Fallback start alt e) (start e)
start = lens (\f -> case f of
                 Start x -> Just x
                 _ -> Nothing)
        (\_ x -> Just (Start x))

alternative :: MaybeLens (Fallback start alt e) (alt e)
alternative = lens (\f -> case f of
                       Alternative x -> Just x
                       _ -> Nothing)
              (\_ x -> Just (Alternative x))

data RevFallback start alt tp where
  RevStart :: RevComp start tp -> RevFallback start alt tp
  RevAlternative :: RevComp alt tp -> RevFallback start alt tp

instance (Composite start,Composite alt,Convert start alt)
         => Composite (Fallback start alt) where
  type RevComp (Fallback start alt) = RevFallback start alt
  foldExprs f (Start e) = do
    ne <- foldExprs (f.RevStart) e
    return (Start ne)
  foldExprs f (Alternative e) = do
    ne <- foldExprs (f.RevAlternative) e
    return (Alternative ne)
  accessComposite (RevStart r) = start `composeMaybe` accessComposite r
  accessComposite (RevAlternative r) = alternative `composeMaybe` accessComposite r
  compCombine f (Start x) (Start y) = do
    z <- compCombine f x y
    case z of
      Just res -> return (Just (Start res))
      Nothing -> do
        nx <- convert x
        case nx of
          Nothing -> return Nothing
          Just nx' -> do
            ny <- convert y
            case ny of
              Nothing -> return Nothing
              Just ny' -> do
                res <- compCombine f nx' ny'
                return $ fmap Alternative res
  compCombine f (Start x) (Alternative y) = do
    nx <- convert x
    case nx of
      Nothing -> return Nothing
      Just nx' -> do
        res <- compCombine f nx' y
        return $ fmap Alternative res
  compCombine f (Alternative x) (Start y) = do
    ny <- convert y
    case ny of
      Nothing -> return Nothing
      Just ny' -> do
        res <- compCombine f x ny'
        return $ fmap Alternative res
  compCombine f (Alternative x) (Alternative y) = do
    res <- compCombine f x y
    return $ fmap Alternative res
  compCompare (Start x) (Start y) = compCompare x y
  compCompare (Start _) _ = LT
  compCompare _ (Start _) = GT
  compCompare (Alternative x) (Alternative y) = compCompare x y
  compShow p (Start x) = compShow p x
  compShow p (Alternative x) = compShow p x
  compInvariant (Start x) = compInvariant x
  compInvariant (Alternative x) = compInvariant x

instance (IsSingleton start,IsSingleton alt,
          SingletonType start ~ SingletonType alt,
          Convert start alt)
         => IsSingleton (Fallback start alt) where
  type SingletonType (Fallback start alt) = SingletonType start
  getSingleton (Start x) = getSingleton x
  getSingleton (Alternative x) = getSingleton x

instance (IsConstant start,IsConstant alt,
          SingletonType start ~ SingletonType alt,
          Convert start alt)
         => IsConstant (Fallback start alt) where
  getConstant (Start x) = getConstant x
  getConstant (Alternative x) = getConstant x

instance (IsRanged start,IsRanged alt,
          SingletonType start ~ SingletonType alt,
          Convert start alt)
         => IsRanged (Fallback start alt) where
  getRange (Start x) = getRange x
  getRange (Alternative x) = getRange x

instance (Container start,Container alt,
          ElementType start ~ ElementType alt,
          Convert start alt)
         => Container (Fallback start alt) where
  type ElementType (Fallback start alt) = ElementType start
  elementType (Start x) = elementType x
  elementType (Alternative x) = elementType x

instance (IsArray start idx,IsArray alt idx,
          ElementType start ~ ElementType alt,
          Convert start alt)
         => IsArray (Fallback start alt) idx where
  newArray idx el = do
    arr <- newArray idx el
    return $ Start arr
  select (Start arr :: Fallback start alt e) idx = do
    el <- select arr idx
    case el of
      Just res -> return $ Just res
      Nothing -> do
        narr <- convert arr
        case narr of
          Nothing -> return Nothing
          Just narr' -> select (narr' :: alt e) idx
  select (Alternative arr) idx = select arr idx
  store (Start arr) idx el = do
    narr <- store arr idx el
    case narr of
      Just res -> return $ Just (Start res)
      Nothing -> do
        arr2 <- convert arr
        case arr2 of
          Nothing -> return Nothing
          Just arr2' -> do
            narr2 <- store arr2' idx el
            return $ fmap Alternative narr2
  store (Alternative arr) idx el = do
    narr <- store arr idx el
    return $ fmap Alternative narr

instance (IsBounded start idx,IsBounded alt idx,
          ElementType start ~ ElementType alt,
          Convert start alt)
         => IsBounded (Fallback start alt) idx where
  checkIndex (Start x) idx = checkIndex x idx
  checkIndex (Alternative x) idx = checkIndex x idx

instance (Composite start,Composite alt) => GShow (RevFallback start alt) where
  gshowsPrec p (RevStart r) = showParen (p>10) $ showString "RevStart " . gshowsPrec 11 r
  gshowsPrec p (RevAlternative r) = showParen (p>10) $ showString "RevAlternative " . gshowsPrec 11 r

instance (Composite start,Composite alt) => GEq (RevFallback start alt) where
  geq (RevStart x) (RevStart y) = do
    Refl <- geq x y
    return Refl
  geq (RevAlternative x) (RevAlternative y) = do
    Refl <- geq x y
    return Refl
  geq _ _ = Nothing

instance (Composite start,Composite alt) => GCompare (RevFallback start alt) where
  gcompare (RevStart x) (RevStart y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevStart _) _ = GLT
  gcompare _ (RevStart _) = GGT
  gcompare (RevAlternative x) (RevAlternative y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
