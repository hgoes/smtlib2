module Language.SMTLib2.Composite.Convert where

import Language.SMTLib2 hiding (store,select)
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains

import Data.GADT.Show
import Data.GADT.Compare
import Data.Functor.Identity

class (Composite from,Composite to) => Convert from to where
  convert :: (Embed m e,Monad m) => from e -> m (Maybe (to e))

class ConvertC from to where
  convertC :: (Composite a,Embed m e,Monad m)
           => from a e -> m (Maybe (to a e))

data Fallback start alt (e :: Type -> *)
  = Start { _start :: start e }
  | Alternative { _alternative :: alt e }

data FallbackC start alt (a :: (Type -> *) -> *) (e :: Type -> *)
  = StartC { _startC :: start a e }
  | AlternativeC { _alternativeC :: alt a e }

data Fallback2 start alt1 alt2 (e :: Type -> *)
  = Start2 { _start2 :: start e }
  | Alternative2_1 { _alternative2_1 :: alt1 e }
  | Alternative2_2 { _alternative2_2 :: alt2 e }

fallback :: (Embed m e,Monad m,Convert start alt)
         => (start e -> start e -> m (Maybe (start e)))
         -> (alt e -> alt e -> m (Maybe (alt e)))
         -> Fallback start alt e
         -> Fallback start alt e
         -> m (Maybe (Fallback start alt e))
fallback f g fb1 fb2 = do
  res <- fallbackExtra (\s1 s2 -> fmap (fmap (\x -> (x,()))) $ f s1 s2)
         (\a1 a2 -> fmap (fmap (\x -> (x,()))) $ g a1 a2)
         fb1 fb2
  return $ fmap fst res

fallbackC :: (Embed m e,Monad m,Composite a,Composite (start a),Composite (alt a),ConvertC start alt)
          => (start a e -> start a e -> m (Maybe (start a e)))
          -> (alt a e -> alt a e -> m (Maybe (alt a e)))
          -> FallbackC start alt a e
          -> FallbackC start alt a e
          -> m (Maybe (FallbackC start alt a e))
fallbackC f g fb1 fb2 = do
  res <- fallbackExtraC (\s1 s2 -> fmap (fmap (\x -> (x,()))) $ f s1 s2)
         (\a1 a2 -> fmap (fmap (\x -> (x,()))) $ g a1 a2)
         fb1 fb2
  return $ fmap fst res

fallbackExtra :: (Embed m e,Monad m,Convert start alt)
              => (start e -> start e -> m (Maybe (start e,a)))
              -> (alt e -> alt e -> m (Maybe (alt e,a)))
              -> Fallback start alt e
              -> Fallback start alt e
              -> m (Maybe (Fallback start alt e,a))
fallbackExtra f g (Start x) (Start y) = do
  z <- f x y
  case z of
    Just (res,extra) -> return $ Just (Start res,extra)
    Nothing -> do
      nx <- convert x
      case nx of
        Just nx' -> fallbackExtra f g (Alternative nx') (Start y)
        Nothing -> return Nothing
fallbackExtra f g (Start x) (Alternative y) = do
  nx <- convert x
  case nx of
    Just nx' -> fallbackExtra f g (Alternative nx') (Alternative y)
    Nothing -> return Nothing
fallbackExtra f g (Alternative x) (Start y) = do
  ny <- convert y
  case ny of
    Just ny' -> fallbackExtra f g (Alternative x) (Alternative ny')
    Nothing -> return Nothing
fallbackExtra f g (Alternative x) (Alternative y) = do
  z <- g x y
  case z of
    Just (res,extra) -> return $ Just (Alternative res,extra)
    Nothing -> return Nothing

fallbackExtraC :: (Embed m e,Monad m,Composite el,Composite (start el),Composite (alt el),ConvertC start alt)
              => (start el e -> start el e -> m (Maybe (start el e,a)))
              -> (alt el e -> alt el e -> m (Maybe (alt el e,a)))
              -> FallbackC start alt el e
              -> FallbackC start alt el e
              -> m (Maybe (FallbackC start alt el e,a))
fallbackExtraC f g (StartC x) (StartC y) = do
  z <- f x y
  case z of
    Just (res,extra) -> return $ Just (StartC res,extra)
    Nothing -> do
      nx <- convertC x
      case nx of
        Just nx' -> fallbackExtraC f g (AlternativeC nx') (StartC y)
        Nothing -> return Nothing
fallbackExtraC f g (StartC x) (AlternativeC y) = do
  nx <- convertC x
  case nx of
    Just nx' -> fallbackExtraC f g (AlternativeC nx') (AlternativeC y)
    Nothing -> return Nothing
fallbackExtraC f g (AlternativeC x) (StartC y) = do
  ny <- convertC y
  case ny of
    Just ny' -> fallbackExtraC f g (AlternativeC x) (AlternativeC ny')
    Nothing -> return Nothing
fallbackExtraC f g (AlternativeC x) (AlternativeC y) = do
  z <- g x y
  case z of
    Just (res,extra) -> return $ Just (AlternativeC res,extra)
    Nothing -> return Nothing

mapFallback :: (Embed m e,Monad m)
            => (start e -> m (start' e))
            -> (alt e -> m (alt' e))
            -> Fallback start alt e
            -> m (Fallback start' alt' e)
mapFallback f g (Start x) = do
  nx <- f x
  return $ Start nx
mapFallback f g (Alternative x) = do
  nx <- g x
  return $ Alternative nx

fallback2 :: (Embed m e,Monad m,
              Convert start alt1,Convert start alt2,Convert alt1 alt2)
          => (start e -> start e -> m (Maybe (start e)))
          -> (alt1 e -> alt1 e -> m (Maybe (alt1 e)))
          -> (alt2 e -> alt2 e -> m (Maybe (alt2 e)))
          -> Fallback2 start alt1 alt2 e
          -> Fallback2 start alt1 alt2 e
          -> m (Maybe (Fallback2 start alt1 alt2 e))
fallback2 f g h fb1 fb2 = do
  res <- fallbackExtra2 (adj f) (adj g) (adj h) fb1 fb2
  return $ fmap fst res
  where
    adj c p q = fmap (fmap (\x -> (x,()))) $ c p q


fallbackExtra2 :: (Embed m e,Monad m,
                   Convert start alt1,Convert start alt2,Convert alt1 alt2)
               => (start e -> start e -> m (Maybe (start e,a)))
               -> (alt1 e -> alt1 e -> m (Maybe (alt1 e,a)))
               -> (alt2 e -> alt2 e -> m (Maybe (alt2 e,a)))
               -> Fallback2 start alt1 alt2 e
               -> Fallback2 start alt1 alt2 e
               -> m (Maybe (Fallback2 start alt1 alt2 e,a))
fallbackExtra2 f g h (Start2 x) (Start2 y) = do
  z <- f x y
  case z of
    Just (res,extra) -> return $ Just (Start2 res,extra)
    Nothing -> do
      nx <- convert x
      case nx of
        Just nx' -> fallbackExtra2 f g h (Alternative2_1 nx') (Start2 y)
        Nothing -> do
          nx2 <- convert x
          case nx2 of
            Nothing -> return Nothing
            Just nx2' -> fallbackExtra2 f g h (Alternative2_2 nx2') (Start2 y)
fallbackExtra2 f g h (Start2 x) (Alternative2_1 y) = do
  nx <- convert x
  case nx of
    Just nx' -> fallbackExtra2 f g h (Alternative2_1 nx') (Alternative2_1 y)
    Nothing -> do
      nx2 <- convert x
      case nx2 of
        Nothing -> return Nothing
        Just nx2' -> fallbackExtra2 f g h (Alternative2_2 nx2') (Alternative2_1 y)
fallbackExtra2 f g h (Start2 x) (Alternative2_2 y) = do
  nx <- convert x
  case nx of
    Nothing -> return Nothing
    Just nx' -> fallbackExtra2 f g h (Alternative2_2 nx') (Alternative2_2 y)
fallbackExtra2 f g h (Alternative2_1 x) (Start2 y) = do
  ny <- convert y
  case ny of
    Just ny' -> fallbackExtra2 f g h (Alternative2_1 x) (Alternative2_1 ny')
    Nothing -> do
      ny2 <- convert y
      case ny2 of
        Just ny2' -> fallbackExtra2 f g h (Alternative2_1 x) (Alternative2_2 ny2')
        Nothing -> return Nothing
fallbackExtra2 f g h (Alternative2_1 x) (Alternative2_1 y) = do
  z <- g x y
  case z of
    Just (res,extra) -> return $ Just (Alternative2_1 res,extra)
    Nothing -> do
      nx <- convert x
      case nx of
        Nothing -> return Nothing
        Just nx' -> fallbackExtra2 f g h (Alternative2_2 nx') (Alternative2_1 y)
fallbackExtra2 f g h (Alternative2_1 x) (Alternative2_2 y) = do
  nx <- convert x
  case nx of
    Nothing -> return Nothing
    Just nx' -> fallbackExtra2 f g h (Alternative2_2 nx') (Alternative2_2 y)
fallbackExtra2 f g h (Alternative2_2 x) (Start2 y) = do
  ny <- convert y
  case ny of
    Nothing -> return Nothing
    Just ny' -> fallbackExtra2 f g h (Alternative2_2 x) (Alternative2_2 ny')
fallbackExtra2 f g h (Alternative2_2 x) (Alternative2_1 y) = do
  ny <- convert y
  case ny of
    Nothing -> return Nothing
    Just ny' -> fallbackExtra2 f g h (Alternative2_2 x) (Alternative2_2 ny')
fallbackExtra2 f g h (Alternative2_2 x) (Alternative2_2 y) = do
  res <- h x y
  case res of
    Nothing -> return Nothing
    Just (res',extra) -> return $ Just (Alternative2_2 res',extra)

mapFallback2 :: (Embed m e,Monad m)
             => (start e -> m (start' e))
             -> (alt1 e -> m (alt1' e))
             -> (alt2 e -> m (alt2' e))
             -> Fallback2 start alt1 alt2 e
             -> m (Fallback2 start' alt1' alt2' e)
mapFallback2 f g h (Start2 x) = do
  nx <- f x
  return $ Start2 nx
mapFallback2 f g h (Alternative2_1 x) = do
  nx <- g x
  return $ Alternative2_1 nx
mapFallback2 f g h (Alternative2_2 x) = do
  nx <- h x
  return $ Alternative2_2 nx

convertFallback :: (Convert a b,Embed m e,Monad m)
                => Fallback a b e
                -> m (Maybe (Fallback a b e))
convertFallback (Start x) = do
  y <- convert x
  case y of
    Nothing -> return Nothing
    Just y' -> return $ Just (Alternative y')
convertFallback (Alternative x)
  = return $ Just (Alternative x)

data RevFallback start alt tp where
  RevStart :: RevComp start tp -> RevFallback start alt tp
  RevAlternative :: RevComp alt tp -> RevFallback start alt tp

data RevFallback2 start alt1 alt2 tp where
  RevStart2 :: RevComp start tp -> RevFallback2 start alt1 alt2 tp
  RevAlternative2_1 :: RevComp alt1 tp -> RevFallback2 start alt1 alt2 tp
  RevAlternative2_2 :: RevComp alt2 tp -> RevFallback2 start alt1 alt2 tp

instance (Composite start,Composite alt,Convert start alt)
         => Composite (Fallback start alt) where
  type RevComp (Fallback start alt) = RevFallback start alt
  foldExprs f (Start e) = do
    ne <- foldExprs (f.RevStart) e
    return (Start ne)
  foldExprs f (Alternative e) = do
    ne <- foldExprs (f.RevAlternative) e
    return (Alternative ne)
  mapExprs f (Start e) = do
    ne <- mapExprs f e
    return $ Start ne
  mapExprs f (Alternative e) = do
    ne <- mapExprs f e
    return $ Alternative ne
  getRev (RevStart r) (Start x) = getRev r x
  getRev (RevAlternative r) (Alternative x) = getRev r x
  getRev _ _ = Nothing
  setRev (RevStart r) x fb = do
    nel <- setRev r x (case fb of
                         Just (Start y) -> Just y
                         _ -> Nothing)
    return $ Start nel
  setRev (RevAlternative r) x fb = do
    nel <- setRev r x (case fb of
                         Just (Alternative y) -> Just y
                         _ -> Nothing)
    return $ Alternative nel
  compCombine f = fallback (compCombine f) (compCombine f)
  compCompare (Start x) (Start y) = compCompare x y
  compCompare (Start _) _ = LT
  compCompare _ (Start _) = GT
  compCompare (Alternative x) (Alternative y) = compCompare x y
  compShow p (Start x) = compShow p x
  compShow p (Alternative x) = compShow p x
  compInvariant (Start x) = compInvariant x
  compInvariant (Alternative x) = compInvariant x

instance (Composite a,Composite (start a),Composite (alt a),ConvertC start alt)
         => Composite (FallbackC start alt a) where
  type RevComp (FallbackC start alt a) = RevFallback (start a) (alt a)
  foldExprs f (StartC e) = do
    ne <- foldExprs (f.RevStart) e
    return (StartC ne)
  foldExprs f (AlternativeC e) = do
    ne <- foldExprs (f.RevAlternative) e
    return (AlternativeC ne)
  mapExprs f (StartC e) = do
    ne <- mapExprs f e
    return (StartC ne)
  mapExprs f (AlternativeC e) = do
    ne <- mapExprs f e
    return (AlternativeC ne)
  getRev (RevStart r) (StartC x) = getRev r x
  getRev (RevAlternative r) (AlternativeC x) = getRev r x
  getRev _ _ = Nothing
  setRev (RevStart r) x fb = do
    nel <- setRev r x (case fb of
                         Just (StartC y) -> Just y
                         _ -> Nothing)
    return $ StartC nel
  setRev (RevAlternative r) x fb = do
    nel <- setRev r x (case fb of
                         Just (AlternativeC y) -> Just y
                         _ -> Nothing)
    return $ AlternativeC nel
  compCombine f = fallbackC (compCombine f) (compCombine f)
  compCompare (StartC x) (StartC y) = compCompare x y
  compCompare (StartC _) _ = LT
  compCompare _ (StartC _) = GT
  compCompare (AlternativeC x) (AlternativeC y) = compCompare x y
  compShow p (StartC x) = compShow p x
  compShow p (AlternativeC x) = compShow p x
  compInvariant (StartC x) = compInvariant x
  compInvariant (AlternativeC x) = compInvariant x

instance (Composite start,Composite alt1,Composite alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => Composite (Fallback2 start alt1 alt2) where
  type RevComp (Fallback2 start alt1 alt2) = RevFallback2 start alt1 alt2
  foldExprs f (Start2 e) = do
    ne <- foldExprs (f.RevStart2) e
    return $ Start2 ne
  foldExprs f (Alternative2_1 e) = do
    ne <- foldExprs (f.RevAlternative2_1) e
    return $ Alternative2_1 ne
  foldExprs f (Alternative2_2 e) = do
    ne <- foldExprs (f.RevAlternative2_2) e
    return $ Alternative2_2 ne
  mapExprs f (Start2 e) = do
    ne <- mapExprs f e
    return $ Start2 ne
  mapExprs f (Alternative2_1 e) = do
    ne <- mapExprs f e
    return $ Alternative2_1 ne
  mapExprs f (Alternative2_2 e) = do
    ne <- mapExprs f e
    return $ Alternative2_2 ne
  getRev (RevStart2 r) (Start2 x) = getRev r x
  getRev (RevAlternative2_1 r) (Alternative2_1 x) = getRev r x
  getRev (RevAlternative2_2 r) (Alternative2_2 x) = getRev r x
  getRev _ _ = Nothing
  setRev (RevStart2 r) x fb = do
    nel <- setRev r x (case fb of
                         Just (Start2 y) -> Just y
                         _ -> Nothing)
    return $ Start2 nel
  setRev (RevAlternative2_1 r) x fb = do
    nel <- setRev r x (case fb of
                         Just (Alternative2_1 y) -> Just y
                         _ -> Nothing)
    return $ Alternative2_1 nel
  setRev (RevAlternative2_2 r) x fb = do
    nel <- setRev r x (case fb of
                         Just (Alternative2_2 y) -> Just y
                         _ -> Nothing)
    return $ Alternative2_2 nel
  compCombine f = fallback2 (compCombine f) (compCombine f) (compCombine f)
  compCompare (Start2 x) (Start2 y) = compCompare x y
  compCompare (Start2 _) _ = LT
  compCompare _ (Start2 _) = GT
  compCompare (Alternative2_1 x) (Alternative2_1 y) = compCompare x y
  compCompare (Alternative2_1 _) _ = LT
  compCompare _ (Alternative2_1 _) = GT
  compCompare (Alternative2_2 x) (Alternative2_2 y) = compCompare x y
  compShow p (Start2 x) = compShow p x
  compShow p (Alternative2_1 x) = compShow p x
  compShow p (Alternative2_2 x) = compShow p x
  compInvariant (Start2 x) = compInvariant x
  compInvariant (Alternative2_1 x) = compInvariant x
  compInvariant (Alternative2_2 x) = compInvariant x

instance (Convert start alt,
          Convert start x,Convert alt x) => Convert (Fallback start alt) x where
  convert (Start x) = convert x
  convert (Alternative x) = convert x

instance (Convert start alt1,Convert start alt2,Convert alt1 alt2,
          Convert start x,Convert alt1 x,Convert alt2 x) => Convert (Fallback2 start alt1 alt2) x where
  convert (Start2 x) = convert x
  convert (Alternative2_1 x) = convert x
  convert (Alternative2_2 x) = convert x

instance (IsSingleton start,IsSingleton alt,
          SingletonType start ~ SingletonType alt,
          Convert start alt)
         => IsSingleton (Fallback start alt) where
  type SingletonType (Fallback start alt) = SingletonType start
  getSingleton (Start x) = getSingleton x
  getSingleton (Alternative x) = getSingleton x

instance (IsSingleton start,IsSingleton alt1,IsSingleton alt2,
          SingletonType start ~ SingletonType alt1,
          SingletonType start ~ SingletonType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => IsSingleton (Fallback2 start alt1 alt2) where
  type SingletonType (Fallback2 start alt1 alt2) = SingletonType start
  getSingleton (Start2 x) = getSingleton x
  getSingleton (Alternative2_1 x) = getSingleton x
  getSingleton (Alternative2_2 x) = getSingleton x

instance (IsConstant start,IsConstant alt,
          SingletonType start ~ SingletonType alt,
          Convert start alt)
         => IsConstant (Fallback start alt) where
  getConstant (Start x) = getConstant x
  getConstant (Alternative x) = getConstant x

instance (IsConstant start,IsConstant alt1,IsConstant alt2,
          SingletonType start ~ SingletonType alt1,
          SingletonType start ~ SingletonType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => IsConstant (Fallback2 start alt1 alt2) where
  getConstant (Start2 x) = getConstant x
  getConstant (Alternative2_1 x) = getConstant x
  getConstant (Alternative2_2 x) = getConstant x

instance (IsRanged start,IsRanged alt,
          SingletonType start ~ SingletonType alt,
          Convert start alt)
         => IsRanged (Fallback start alt) where
  getRange (Start x) = getRange x
  getRange (Alternative x) = getRange x

instance (IsRanged start,IsRanged alt1,IsRanged alt2,
          SingletonType start ~ SingletonType alt1,
          SingletonType start ~ SingletonType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => IsRanged (Fallback2 start alt1 alt2) where
  getRange (Start2 x) = getRange x
  getRange (Alternative2_1 x) = getRange x
  getRange (Alternative2_2 x) = getRange x

instance (Wrapper start,Wrapper alt,
          ElementType start ~ ElementType alt,
          Convert start alt)
         => Wrapper (Fallback start alt) where
  type ElementType (Fallback start alt) = ElementType start
  elementType (Start x) = elementType x
  elementType (Alternative x) = elementType x

instance (Wrapper start,Wrapper alt1,Wrapper alt2,
          ElementType start ~ ElementType alt1,
          ElementType start ~ ElementType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => Wrapper (Fallback2 start alt1 alt2) where
  type ElementType (Fallback2 start alt1 alt2) = ElementType start
  elementType (Start2 x) = elementType x
  elementType (Alternative2_1 x) = elementType x
  elementType (Alternative2_2 x) = elementType x

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

instance (IsArray start idx,IsArray alt1 idx,IsArray alt2 idx,
          ElementType start ~ ElementType alt1,
          ElementType start ~ ElementType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => IsArray (Fallback2 start alt1 alt2) idx where
  newArray idx el = do
    arr <- newArray idx el
    return $ Start2 arr
  select (Start2 arr :: Fallback2 start alt1 alt2 e) idx = do
    el <- select arr idx
    case el of
      Just res -> return $ Just res
      Nothing -> do
        arr1 <- convert arr
        case arr1 of
          Just arr1' -> select (Alternative2_1 arr1' :: Fallback2 start alt1 alt2 e) idx
          Nothing -> do
            arr2 <- convert arr
            case arr2 of
              Nothing -> return Nothing
              Just arr2' -> select (Alternative2_2 arr2' :: Fallback2 start alt1 alt2 e) idx
  select (Alternative2_1 arr :: Fallback2 start alt1 alt2 e) idx = do
    el <- select arr idx
    case el of
      Just res -> return $ Just res
      Nothing -> do
        arr1 <- convert arr
        case arr1 of
          Nothing -> return Nothing
          Just arr1' -> select (Alternative2_2 arr1' :: Fallback2 start alt1 alt2 e) idx
  select (Alternative2_2 arr) idx = select arr idx
  store (Start2 arr :: Fallback2 start alt1 alt2 e) idx el = do
    narr <- store arr idx el
    case narr of
      Just res -> return $ Just (Start2 res)
      Nothing -> do
        arr1 <- convert arr
        case arr1 of
          Just arr1' -> store (Alternative2_1 arr1' :: Fallback2 start alt1 alt2 e) idx el
          Nothing -> do
            arr2 <- convert arr
            case arr2 of
              Just arr2' -> store (Alternative2_2 arr2' :: Fallback2 start alt1 alt2 e) idx el
              Nothing -> return Nothing
  store (Alternative2_1 arr :: Fallback2 start alt1 alt2 e) idx el = do
    narr <- store arr idx el
    case narr of
      Just res -> return $ Just $ Alternative2_1 res
      Nothing -> do
        arr1 <- convert arr
        case arr1 of
          Just arr1' -> store (Alternative2_2 arr1' :: Fallback2 start alt1 alt2 e) idx el
          Nothing -> return Nothing
  store (Alternative2_2 arr) idx el = do
    narr <- store arr idx el
    case narr of
      Nothing -> return Nothing
      Just res -> return $ Just $ Alternative2_2 res

instance (IsStaticBounded start,IsStaticBounded alt,
          ElementType start ~ ElementType alt,
          Convert start alt)
         => IsStaticBounded (Fallback start alt) where
  checkStaticIndex (Start x) = checkStaticIndex x
  checkStaticIndex (Alternative x) = checkStaticIndex x

instance (IsBounded start idx,IsBounded alt idx,
          ElementType start ~ ElementType alt,
          Convert start alt)
         => IsBounded (Fallback start alt) idx where
  checkIndex (Start x) = checkIndex x
  checkIndex (Alternative x) = checkIndex x
  arraySize (Start x) = arraySize x
  arraySize (Alternative x) = arraySize x

instance (IsStaticBounded start,IsStaticBounded alt1,IsStaticBounded alt2,
          ElementType start ~ ElementType alt1,
          ElementType start ~ ElementType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => IsStaticBounded (Fallback2 start alt1 alt2) where
  checkStaticIndex (Start2 x) = checkStaticIndex x
  checkStaticIndex (Alternative2_1 x) = checkStaticIndex x
  checkStaticIndex (Alternative2_2 x) = checkStaticIndex x

instance (IsBounded start idx,IsBounded alt1 idx,IsBounded alt2 idx,
          ElementType start ~ ElementType alt1,
          ElementType start ~ ElementType alt2,
          Convert start alt1,Convert start alt2,Convert alt1 alt2)
         => IsBounded (Fallback2 start alt1 alt2) idx where
  checkIndex (Start2 x) = checkIndex x
  checkIndex (Alternative2_1 x) = checkIndex x
  checkIndex (Alternative2_2 x) = checkIndex x
  arraySize (Start2 x) = arraySize x
  arraySize (Alternative2_1 x) = arraySize x
  arraySize (Alternative2_2 x) = arraySize x

instance (Composite start,Composite alt) => GShow (RevFallback start alt) where
  gshowsPrec p (RevStart r) = showParen (p>10) $ showString "RevStart " . gshowsPrec 11 r
  gshowsPrec p (RevAlternative r) = showParen (p>10) $ showString "RevAlternative " . gshowsPrec 11 r

instance (Composite start,Composite alt1,Composite alt2)
         => GShow (RevFallback2 start alt1 alt2) where
  gshowsPrec p (RevStart2 r) = showParen (p>10) $ showString "RevStart2 " . gshowsPrec 11 r
  gshowsPrec p (RevAlternative2_1 r) = showParen (p>10) $ showString "RevAlternative2_1 " . gshowsPrec 11 r
  gshowsPrec p (RevAlternative2_2 r) = showParen (p>10) $ showString "RevAlternative2_2 " . gshowsPrec 11 r

instance (Composite start,Composite alt) => GEq (RevFallback start alt) where
  geq (RevStart x) (RevStart y) = geq x y
  geq (RevAlternative x) (RevAlternative y) = geq x y
  geq _ _ = Nothing

instance (Composite start,Composite alt1,Composite alt2)
         => GEq (RevFallback2 start alt1 alt2) where
  geq (RevStart2 x) (RevStart2 y) = geq x y
  geq (RevAlternative2_1 x) (RevAlternative2_1 y) = geq x y
  geq (RevAlternative2_2 x) (RevAlternative2_2 y) = geq x y
  geq _ _ = Nothing

instance (Composite start,Composite alt) => GCompare (RevFallback start alt) where
  gcompare (RevStart x) (RevStart y) = gcompare x y
  gcompare (RevStart _) _ = GLT
  gcompare _ (RevStart _) = GGT
  gcompare (RevAlternative x) (RevAlternative y) = gcompare x y

instance (Composite start,Composite alt1,Composite alt2)
         => GCompare (RevFallback2 start alt1 alt2) where
  gcompare (RevStart2 x) (RevStart2 y) = gcompare x y
  gcompare (RevStart2 _) _ = GLT
  gcompare _ (RevStart2 _) = GGT
  gcompare (RevAlternative2_1 x) (RevAlternative2_1 y) = gcompare x y
  gcompare (RevAlternative2_1 _) _ = GLT
  gcompare _ (RevAlternative2_1 _) = GGT
  gcompare (RevAlternative2_2 x) (RevAlternative2_2 y) = gcompare x y

instance (IsNumeric start,IsNumeric alt,Convert start alt
         ) => IsNumeric (Fallback start alt) where
  compositeFromInteger i (Start r) = case compositeFromInteger i r of
    Just r -> Just $ Start r
    Nothing -> do
      nr <- runIdentity $ convert r
      res <- compositeFromInteger i nr
      return $ Alternative res
  compositeFromInteger i (Alternative r)
    = fmap Alternative $ compositeFromInteger i r
  compositeToInteger (Start i) = compositeToInteger i
  compositeToInteger (Alternative i) = compositeToInteger i
  compositePlus = fallback compositePlus compositePlus
  compositeMinus = fallback compositeMinus compositeMinus
  compositeSum xs = case mapM (\x -> case x of
                                  Start x' -> Just x'
                                  Alternative _ -> Nothing
                              ) xs of
    Just xs' -> do
      res <- compositeSum xs'
      case res of
        Just r -> return $ Just $ Start r
        Nothing -> conv
    Nothing -> conv
    where
      conv =  do
        xs' <- mapM (\x -> case x of
                        Start x' -> convert x'
                        Alternative x' -> return $ Just x'
                    ) xs
        case sequence xs' of
          Nothing -> return Nothing
          Just xs'' -> do
            res <- compositeSum xs''
            case res of
              Nothing -> return Nothing
              Just r -> return $ Just $ Alternative r
  compositeNegate (Start x) = do
    res <- compositeNegate x
    case res of
      Just r -> return $ Just $ Start r
      Nothing -> do
        nx <- convert x
        case nx of
          Nothing -> return Nothing
          Just nx' -> do
            res <- compositeNegate nx'
            return $ fmap Alternative res
  compositeMult = fallback compositeMult compositeMult
  compositeGEQ (Start x::Fallback start alt e) (Start y) = do
    res <- compositeGEQ x y
    case res of
      Just r -> return $ Just r
      Nothing -> do
        nx <- convert x
        case nx of
          Nothing -> return Nothing
          Just nx' -> do
            ny <- convert y
            case ny of
              Nothing -> return Nothing
              Just ny' -> compositeGEQ (nx'::alt e) ny'
  compositeGEQ (Alternative x) (Alternative y) = compositeGEQ x y
  compositeGEQ (Start x) y = do
    nx <- convert x
    case nx of
      Nothing -> return Nothing
      Just nx' -> compositeGEQ (Alternative nx') y
  compositeGEQ x (Start y) = do
    ny <- convert y
    case ny of
      Nothing -> return Nothing
      Just ny' -> compositeGEQ x (Alternative ny')
  compositeDiv = fallback compositeDiv compositeDiv
  compositeMod = fallback compositeMod compositeMod

instance (CanConcat start,CanConcat alt,Convert start alt) => CanConcat (Fallback start alt) where
  withConcat f xs = case mapM (\x -> case x of
                                  Start x' -> return x'
                                  Alternative _ -> Nothing
                              ) xs of
    Nothing -> conv
    Just xs' -> do
      res <- withConcat (\x -> do
                            (res,nx) <- f (Start x)
                            case nx of
                              Start nx' -> return (Just res,nx')
                              _ -> return (Nothing,x)
                        ) xs'
      case res of
        Nothing -> conv
        Just (Nothing,_) -> conv
        Just (Just r,nxs) -> return $ Just (r,fmap Start nxs)
    where
      conv = do
        xs' <- mapM (\x -> case x of
                        Start x -> convert x
                        Alternative x -> return $ Just x
                    ) xs
        case sequence xs' of
          Nothing -> return Nothing
          Just xs'' -> do
            res <- withConcat (\x -> do
                                  (res,nx) <- f (Alternative x)
                                  case nx of
                                    Alternative nx' -> return (Just res,nx')
                                    _ -> return (Nothing,x)
                              ) xs''
            case res of
              Just (Just r,nxs) -> return $ Just (r,fmap Alternative nxs)
              _ -> return Nothing
