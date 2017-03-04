module Language.SMTLib2.Composite.List where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Container
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Null

import Data.List (genericIndex,genericLength)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Maybe (catMaybes)
import Data.GADT.Show
import Data.GADT.Compare
import Text.Show
import Data.Foldable
import Control.Monad.Except

data RevList a tp = RevList !Int !(RevComp a tp)

newtype CompList a (e :: Type -> *) = CompList { compList :: Vector (a e) }

instance Composite a => Composite (CompList a) where
  type RevComp (CompList a) = RevList a
  foldExprs f (CompList vec) = do
    nvec <- Vec.imapM (\n -> foldExprs (f . RevList n)) vec
    return $ CompList nvec
  getRev (RevList n r) (CompList lst) = do
    el <- lst Vec.!? n
    getRev r el
  setRev (RevList n r) x (Just (CompList lst)) = do
    nel <- setRev r x (lst Vec.!? n)
    let nlst = lst Vec.// [(n,nel)]
    return $ CompList nlst
  setRev _ _ _ = Nothing
  compCombine f (CompList xs) (CompList ys) = do
    res <- runExceptT (do
                          zs <- Vec.zipWithM (\x y -> do
                                                 z <- lift $ compCombine f x y
                                                 case z of
                                                   Just nz -> return nz
                                                   Nothing -> throwError ()
                                             ) xs ys
                          let lx = Vec.length xs
                              ly = Vec.length ys
                          return $ case compare lx ly of
                            EQ -> zs
                            LT -> zs Vec.++ Vec.drop lx ys
                            GT -> zs Vec.++ Vec.drop ly xs)
    case res of
      Right r -> return (Just $ CompList r)
      Left () -> return Nothing
  compCompare (CompList xs) (CompList ys)
    = case compare (Vec.length xs) (Vec.length ys) of
    EQ -> let zs = Vec.zipWith compCompare xs ys
          in mconcat $ Vec.toList zs
  compShow = showsPrec
  compInvariant (CompList xs) = fmap concat $ mapM compInvariant $ Vec.toList xs

instance Composite el => Container (CompList el) where
  data Index (CompList el) el' e where
    ListIndex :: !Int -> Index (CompList el) el e
  elementGet (CompList lst) (ListIndex i) = case lst Vec.!? i of
    Nothing -> error $ "elementGet{CompList}: Index "++show i++" out of range."
    Just res -> return res
  elementSet (CompList lst) (ListIndex i) x
    = return $ CompList $ lst Vec.// [(i,x)]
  elementsSet (CompList lst) upd
    = return $ CompList $ lst Vec.// [ (i,nel) | (ListIndex i,nel) <- upd ]
  showIndex p (ListIndex i) = showsPrec p i

dynamicAt :: (Composite a,Integral (Value tp),Embed m e,Monad m)
          => Maybe (Range tp) -> e tp
          -> Access (CompList a) ('Seq a 'Id) a m e
dynamicAt (Just (asFiniteRange -> Just [val])) _
  = \l@(CompList lst)
    -> let idx = fromIntegral val
       in if idx >= 0 &&
             idx < Vec.length lst
       then at (ListIndex idx) l
       else return $ AccSeq []
dynamicAt rng i = \(CompList lst)
                  -> fmap (AccSeq . catMaybes) $
                     mapM (\(el,idx) -> do
                              let vidx = fromIntegral idx
                              case rng of
                                Just rng'
                                  | not (includes vidx rng')
                                    -> return Nothing
                                _ -> do
                                  cond <- i .==. constant vidx
                                  return $ Just (ListIndex idx,[cond],AccId)
                          ) (zip (Vec.toList lst) [0..])

instance (Composite a,GShow e) => Show (CompList a e) where
  showsPrec _ (CompList xs) = showListWith (compShow 0) (Vec.toList xs)

instance CompositeExtract a => CompositeExtract (CompList a) where
  type CompExtract (CompList a) = Vector (CompExtract a)
  compExtract f (CompList xs) = Vec.mapM (compExtract f) xs

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

{-data RevList a tp = RevList !Integer !(RevComp a tp)

newtype CompList a (e :: Type -> *) = CompList { compList :: [a e] }

instance Composite a => Composite (CompList a) where
  type RevComp (CompList a) = RevList a
  foldExprs f (CompList lst) = do
    nlst <- mapM (\(n,el) -> foldExprs (f . RevList n) el) (zip [0..] lst)
    return (CompList nlst)
  getRev (RevList n r) (CompList lst) = do
    el <- safeGenericIndex lst n
    getRev r el
  setRev (RevList n r) x (Just (CompList lst)) = do
    nel <- setRev r x (safeGenericIndex lst n)
    nlst <- safeGenericInsertAt n nel lst
    return $ CompList nlst
  setRev _ _ _ = Nothing
  withRev (RevList n r) (CompList lst) f = do
    nlst <- safeGenericUpdateAt (return []) n (\el -> withRev r el f) lst
    return (CompList nlst)
  compCombine f (CompList xs) (CompList ys) = fmap (fmap CompList) $ merge xs ys
    where
      merge [] ys = return (Just ys)
      merge xs [] = return (Just xs)
      merge (x:xs) (y:ys) = do
        z <- compCombine f x y
        case z of
          Just z' -> do
            zs <- merge xs ys
            return $ fmap (z':) zs
          Nothing -> return Nothing
  compCompare (CompList xs) (CompList ys) = comp xs ys
    where
      comp [] [] = EQ
      comp [] _  = LT
      comp _ []  = GT
      comp (x:xs) (y:ys) = case compCompare x y of
        EQ -> comp xs ys
        r -> r
  compShow = showsPrec
  compInvariant (CompList xs) = fmap concat $ mapM compInvariant xs

instance Composite el => Container (CompList el) where
  data Index (CompList el) el' e where
    ListIndex :: Integer -> Index (CompList el) el e
  elementGet (CompList lst) (ListIndex i) = case safeGenericIndex lst i of
    Nothing -> error $ "elementGet{CompList}: Index "++show i++" out of range."
    Just res -> return res
  elementsGet lst [] = return []
  elementsGet (CompList lst) idxs@(ListIndex _:_)
    = return $ get 0 lst
      (fmap (\(ListIndex i) -> i) idxs)
    where
      get :: Integer -> [a] -> [Integer] -> [a]
      get _ _ [] = []
      get n (x:xs) (i:is)
        | i==n      = x:get (n+1) xs is
        | otherwise = get (n+1) xs (i:is)
      get _ [] _ = error "elementsGet{CompList}: Index out of range."
  elementSet (CompList lst) (ListIndex i) x
    = case safeGenericUpdateAt Nothing i (\_ -> Just x) lst of
    Just nlst -> return (CompList nlst)
    Nothing -> error $ "elementSet{CompList}: Index "++show i++" out of range."
  elementsSet lst [] = return lst
  elementsSet (CompList lst) upd@((ListIndex _,_):_)
    = return $ CompList $ set 0 lst
      (fmap (\(ListIndex i,x) -> (i,x)) upd)
    where
      set _ xs [] = xs
      set n (x:xs) is'@((i,nx):is)
        | n==i      = nx:set (n+1) xs is
        | otherwise =  x:set (n+1) xs is'
  withElement (CompList lst) (ListIndex i) f
    = fmap CompList $ safeGenericUpdateAt
      (error $ "withElement{CompList}: Index "++show i++" out of range.")
      i (\x -> f x) lst
  showIndex p (ListIndex i) = showsPrec p i

dynamicAt :: (Composite a,Integral (Value tp),Embed m e,Monad m)
          => Maybe (Range tp) -> e tp
          -> Access (CompList a) ('Seq a 'Id) a m e
dynamicAt (Just (asFiniteRange -> Just [val])) _
  = \l@(CompList lst)
    -> if val >= 0 &&
          val < genericLength lst
       then at (ListIndex $ toInteger val) l
       else return $ AccSeq []
dynamicAt rng i = \(CompList lst)
                  -> fmap (AccSeq . catMaybes) $
                     mapM (\(el,idx) -> do
                              let vidx = fromInteger idx
                              case rng of
                                Just rng'
                                  | not (includes vidx rng')
                                    -> return Nothing
                                _ -> do
                                  cond <- i .==. constant vidx
                                  return $ Just (ListIndex idx,[cond],AccId)
                          ) (zip lst [0..])

instance (Composite a,GShow e) => Show (CompList a e) where
  showsPrec _ (CompList xs) = showListWith (compShow 0) xs

{-instance (Composite a,IsRanged idx,
          Enum (Value (SingletonType idx))
         ) => IsArray (CompList a) idx where
  type ElementType (CompList a) = a
  select (CompList xs) idx = ites trgs
    where
      rng = getRange idx
      trgs = [ (x,i) | (x,i) <- zip xs [toEnum 0..]
                     , includes i rng ]
      ites [] = return Nothing
      ites [(el,_)] = return (Just el)
      ites ((el,v):rest) = do
        ifF <- ites rest
        case ifF of
          Nothing -> return Nothing
          Just ifF' -> do
            cond <- getSingleton idx .==. constant v
            compITE cond el ifF'
  store (CompList xs) idx nel = do
    nxs <- sequence updated
    return $ fmap CompList $ sequence nxs
    where
      rng = getRange idx
      updated = case isConst rng of
        Nothing -> [ if includes i rng
                     then do
                       cond <- getSingleton idx .==. constant i
                       compITE cond nel x
                     else return (Just x)
                   | (x,i) <- zip xs [toEnum 0..] ]
        Just ri -> [ if i==ri
                     then return (Just nel)
                     else return (Just x)
                   | (x,i) <- zip xs [toEnum 0..] ]-}

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
-}

safeGenericIndex :: (Num i,Eq i) => [a] -> i -> Maybe a
safeGenericIndex (x:xs) 0 = Just x
safeGenericIndex (_:xs) n = safeGenericIndex xs (n-1)
safeGenericIndex [] _ = Nothing

safeGenericInsertAt :: (Num i,Eq i) => i -> a -> [a] -> Maybe [a]
safeGenericInsertAt 0 x (_:ys) = Just $ x:ys
safeGenericInsertAt n x (y:ys) = do
  ys' <- safeGenericInsertAt (n-1) x ys
  return $ y:ys'
safeGenericInsertAt _ _ [] = Nothing

safeGenericUpdateAt :: (Num i,Eq i,Monad m) => m [a] -> i -> (a -> m a) -> [a] -> m [a]
safeGenericUpdateAt def 0 f (x:xs) = do
  nx <- f x
  return $ nx:xs
safeGenericUpdateAt def n f (x:xs) = do
  nxs <- safeGenericUpdateAt def (n-1) f xs
  return $ x:nxs
safeGenericUpdateAt def _ _ [] = def

--instance StaticByteWidth a => StaticByteWidth (CompList a) where
--  staticByteWidth (CompList xs) = sum $ fmap staticByteWidth xs

{-# SPECIALIZE safeGenericIndex :: [a] -> Integer -> Maybe a #-}
{-# SPECIALIZE safeGenericInsertAt :: Integer -> a -> [a] -> Maybe [a] #-}
{-# SPECIALIZE safeGenericUpdateAt :: Monad m => m [a] -> Integer -> (a -> m a) -> [a] -> m [a] #-}

