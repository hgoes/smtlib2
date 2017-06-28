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
  mapExprs f (CompList vec) = do
    nvec <- Vec.mapM (mapExprs f) vec
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
  compIsSubsetOf f (CompList xs) (CompList ys)
    = subset (Vec.toList xs) (Vec.toList ys)
    where
      subset [] _ = True
      subset (x:xs) (y:ys) = compIsSubsetOf f x y &&
                             subset xs ys
      subset _ _ = False
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

combineListWith :: (Embed m e,Monad m,GCompare e,Composite a)
                => (Int -> m (a e))
                -> (a e -> a e -> m (Maybe (a e)))
                -> CompList a e
                -> CompList a e
                -> m (Maybe (CompList a e))
combineListWith def f (CompList xs) (CompList ys) = do
  res <- runExceptT (do
                        zs <- Vec.zipWithM (\x y -> do
                                               z <- lift $ f x y
                                               case z of
                                                 Just nz -> return nz
                                                 Nothing -> throwError ()
                                           ) xs ys
                        let lx = Vec.length xs
                            ly = Vec.length ys
                        case compare lx ly of
                          EQ -> return zs
                          LT -> do
                            nys <- Vec.imapM
                                   (\i y -> do
                                       x <- lift $ def i
                                       z <- lift $ f x y
                                       case z of
                                         Just nz -> return nz
                                         Nothing -> throwError ())
                                   (Vec.drop lx ys)
                            return $ zs Vec.++ nys
                          GT -> do
                            nxs <- Vec.imapM
                                   (\i x -> do
                                       y <- lift $ def i
                                       z <- lift $ f x y
                                       case z of
                                         Just nz -> return nz
                                         Nothing -> throwError ())
                                   (Vec.drop ly xs)
                            return $ zs Vec.++ nxs)
  case res of
    Right r -> return (Just $ CompList r)
    Left () -> return Nothing

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

