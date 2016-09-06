module Language.SMTLib2.Composite.List where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Lens

import Data.List (genericIndex)
import Data.GADT.Show
import Data.GADT.Compare
import Text.Show
import Data.Foldable
import Control.Lens

data RevList a tp = RevList Integer (RevComp a tp)

newtype CompList a (e :: Type -> *) = CompList { _compList :: [a e] }

makeLenses ''CompList

instance Composite a => Composite (CompList a) where
  type RevComp (CompList a) = RevList a
  foldExprs f (CompList lst) = do
    nlst <- mapM (\(n,el) -> foldExprs (f . RevList n) el) (zip [0..] lst)
    return (CompList nlst)
  accessComposite (RevList n r)
    = maybeLens compList `composeMaybe`
      lens (\lst -> lst `safeGenericIndex` n)
           (\lst nel -> safeGenericInsertAt n nel lst) `composeMaybe`
      accessComposite r
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
  compShow _ (CompList xs) = showListWith (compShow 0) xs
  compInvariant (CompList xs) = fmap concat $ mapM compInvariant xs

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

listElement :: Integer -> CompLens (CompList a) a
listElement i = liftLens $ compList . _elem i
  where
    _elem :: Integer -> Lens' [a] a
    _elem i = lens (`genericIndex` i) (flip $ insertAt i)

    insertAt :: Integer -> a -> [a] -> [a]
    insertAt 0 x (_:ys) = x:ys
    insertAt n x (y:ys) = y:insertAt (n-1) x ys

listElement' :: (Num i,Eq i) => i -> MaybeLens [a] a
listElement' i = lens (\xs -> safeGenericIndex xs i)
                 (\xs x -> safeGenericInsertAt i x xs)

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
