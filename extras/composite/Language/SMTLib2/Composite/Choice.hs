{-# LANGUAGE DataKinds,GADTs,TypeFamilies,ExistentialQuantification,ScopedTypeVariables,RankNTypes #-}
module Language.SMTLib2.Composite.Choice
  (Choice(),ChoiceEncoding(..),
   -- * Encodings
   boolEncoding,intEncoding,bvEncoding,dtEncoding,possibleChoices,
   -- * Constructor
   singleton,initial,
   -- * Functions
   getChosen,setChosen,getChoiceValues,getChoices,mapChoices
  ) where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Container
import Language.SMTLib2.Composite.List
import Language.SMTLib2.Composite.Tuple
import Language.SMTLib2.Composite.Singleton
import Language.SMTLib2.Composite.Null
import Language.SMTLib2
import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.GADT.Show
import Data.GADT.Compare
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Identity
import Data.Typeable
import Data.List (genericIndex,sortBy)
import Data.Ord (comparing)
import Control.Monad.Except
import Text.Show
import Data.Maybe

data ChoiceEncoding = BoolEncoding
                    | ValueEncoding Type

data Choice enc c e where
  ChoiceSingleton :: c e -> Choice BoolEncoding c e
  ChoiceBool :: [(c e,e BoolType)] -> Choice BoolEncoding c e
  ChoiceValue :: [(c e,Value tp)] -> e tp -> Choice (ValueEncoding tp) c e

singleton :: (Composite c,Embed m e,Monad m,GetType e) => Choice enc c Repr -> c e -> m (Choice enc c e)
singleton (ChoiceSingleton _) x = return $ ChoiceSingleton x
singleton (ChoiceBool _) x = return $ ChoiceSingleton x
singleton (ChoiceValue mp _) x = case lookupBy (\(el,_) -> compCompare (compType x) el) mp of
  Just (_,key) -> do
    val <- constant key
    return $ ChoiceValue [(x,key)] val

boolEncoding :: Composite c => [c Repr] -> Choice BoolEncoding c Repr
boolEncoding [c] = ChoiceSingleton c
boolEncoding cs  = ChoiceBool $ zip (normalizeList compCompare cs) (repeat bool)

intEncoding :: Composite c => [c Repr] -> Choice (ValueEncoding IntType) c Repr
intEncoding xs = ChoiceValue (zip (normalizeList compCompare xs) [ IntValue n | n <- [0..] ]) int

bvEncoding :: Composite c => [c Repr]
           -> (forall bw. Choice (ValueEncoding (BitVecType bw)) c Repr -> a)
           -> a
bvEncoding xs f = reifyNat bits $ \bw -> f $ ChoiceValue
                                         (zip (normalizeList compCompare xs)
                                          [ BitVecValue n bw | n <- [0..] ])
                                         (bitvec bw)
  where
    bits = ceiling $ logBase 2 (fromIntegral size :: Double)
    size = length xs

data EncodingElement a (sig :: [Type]) where
  EncodingElement :: a -> DynamicConstructor '[] -> EncodingElement a '[]

-- | Like `reifyList`, but specialized on Type-kinded lists so we can have Typeable instances
reifyTypeList :: (forall r'. a -> (forall (tp::[Type]). Typeable tp => e tp -> r') -> r')
          -> [a] -> (forall (tp :: [[Type]]). Typeable tp => List e tp -> r)
          -> r
reifyTypeList _ [] g = g Nil
reifyTypeList f (x:xs) g = f x $ \x' -> reifyTypeList f xs $ \xs' -> g (x' ::: xs')

dtEncoding :: (Composite c,Backend b) => String -> [(String,c Repr)]
           -> (forall dt. Choice (ValueEncoding (DataType (DynamicValue dt))) c Repr -> SMT b a)
           -> SMT b a
dtEncoding dtName (els :: [(String,c Repr)]) g
  = reifyTypeList
  (\(con,el) f -> f (EncodingElement el (DynConstructor Nil con))) (normalizeList (\(_,x) (_,y) -> compCompare x y) els) $
  \(cons :: List (EncodingElement (c Repr)) sig)
  -> let cons' = runIdentity $ List.mapM
           (\(EncodingElement _ con) -> return con) cons
         tp :: DynamicDatatype sig
         tp = DynDatatype cons' dtName
         tp' :: Datatype (DynamicValue sig)
         tp' = DynDatatypeInfo tp
         vals = runIdentity $ List.toListIndex
           (\idx (EncodingElement el con) -> return (el,DataValue tp' (DynValue tp idx Nil))) cons
     in do
    registerDatatype tp'
    g $ ChoiceValue vals (DataRepr tp')

data RevChoice enc c t where
  RevChoiceBool :: Integer -> RevChoice BoolEncoding c BoolType
  RevChoiceValue :: RevChoice (ValueEncoding t) c t
  RevChoiceElement :: Integer -> RevComp c tp -> RevChoice enc c tp

instance (Composite c) => Composite (Choice enc c) where
  type RevComp (Choice enc a) = RevChoice enc a
  foldExprs f (ChoiceSingleton x) = do
    nx <- foldExprs (\rev -> f (RevChoiceElement 0 rev)
                    ) x
    return (ChoiceSingleton nx)
  foldExprs f (ChoiceBool lst) = do
    nlst <- mapM (\(i,(el,cond)) -> do
                     nel <- foldExprs (\rev -> f (RevChoiceElement i rev)
                                      ) el
                     ncond <- f (RevChoiceBool i) cond
                     return (nel,ncond)
                 ) $ zip [0..] lst
    return $ ChoiceBool nlst
  foldExprs f (ChoiceValue lst v) = do
    nv <- f RevChoiceValue v
    nlst <- mapM (\(i,(el,val)) -> do
                     nel <- foldExprs (\rev -> f (RevChoiceElement i rev)) el
                     return (nel,val)
                 ) $ zip [0..] lst
    return (ChoiceValue nlst nv)
  getRev (RevChoiceBool i) (ChoiceBool lst) = do
    (_,cond) <- safeGenericIndex lst i
    return cond
  getRev RevChoiceValue (ChoiceValue _ e) = Just e
  getRev (RevChoiceElement 0 r) (ChoiceSingleton c) = getRev r c
  getRev (RevChoiceElement n r) (ChoiceBool lst) = do
    (el,_) <- safeGenericIndex lst n
    getRev r el
  getRev (RevChoiceElement n r) (ChoiceValue lst _) = do
    (el,_) <- safeGenericIndex lst n
    getRev r el
  getRev _ _ = Nothing
  setRev (RevChoiceBool i) x (Just (ChoiceBool lst)) = do
    nlst <- safeGenericUpdateAt i (\(el,_) -> Just (el,x)) lst
    return $ ChoiceBool nlst
  setRev RevChoiceValue x (Just (ChoiceValue lst _)) = Just $ ChoiceValue lst x
  setRev (RevChoiceElement 0 r) x (Just (ChoiceSingleton y)) = do
    ny <- setRev r x (Just y)
    return $ ChoiceSingleton ny
  setRev (RevChoiceElement n r) x (Just (ChoiceBool lst)) = do
    nlst <- safeGenericUpdateAt n (\(el,cond) -> do
                                      nel <- setRev r x (Just el)
                                      return (nel,cond)) lst
    return $ ChoiceBool nlst
  setRev (RevChoiceElement n r) x (Just (ChoiceValue lst v)) = do
    nlst <- safeGenericUpdateAt n (\(el,val) -> do
                                      nel <- setRev r x (Just el)
                                      return (nel,val)) lst
    return $ ChoiceValue nlst v
  setRev _ _ _ = Nothing
  compCombine f (ChoiceSingleton x) (ChoiceSingleton y) = do
    z <- compCombine f x y
    case z of
      Nothing -> do
        ct <- true
        cf <- false
        condX <- f ct cf
        condY <- f cf ct
        case compCompare (compType x) (compType y) of
          EQ -> error "Not well-behaved instance of Composite passed to Choice data type"
          LT -> return $ Just $ ChoiceBool [(x,condX),(y,condY)]
          GT -> return $ Just $ ChoiceBool [(y,condY),(x,condX)]
      Just z' -> return $ Just $ ChoiceSingleton z'
  compCombine f (ChoiceSingleton x) (ChoiceBool ys) = do
    cf <- false
    ct <- true
    cond <- f ct cf
    nlst <- runExceptT $ insertByWith (\(x,_) (y,_) -> compCompare x y)
            (\(x,cx) (y,cy) -> do
                z <- lift $ compCombine f x y
                cz <- lift $ f cx cy
                case z of
                  Nothing -> throwError ()
                  Just z' -> return (z',cz)) (x,cond) ys
    case nlst of
      Left () -> return Nothing
      Right nlst' -> return $ Just $ ChoiceBool nlst'
  compCombine f (ChoiceBool xs) (ChoiceSingleton y) = do
    cf <- false
    ct <- true
    cond <- f cf ct
    nlst <- runExceptT $ insertByWith (\(x,_) (y,_) -> compCompare x y)
            (\(x,cx) (y,cy) -> do
                z <- lift $ compCombine f x y
                cz <- lift $ f cx cy
                case z of
                  Nothing -> throwError ()
                  Just z' -> return (z',cz)) (y,cond) xs
    case nlst of
      Left () -> return Nothing
      Right nlst' -> return $ Just $ ChoiceBool nlst'
  compCombine f (ChoiceBool xs) (ChoiceBool ys) = do
    zs <- runExceptT $ mergeByWith (\(x,_) (y,_) -> compCompare x y)
          (\(x,cx) (y,cy) -> do
              z <- lift $ compCombine f x y
              cz <- lift $ f cx cy
              case z of
                Nothing -> throwError ()
                Just z' -> return (z',cz)) xs ys
    case zs of
      Left () -> return Nothing
      Right zs' -> return $ Just (ChoiceBool zs')
  compCombine f (ChoiceValue xs ex) (ChoiceValue ys ey) = case geq (getType ex) (getType ey) of
    Just Refl -> do
      ez <- f ex ey
      zs <- runExceptT $ mergeByWith (\(_,vx) (_,vy) -> compare vx vy)
            (\(x,vx) (y,vy) -> do
                z <- lift $ compCombine f x y
                case z of
                  Nothing -> throwError ()
                  Just z' -> return (z',vx)) xs ys
      case zs of
        Left () -> return Nothing
        Right zs' -> return $ Just $ ChoiceValue zs' ez
    Nothing -> return Nothing
  compCompare = compareChoice
  compShow = showsPrec
  compInvariant (ChoiceSingleton c) = compInvariant c
  compInvariant (ChoiceBool xs) = do
    recInv <- fmap concat $ mapM (\(x,_) -> compInvariant x) xs
    inv <- oneOf [] $ fmap snd xs
    inv' <- case inv of
      [x] -> return x
      _ -> or' inv
    return $ inv':recInv
    where
      oneOf _ [] = return []
      oneOf xs (y:ys) = do
        xs' <- mapM not' xs
        ys' <- mapM not' ys
        cs <- oneOf (xs++[y]) ys
        c <- and' (xs'++y:ys')
        return $ c:cs

compareChoice :: (Composite c,GCompare e) => Choice enc c e -> Choice enc c e -> Ordering
compareChoice (ChoiceSingleton x) (ChoiceSingleton y) = compCompare x y
compareChoice (ChoiceSingleton _) _ = LT
compareChoice _ (ChoiceSingleton _) = GT
compareChoice (ChoiceBool xs) (ChoiceBool ys)
  = compareListWith (\(cx,ex) (cy,ey) -> case gcompare ex ey of
                        GEQ -> compCompare cx cy
                        GLT -> LT
                        GGT -> GT) xs ys
compareChoice (ChoiceBool _) _ = LT
compareChoice _ (ChoiceBool _) = GT
compareChoice (ChoiceValue xs ex) (ChoiceValue ys ey) = case gcompare ex ey of
  GEQ -> compareListWith (\(cx,vx) (cy,vy) -> case compare vx vy of
                             EQ -> compCompare cx cy
                             r -> r) xs ys
  GLT -> LT
  GGT -> GT

instance (Composite c,GCompare e) => Eq (Choice enc c e) where
  (==) x y = compareChoice x y==EQ
instance (Composite c,GCompare e) => Ord (Choice enc c e) where
  compare = compareChoice

instance (Composite c,GShow e) => Show (Choice enc c e) where
  showsPrec p (ChoiceSingleton x) = showParen (p>10) $ showString "ChoiceSingleton " . compShow 11 x
  showsPrec p (ChoiceBool xs)
    = showParen (p>10) $ showString "ChoiceBool " .
      showListWith (\(x,ex) -> showChar '(' . compShow 0 x .
                               showChar ',' . gshowsPrec 0 ex .
                               showChar ')') xs
  showsPrec p (ChoiceValue xs e)
    = showParen (p>10) $ showString "ChoiceValue " .
      showListWith (\(x,vx) -> showChar '(' . compShow 0 x .
                               showChar ',' . gshowsPrec 0 vx .
                               showChar ')') xs . showChar ' ' .
      gshowsPrec 11 e

instance CompositeExtract c => CompositeExtract (Choice enc c) where
  type CompExtract (Choice enc a) = CompExtract a
  compExtract f (ChoiceSingleton x) = compExtract f x
  compExtract f (ChoiceBool lst) = do
    nlst <- mapM (\(v,cond) -> do
                     BoolValue res <- f cond
                     return (v,res)
                 ) lst
    case [ v | (v,True) <- nlst ] of
      [] -> error "Choice: No value selected."
      [x] -> compExtract f x
      _ -> error "Choice: More than one value selected."
  compExtract f (ChoiceValue lst e) = do
    val <- f e
    case [ comp | (comp,v) <- lst, v == val ] of
      [] -> error "Choice: No value selected."
      [x] -> compExtract f x
      _ -> error "Choice: More than one value selected."

instance Composite c => Show (RevChoice enc c tp) where
  showsPrec p (RevChoiceBool i) = showParen (p>10) $
    showString "RevChoiceBool " .
    showsPrec 11 i
  showsPrec p RevChoiceValue = showString "RevChoiceValue"
  showsPrec p (RevChoiceElement i rev) = showParen (p>10) $
    showString "RevChoiceElement " .
    showsPrec 11 i . showChar ' ' .
    gshowsPrec 11 rev

instance Composite c => GShow (RevChoice enc c) where
  gshowsPrec = showsPrec

instance Composite c => GEq (RevChoice enc c) where
  geq (RevChoiceBool x) (RevChoiceBool y) = if x==y
                                            then Just Refl
                                            else Nothing
  geq RevChoiceValue RevChoiceValue = Just Refl
  geq (RevChoiceElement i1 r1) (RevChoiceElement i2 r2)
    = if i1==i2
      then do
    Refl <- geq r1 r2
    return Refl
      else Nothing
  geq _ _ = Nothing

instance Composite c => GCompare (RevChoice enc c) where
  gcompare (RevChoiceBool x) (RevChoiceBool y) = case compare x y of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (RevChoiceBool _) _ = GLT
  gcompare _ (RevChoiceBool _) = GGT
  gcompare RevChoiceValue RevChoiceValue = GEQ
  gcompare RevChoiceValue _ = GLT
  gcompare _ RevChoiceValue = GGT
  gcompare (RevChoiceElement i1 r1) (RevChoiceElement i2 r2) = case compare i1 i2 of
    LT -> GLT
    GT -> GGT
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT

-- | Sort and remove duplicates from a list.
normalizeList :: (a -> a -> Ordering) -> [a] -> [a]
normalizeList f = dups . sortBy f
  where
    dups [] = []
    dups [x] = [x]
    dups (x:y:ys) = if f x y == EQ
                    then dups (x:ys)
                    else x:dups (y:ys)

-- | Insert into a sorted list with a comparing and combining function.
insertByWith :: Monad m => (a -> a -> Ordering) -> (a -> a -> m a) -> a -> [a] -> m [a]
insertByWith comp comb x [] = return [x]
insertByWith comp comb x (y:ys) = case comp x y of
  LT -> return $ x:y:ys
  GT -> do
    ys' <- insertByWith comp comb x ys
    return $ y:ys'
  EQ -> do
    ny <- comb x y
    return $ ny:ys

mergeByWith :: Monad m => (a -> a -> Ordering) -> (a -> a -> m a) -> [a] -> [a] -> m [a]
mergeByWith comp comb [] ys = return ys
mergeByWith comp comb xs [] = return xs
mergeByWith comp comb (x:xs) (y:ys) = case comp x y of
  LT -> do
    zs <- mergeByWith comp comb xs (y:ys)
    return $ x:zs
  GT -> do
    zs <- mergeByWith comp comb (x:xs) ys
    return $ y:zs
  EQ -> do
    z <- comb x y
    zs <- mergeByWith comp comb xs ys
    return $ z:zs

lookupBy :: (a -> Ordering) -> [a] -> Maybe a
lookupBy _ [] = Nothing
lookupBy f (x:xs) = case f x of
  LT -> lookupBy f xs
  EQ -> Just x
  GT -> Nothing

compareListWith :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
compareListWith _ [] [] = EQ
compareListWith _ [] _ = LT
compareListWith _ _ [] = GT
compareListWith f (x:xs) (y:ys) = case f x y of
  EQ -> compareListWith f xs ys
  r -> r

-- | Get all the values represented by this encoding.
possibleChoices :: Choice enc c e -> [c e]
possibleChoices (ChoiceSingleton x) = [x]
possibleChoices (ChoiceBool vals) = fmap fst vals
possibleChoices (ChoiceValue mp _) = fmap fst mp

getChosen :: (Composite c,Embed m e,Monad m,GetType e,GCompare e)
          => Choice enc c e
          -> m (Maybe (c e))
getChosen (ChoiceSingleton x) = return (Just x)
getChosen (ChoiceBool xs) = compITEs (fmap (\(x,c) -> (c,x)) xs)
getChosen (ChoiceValue xs var) = do
  xs' <- mapM (\(c,val) -> do
                  cond <- var .==. constant val
                  return (cond,c)
              ) xs
  compITEs xs'

setChosen :: (Composite c,Embed m e,Monad m,GCompare e)
          => Choice enc c e
          -> c e
          -> m (Choice enc c e)
setChosen (ChoiceSingleton _) nel = return $ ChoiceSingleton nel
setChosen (ChoiceBool _) nel = return $ ChoiceSingleton nel
setChosen (ChoiceValue entrs _) nel = case lookupBy (\(el,_) -> compCompare nel el) entrs of
  Just (_,k) -> do
    val <- constant k
    return $ ChoiceValue entrs val

getChoiceValues :: Choice enc c e -> [c e]
getChoiceValues (ChoiceSingleton x) = [x]
getChoiceValues (ChoiceBool lst) = fmap fst lst
getChoiceValues (ChoiceValue lst _) = fmap fst lst

getChoices :: (Embed m e,Monad m) => Choice enc c e -> m [(c e,[e BoolType])]
getChoices (ChoiceSingleton x) = return [(x,[])]
getChoices (ChoiceBool lst) = return $ fmap (\(el,c) -> (el,[c])) lst
getChoices (ChoiceValue lst e)
  = mapM (\(c,val) -> do
             cond <- e .==. constant val
             return (c,[cond])
         ) lst

mapChoices :: (Embed m e,Monad m)
           => (e BoolType -> c e -> m (c e))
           -> Choice enc c e
           -> m (Choice enc c e)
mapChoices f (ChoiceSingleton x) = do
  cond <- true
  nx <- f cond x
  return $ ChoiceSingleton nx
mapChoices f (ChoiceBool lst) = do
  nlst <- mapM (\(el,cond) -> do
                   nel <- f cond el
                   return (nel,cond)) lst
  return $ ChoiceBool nlst
mapChoices f (ChoiceValue lst var) = do
  nlst <- mapM (\(el,val) -> do
                   cond <- var .==. constant val
                   nel <- f cond el
                   return (nel,val)
               ) lst
  return $ ChoiceValue nlst var

zipSame :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipSame f [] [] = Just []
zipSame f (x:xs) (y:ys) = do
  rest <- zipSame f xs ys
  return (f x y:rest)
zipSame _ _ _ = Nothing

initial :: (Composite c,Embed m e,Monad m)
        => (c Repr -> m (c e,Maybe (e BoolType)))
        -> Choice enc c Repr
        -> m (Choice enc c e)
initial f (ChoiceSingleton x) = do
  (r,_) <- f x
  return (ChoiceSingleton r)
initial f (ChoiceBool xs) = do
  lst <- mapM (\(x,_) -> do
                  (c,cond) <- f x
                  case cond of
                    Nothing -> do
                      ncond <- false
                      return (c,ncond)
                    Just ncond -> return (c,ncond)) xs
  return $ ChoiceBool lst
initial f (ChoiceValue xs tp) = do
  lst <- mapM (\(x,val) -> do
                  (c,cond) <- f x
                  return (c,cond,val)) xs
  e <- mkITE [ (cond,val) | (c,Just cond,val) <- lst ]
  return $ ChoiceValue (fmap (\(c,_,val) -> (c,val)) lst) e
  where
    mkITE [(_,val)] = constant val
    mkITE ((cond,val):rest) = do
      ifF <- mkITE rest
      ite cond (constant val) ifF

chosen :: (Embed m e,Monad m) => Accessor (Choice enc c) (NoComp Integer) c m e
chosen = Accessor get set
  where
    get :: (Embed m e,Monad m)
        => Choice enc c e
        -> m [(NoComp Integer e,[e BoolType],c e)]
    get (ChoiceSingleton x) = return [(NoComp 0,[],x)]
    get (ChoiceBool xs) = return $ fmap (\((el,c),n) -> (NoComp n,[c],el)
                                        ) $ zip xs [0..]
    get (ChoiceValue xs var) = mapM (\((el,val),n) -> do
                                        cond <- var .==. constant val
                                        return (NoComp n,[cond],el)
                                    ) $ zip xs [0..]

    set :: (Embed m e,Monad m)
        => [(NoComp Integer e,c e)]
        -> Choice enc c e
        -> m (Choice enc c e)
    set [] ch = return ch
    set [(_,nel)] (ChoiceSingleton _) = return $ ChoiceSingleton nel
    set upd (ChoiceBool xs) = return $ ChoiceBool $ merge upd 0 xs
    set upd (ChoiceValue xs var) = return $ ChoiceValue (merge upd 0 xs) var

    merge [] _ xs = xs
    merge upd@((NoComp i,nel):upd') p ((el,cond):xs)
      | p==i      = (nel,cond):merge upd' (p+1) xs
      | otherwise = (el,cond):merge upd (p+1) xs

                                          
