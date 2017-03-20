{-# LANGUAGE DataKinds,GADTs,TypeFamilies,ExistentialQuantification,ScopedTypeVariables,RankNTypes #-}
module Language.SMTLib2.Composite.Choice
  (Choice(),ChoiceEncoding(..),RevChoice(),
   -- * Encodings
   boolEncoding,intEncoding,bvEncoding,{-dtEncoding,-}possibleChoices,
   -- * Constructor
   singleton,initial,initialBoolean,
   -- * Accessors
   chosen,
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
import qualified GHC.TypeLits as TL
import Data.Vector (Vector)
import qualified Data.Vector as Vec

data ChoiceEncoding = BoolEncoding
                    | ValueEncoding Type

data Choice enc c e where
  ChoiceSingleton :: c e -> Choice BoolEncoding c e
  ChoiceBool :: Vector (c e,e BoolType) -> Choice BoolEncoding c e
  ChoiceValue :: Repr tp -> Vector (c e,Value tp) -> e tp -> Choice (ValueEncoding tp) c e

singleton :: (Composite c,Embed m e,Monad m) => Choice enc c Repr -> c e -> m (Choice enc c e)
singleton (ChoiceSingleton _) x = return $ ChoiceSingleton x
singleton (ChoiceBool _) x = return $ ChoiceSingleton x
singleton (ChoiceValue tp mp _) x = do
  tpX <- compTypeM x
  case lookupBy (\(el,_) -> compCompare tpX el) mp of
    Just (_,key) -> do
      val <- constant key
      return $ ChoiceValue tp (Vec.singleton (x,key)) val

boolEncoding :: Composite c => [c Repr] -> Choice BoolEncoding c Repr
boolEncoding [c] = ChoiceSingleton c
boolEncoding cs  = ChoiceBool $ Vec.fromList $
                   zip (normalizeList compCompare cs) (repeat bool)

intEncoding :: Composite c => [c Repr] -> Choice (ValueEncoding IntType) c Repr
intEncoding xs = ChoiceValue int (Vec.fromList $
                                  zip (normalizeList compCompare xs)
                                  [ IntValue n | n <- [0..] ]) int

bvEncoding :: Composite c => [c Repr]
           -> (forall bw. Choice (ValueEncoding (BitVecType bw)) c Repr -> a)
           -> a
bvEncoding xs f = case TL.someNatVal bits of
  Just (TL.SomeNat w) -> let bw' = bw w
                         in f $ ChoiceValue (BitVecRepr bw')
                            (Vec.fromList $
                             zip (normalizeList compCompare xs)
                             [ BitVecValue n bw' | n <- [0..] ])
                            (bitvec bw')
  where
    bits = ceiling $ logBase 2 (fromIntegral size :: Double)
    size = length xs

{-data EncodingElement a (sig :: [Type]) where
  EncodingElement :: a -> DynamicConstructor '[] '[] -> EncodingElement a '[]

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
    g $ ChoiceValue vals (DataRepr tp')-}

data RevChoice enc c t where
  RevChoiceBool :: !Int -> RevChoice BoolEncoding c BoolType
  RevChoiceValue :: RevChoice (ValueEncoding t) c t
  RevChoiceElement :: !Int -> !(RevComp c tp) -> RevChoice enc c tp

instance (Composite c) => Composite (Choice enc c) where
  type RevComp (Choice enc a) = RevChoice enc a
  foldExprs f (ChoiceSingleton x) = do
    nx <- foldExprs (\rev -> f (RevChoiceElement 0 rev)
                    ) x
    return (ChoiceSingleton nx)
  foldExprs f (ChoiceBool lst) = do
    nlst <- Vec.imapM (\i (el,cond) -> do
                          nel <- foldExprs (\rev -> f (RevChoiceElement i rev)
                                           ) el
                          ncond <- f (RevChoiceBool i) cond
                          return (nel,ncond)
                      ) lst
    return $ ChoiceBool nlst
  foldExprs f (ChoiceValue tp lst v) = do
    nv <- f RevChoiceValue v
    nlst <- Vec.imapM (\i (el,val) -> do
                          nel <- foldExprs (\rev -> f (RevChoiceElement i rev)) el
                          return (nel,val)
                      ) lst
    return (ChoiceValue tp nlst nv)
  getRev (RevChoiceBool i) (ChoiceBool lst) = do
    (_,cond) <- lst Vec.!? i
    return cond
  getRev RevChoiceValue (ChoiceValue _ _ e) = Just e
  getRev (RevChoiceElement 0 r) (ChoiceSingleton c) = getRev r c
  getRev (RevChoiceElement n r) (ChoiceBool lst) = do
    (el,_) <- lst Vec.!? n
    getRev r el
  getRev (RevChoiceElement n r) (ChoiceValue _ lst _) = do
    (el,_) <- lst Vec.!? n
    getRev r el
  getRev _ _ = Nothing
  setRev (RevChoiceBool i) x (Just (ChoiceBool lst)) = do
    (el,_) <- lst Vec.!? i
    let nlst = lst Vec.// [(i,(el,x))]
    return $ ChoiceBool nlst
  setRev RevChoiceValue x (Just (ChoiceValue tp lst _)) = Just $ ChoiceValue tp lst x
  setRev (RevChoiceElement 0 r) x (Just (ChoiceSingleton y)) = do
    ny <- setRev r x (Just y)
    return $ ChoiceSingleton ny
  setRev (RevChoiceElement n r) x (Just (ChoiceBool lst)) = do
    (el,c) <- lst Vec.!? n
    nel <- setRev r x (Just el)
    let nlst = lst Vec.// [(n,(nel,c))]
    return $ ChoiceBool nlst
  setRev (RevChoiceElement n r) x (Just (ChoiceValue tp lst v)) = do
    (el,c) <- lst Vec.!? n
    nel <- setRev r x (Just el)
    let nlst = lst Vec.// [(n,(nel,c))]
    return $ ChoiceValue tp nlst v
  setRev _ _ _ = Nothing
  withRev (RevChoiceBool i) (ChoiceBool lst) f = do
    let (el,c) = lst Vec.! i
    nc <- f c
    let nlst = lst Vec.// [(i,(el,nc))]
    return (ChoiceBool nlst)
  withRev RevChoiceValue (ChoiceValue tp lst v) f = do
    nv <- f v
    return (ChoiceValue tp lst nv)
  withRev (RevChoiceElement 0 r) (ChoiceSingleton x) f = do
    nx <- withRev r x f
    return $ ChoiceSingleton nx
  withRev (RevChoiceElement n r) (ChoiceBool lst) f = do
    let (el,c) = lst Vec.! n
    nel <- withRev r el f
    let nlst = lst Vec.// [(n,(nel,c))]
    return $ ChoiceBool nlst
  withRev (RevChoiceElement n r) (ChoiceValue tp lst v) f = do
    let (el,c) = lst Vec.! n
    nel <- withRev r el f
    let nlst = lst Vec.// [(n,(nel,c))]
    return $ ChoiceValue tp nlst v
  withRev _ x _ = return x
  compCombine f (ChoiceSingleton x) (ChoiceSingleton y) = do
    z <- compCombine f x y
    case z of
      Nothing -> do
        ct <- true
        cf <- false
        condX <- f ct cf
        condY <- f cf ct
        case compCompare x y of
          EQ -> error "Not well-behaved instance of Composite passed to Choice data type"
          LT -> return $ Just $ ChoiceBool $ Vec.fromList [(x,condX),(y,condY)]
          GT -> return $ Just $ ChoiceBool $ Vec.fromList [(y,condY),(x,condX)]
      Just z' -> return $ Just $ ChoiceSingleton z'
  compCombine f (ChoiceSingleton x) (ChoiceBool ys) = do
    cf <- false
    ct <- true
    nlst <- runExceptT $ mergeChoiceList (\x (y,_) -> compCompare x y)
            (\x (y,cy) -> do
                z <- lift $ compCombine f x y
                case z of
                  Nothing -> throwError ()
                  Just z' -> do
                    cz <- lift $ f ct cy
                    return (z',cz))
            (\x -> do
                cx <- lift $ f ct cf
                return (x,cx))
            (\(y,cy) -> do
                cy' <- lift $ f cf cy
                return (y,cy'))
            [x] (Vec.toList ys)
    case nlst of
      Left () -> return Nothing
      Right nlst' -> return $ Just $ ChoiceBool $ Vec.fromList nlst'
  compCombine f (ChoiceBool xs) (ChoiceSingleton y) = do
    cf <- false
    ct <- true
    nlst <- runExceptT $ mergeChoiceList (\(x,_) y -> compCompare x y)
            (\(x,cx) y -> do
                z <- lift $ compCombine f x y
                case z of
                  Nothing -> throwError ()
                  Just z' -> do
                    cz <- lift $ f cx ct
                    return (z',cz))
            (\(x,cx) -> do
                cx' <- lift $ f cf cx
                return (x,cx'))
            (\y -> do
                cy <- lift $ f cf ct
                return (y,cy))
            (Vec.toList xs) [y]
    case nlst of
      Left () -> return Nothing
      Right nlst' -> return $ Just $ ChoiceBool $ Vec.fromList nlst'
  compCombine f (ChoiceBool xs) (ChoiceBool ys) = do
    cf <- false
    zs <- runExceptT $ mergeChoiceList (\(x,_) (y,_) -> compCompare x y)
          (\(x,cx) (y,cy) -> do
              z <- lift $ compCombine f x y
              case z of
                Nothing -> throwError ()
                Just z' -> do
                  cz <- lift $ f cx cy
                  return (z',cz))
          (\(x,cx) -> do
              cx' <- lift $ f cx cf
              return (x,cx'))
          (\(y,cy) -> do
              cy' <- lift $ f cf cy
              return (y,cy'))
          (Vec.toList xs) (Vec.toList ys)
    case zs of
      Left () -> return Nothing
      Right zs' -> return $ Just (ChoiceBool $ Vec.fromList zs')
  compCombine f (ChoiceValue tx xs ex) (ChoiceValue ty ys ey) = case geq tx ty of
    Just Refl -> do
      ez <- f ex ey
      zs <- runExceptT $ mergeByWith (\(_,vx) (_,vy) -> compare vx vy)
            (\(x,vx) (y,vy) -> do
                z <- lift $ compCombine f x y
                case z of
                  Nothing -> throwError ()
                  Just z' -> return (z',vx))
            (Vec.toList xs) (Vec.toList ys)
      case zs of
        Left () -> return Nothing
        Right zs' -> return $ Just $ ChoiceValue tx (Vec.fromList zs') ez
    Nothing -> return Nothing
  compCompare = compareChoice
  compShow = showsPrec
  compInvariant (ChoiceSingleton c) = compInvariant c
  compInvariant (ChoiceBool xs) = do
    recInv <- fmap concat $ mapM (\(x,_) -> compInvariant x) (Vec.toList xs)
    inv <- oneOf [] $ fmap snd (Vec.toList xs)
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

instance (Composite c) => Container (Choice enc c) where
  data Index (Choice enc c) el e where
    ChoiceIndex :: !Int -> Index (Choice enc c) c e
  elementGet (ChoiceSingleton x) (ChoiceIndex 0) = return x
  elementGet (ChoiceBool lst) (ChoiceIndex i) = case lst Vec.!? i of
    Just (el,_) -> return el
  elementGet (ChoiceValue _ lst _) (ChoiceIndex i)
    = case lst Vec.!? i of
        Just (el,_) -> return el

  elementSet (ChoiceSingleton _) (ChoiceIndex 0) x
    = return $ ChoiceSingleton x
  elementSet (ChoiceBool lst) (ChoiceIndex i) x
    = let (_,val) = lst Vec.! i
          nlst = lst Vec.// [(i,(x,val))]
      in return $ ChoiceBool nlst
  elementSet (ChoiceValue tp lst var) (ChoiceIndex i) x
    = let (_,val) = lst Vec.! i
          nlst = lst Vec.// [(i,(x,val))]
      in return $ ChoiceValue tp nlst var

  showIndex p (ChoiceIndex i) = showsPrec p i

compareChoice :: (Composite c,GCompare e) => Choice enc c e -> Choice enc c e -> Ordering
compareChoice (ChoiceSingleton x) (ChoiceSingleton y) = compCompare x y
compareChoice (ChoiceSingleton _) _ = LT
compareChoice _ (ChoiceSingleton _) = GT
compareChoice (ChoiceBool xs) (ChoiceBool ys)
  = compareListWith (\(cx,ex) (cy,ey) -> case gcompare ex ey of
                        GEQ -> compCompare cx cy
                        GLT -> LT
                        GGT -> GT) (Vec.toList xs) (Vec.toList ys)
compareChoice (ChoiceBool _) _ = LT
compareChoice _ (ChoiceBool _) = GT
compareChoice (ChoiceValue tx xs ex) (ChoiceValue ty ys ey) = case gcompare ex ey of
  GEQ -> compareListWith (\(cx,vx) (cy,vy) -> case compare vx vy of
                             EQ -> compCompare cx cy
                             r -> r)
         (Vec.toList xs) (Vec.toList ys)
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
                               showChar ')')
      (Vec.toList xs)
  showsPrec p (ChoiceValue _ xs e)
    = showParen (p>10) $ showString "ChoiceValue " .
      showListWith (\(x,vx) -> showChar '(' . compShow 0 x .
                               showChar ',' . gshowsPrec 0 vx .
                               showChar ')')
      (Vec.toList xs) . showChar ' ' .
      gshowsPrec 11 e

instance CompositeExtract c => CompositeExtract (Choice enc c) where
  type CompExtract (Choice enc a) = CompExtract a
  compExtract f (ChoiceSingleton x) = compExtract f x
  compExtract f (ChoiceBool lst) = do
    nlst <- mapM (\(v,cond) -> do
                     BoolValue res <- f cond
                     return (v,res)
                 ) lst
    case [ v | (v,True) <- Vec.toList nlst ] of
      [] -> error "Choice: No value selected."
      [x] -> compExtract f x
      _ -> error "Choice: More than one value selected."
  compExtract f (ChoiceValue tp lst e) = do
    val <- f e
    case [ comp | (comp,v) <- Vec.toList lst, v == val ] of
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

mergeChoiceList :: Monad m => (a -> b -> Ordering)
                -> (a -> b -> m c)
                -> (a -> m c)
                -> (b -> m c)
                -> [a] -> [b] -> m [c]
mergeChoiceList comp comb f g [] ys = mapM g ys
mergeChoiceList comp comb f g xs [] = mapM f xs
mergeChoiceList comp comb f g (x:xs) (y:ys) = case comp x y of
  LT -> do
    nx <- f x
    zs <- mergeChoiceList comp comb f g xs (y:ys)
    return $ nx:zs
  GT -> do
    ny <- g y
    zs <- mergeChoiceList comp comb f g (x:xs) ys
    return $ ny:zs
  EQ -> do
    z <- comb x y
    zs <- mergeChoiceList comp comb f g xs ys
    return $ z:zs

lookupBy :: (a -> Ordering) -> Vector a -> Maybe a
lookupBy f xs = let tl = Vec.dropWhile (\x -> f x==LT) xs
                in if Vec.null tl
                   then Nothing
                   else let hd = Vec.head tl
                        in if f hd==EQ
                           then Just hd
                           else Nothing

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
possibleChoices (ChoiceBool vals) = fmap fst (Vec.toList vals)
possibleChoices (ChoiceValue _ mp _) = fmap fst (Vec.toList mp)

getChosen :: (Composite c,Embed m e,Monad m,GetType e,GCompare e)
          => Choice enc c e
          -> m (Maybe (c e))
getChosen (ChoiceSingleton x) = return (Just x)
getChosen (ChoiceBool xs) = compITEs $ fmap (\(x,c) -> (c,x)) $ Vec.toList xs
getChosen (ChoiceValue _ xs var) = do
  xs' <- mapM (\(c,val) -> do
                  cond <- var .==. constant val
                  return (cond,c)
              ) $ Vec.toList xs
  compITEs xs'

setChosen :: (Composite c,Embed m e,Monad m,GCompare e)
          => Choice enc c e
          -> c e
          -> m (Choice enc c e)
setChosen (ChoiceSingleton _) nel = return $ ChoiceSingleton nel
setChosen (ChoiceBool _) nel = return $ ChoiceSingleton nel
setChosen (ChoiceValue tp entrs _) nel = case lookupBy (\(el,_) -> compCompare nel el) entrs of
  Just (_,k) -> do
    val <- constant k
    return $ ChoiceValue tp entrs val

getChoiceValues :: Choice enc c e -> [c e]
getChoiceValues (ChoiceSingleton x) = [x]
getChoiceValues (ChoiceBool lst) = fmap fst $ Vec.toList lst
getChoiceValues (ChoiceValue _ lst _) = fmap fst $ Vec.toList lst

getChoices :: (Embed m e,Monad m) => Choice enc c e -> m [(c e,[e BoolType])]
getChoices (ChoiceSingleton x) = return [(x,[])]
getChoices (ChoiceBool lst) = return $ fmap (\(el,c) -> (el,[c])) $ Vec.toList lst
getChoices (ChoiceValue _ lst e)
  = mapM (\(c,val) -> do
             cond <- e .==. constant val
             return (c,[cond])
         ) $ Vec.toList lst

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
mapChoices f (ChoiceValue tp lst var) = do
  nlst <- mapM (\(el,val) -> do
                   cond <- var .==. constant val
                   nel <- f cond el
                   return (nel,val)
               ) lst
  return $ ChoiceValue tp nlst var

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
initial f (ChoiceValue _ xs tp) = do
  lst <- mapM (\(x,val) -> do
                  (c,cond) <- f x
                  return (c,cond,val)) xs
  e <- mkITE [ (cond,val) | (c,Just cond,val) <- Vec.toList lst ]
  return $ ChoiceValue tp (fmap (\(c,_,val) -> (c,val)) lst) e
  where
    mkITE [(_,val)] = constant val
    mkITE ((cond,val):rest) = do
      ifF <- mkITE rest
      ite cond (constant val) ifF

initialBoolean :: [(c e,e BoolType)] -> Choice BoolEncoding c e
initialBoolean [(c,_)] = ChoiceSingleton c
initialBoolean cs = ChoiceBool $ Vec.fromList cs

chosen :: (Embed m e,Monad m,Composite c) => Access (Choice enc c) ('Seq c 'Id) c m e
chosen (ChoiceSingleton x) = return $ AccSeq [(ChoiceIndex 0,[],AccId)]
chosen (ChoiceBool xs)
  = return $ AccSeq $
    fmap (\(i,(_,cond)) -> (ChoiceIndex i,[cond],AccId))
    (zip [0..] $ Vec.toList xs)
chosen (ChoiceValue _ xs var)
  = fmap AccSeq $
    mapM (\(i,(_,val)) -> do
             cond <- var .==. constant val
             return (ChoiceIndex i,[cond],AccId)
         ) (zip [0..] $ Vec.toList xs)
