module Language.SMTLib2.Composite.Array.Sectioned where

import Language.SMTLib2
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Array as Array
import Language.SMTLib2.Composite.Ranged
import Language.SMTLib2.Composite.List

import Data.GADT.Show
import Data.GADT.Compare

data Section idx c e
  = DynamicSection { sectionArray  :: CompArray '[idx] c e
                   , sectionLength :: Ranged idx e }
  | StaticSection { sectionElement :: c e }

data RevSection idx c tp where
  RevDynamicSection :: RevArray '[idx] c tp -> RevSection idx c tp
  RevDynamicLength  :: RevSection idx c idx
  RevStaticSection  :: RevComp c tp -> RevSection idx c tp

instance Composite c => Composite (Section idx c) where
  type CompDescr (Section idx c) = (Maybe (Range idx),CompDescr c)
  type RevComp (Section idx c) = RevSection idx c
  compositeType (Nothing,c) = StaticSection (compositeType c)
  compositeType (Just idx,c) = DynamicSection (compositeType (rangeType idx ::: Nil,c)) (compositeType idx)
  foldExprs f (DynamicSection arr len) = do
    narr <- foldExprs (f . RevDynamicSection) arr
    nlen <- foldExprs (\Refl -> f RevDynamicLength) len
    return $ DynamicSection narr nlen
  foldExprs f (StaticSection el) = do
    nel <- foldExprs (f . RevStaticSection) el
    return $ StaticSection nel
  accessComposite (RevDynamicSection r) = accessComposite r . sectionArray
  accessComposite RevDynamicLength = accessComposite Refl . sectionLength
  accessComposite (RevStaticSection r) = accessComposite r . sectionElement

instance Composite c => Show (RevSection idx c tp) where
  showsPrec p (RevDynamicSection r)
    = showParen (p>10) $
      showString "RevDynamicSection " .
      gshowsPrec 11 r
  showsPrec p RevDynamicLength = showString "RevDynamicLength"
  showsPrec p (RevStaticSection r)
    = showParen (p>10) $
      showString "RevStaticSection " .
      gshowsPrec 11 r

instance Composite c => GShow (RevSection idx c) where
  gshowsPrec = showsPrec

instance Composite c => GEq (RevSection idx c) where
  geq (RevDynamicSection r1) (RevDynamicSection r2) = do
    Refl <- geq r1 r2
    return Refl
  geq RevDynamicLength RevDynamicLength = return Refl
  geq (RevStaticSection r1) (RevStaticSection r2) = do
    Refl <- geq r1 r2
    return Refl
  geq _ _ = Nothing

instance Composite c => GCompare (RevSection idx c) where
  gcompare (RevDynamicSection r1) (RevDynamicSection r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevDynamicSection _) _ = GLT
  gcompare _ (RevDynamicSection _) = GGT
  gcompare RevDynamicLength RevDynamicLength = GEQ
  gcompare RevDynamicLength _ = GLT
  gcompare _ RevDynamicLength = GGT
  gcompare (RevStaticSection r1) (RevStaticSection r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

type CompArraySectioned idx c = CompList (Section idx c)

--newtype SectionedIndex = SectionedIndex { section :: Ranged IntType }

selectDescr :: (Num (Value tp),Num (Range tp))
            => (c -> c -> c)
            -> [(Maybe (Range tp),c)]
            -> Range tp
            -> c
selectDescr union arr idx = foldl1 union $ select' (singletonRange 0) arr
  where
    select' _ [] = []
    select' off ((Nothing,descr):arr) = let rest = select' (off + (singletonRange 1)) arr
                                        in if isEmptyRange (intersectionRange off idx)
                                           then rest
                                           else descr:rest
    select' off ((Just len,descr):arr)
      = let noff = off+len
            rest = select' noff arr
        in if isEmptyRange (intersectionRange (betweenRange off noff) idx)
           then rest
           else descr:rest

select :: (Embed m e,GetType e,Composite c,Num (Value tp),Num (Range tp))
       => (e BoolType -> c e -> c e -> m (c e)) -- ^ If-then-else
       -> (e tp -> e tp -> m (e tp)) -- ^ Addition
       -> (e tp -> e tp -> m (e tp)) -- ^ Subtraction
       -> (e tp -> e tp -> e tp -> m (e BoolType)) -- ^ Is the first parameter greater or equal than the second, but smaller than the third parameter?
       -> CompDescr (CompArraySectioned tp c)
       -> Range tp
       -> CompArraySectioned tp c e
       -> Ranged tp e
       -> m (c e)
select ite add sub between descr rng (CompList lst) (Ranged idx) = do
  offv <- constant 0
  conds <- select' (singletonRange 0) offv descr lst
  ites ite conds
  where
    ites :: Monad m => (e BoolType -> c e -> c e -> m (c e)) -> [(e BoolType,c e)] -> m (c e)
    ites _ [(_,v)] = return v
    ites ite ((c,v):vs) = do
      nv <- ites ite vs
      ite c v nv
      
    select' _ _ [] [] = return []
    select' off offv ((Nothing,_):descr) ((StaticSection el):lst) = do
      let noff = off+(singletonRange 1)
      noffv <- constant 1 >>= add offv
      rest <- select' noff noffv descr lst
      if isEmptyRange (intersectionRange off rng)
        then return rest
        else do
        c <- idx .==. offv
        return ((c,el):rest)
    select' off offv ((Just len,_):descr) ((DynamicSection arr (Ranged lenv)):lst) = do
      let noff = off+len
      noffv <- add offv lenv
      rest <- select' noff noffv descr lst
      if isEmptyRange (intersectionRange (betweenRange off noff) rng)
        then return rest
        else do
        c <- between idx offv noffv
        ridx <- sub idx offv
        v <- Array.select arr (ridx ::: Nil)
        return ((c,v):rest)

storeDescr :: (Num (Value tp),Num (Range tp))
           => (c -> c -> c)
           -> [(Maybe (Range tp),c)]
           -> Range tp
           -> c
           -> [(Maybe (Range tp),c)]
storeDescr union arr idx el = store' (singletonRange 0) arr
  where
    store' off ((Nothing,descr):arr)
      = let narr = store' (off+singletonRange 1) arr
        in if isEmptyRange (intersectionRange off idx)
           then (Nothing,descr):narr
           else (Nothing,union descr el):narr
    store' off ((Just len,descr):arr)
      = let noff = off+len
            narr = store' noff arr
        in if isEmptyRange (intersectionRange (betweenRange off noff) idx)
           then (Just len,descr):narr
           else (Just len,union descr el):narr

store :: (Embed m e,GetType e,Composite c,Num (Value tp),Num (Range tp))
      => (e BoolType -> c e -> c e -> m (c e)) -- ^ If-then-else
      -> (e tp -> e tp -> m (e tp)) -- ^ Addition
      -> (e tp -> e tp -> m (e tp)) -- ^ Subtraction
      -> (e tp -> e tp -> e tp -> m (e BoolType)) -- ^ Is the first parameter greater or equal than the second, but smaller than the third parameter?
      -> CompDescr (CompArraySectioned tp c)
      -> Range tp
      -> CompArraySectioned tp c e
      -> Ranged tp e
      -> c e
      -> m (CompArraySectioned tp c e)
store ite add sub between descr rng (CompList lst) (Ranged idx) el = do
  offv <- constant 0
  nlst <- store' (singletonRange 0) offv descr lst
  return (CompList nlst)
  where
    store' _ _ [] [] = return []
    store' off offv ((Nothing,_):descr) ((StaticSection cel):lst) = do
      let noff = off+singletonRange 1
      noffv <- constant 1 >>= add offv
      rest <- store' noff noffv descr lst
      if isEmptyRange (intersectionRange off rng)
        then return $ (StaticSection cel):rest
        else do
        c <- idx .==. offv
        nel <- ite c el cel
        return $ (StaticSection nel):rest
    store' off offv ((Just len,_):descr) ((DynamicSection arr (Ranged lenv)):lst) = do
      let noff = off+len
      noffv <- add offv lenv
      rest <- store' noff noffv descr lst
      if isEmptyRange (intersectionRange (betweenRange off noff) rng)
        then return ((DynamicSection arr (Ranged lenv)):rest)
        else do
        c <- between idx offv noffv
        ridx <- sub idx offv
        narr <- Array.store arr (ridx ::: Nil) el
        return ((DynamicSection arr (Ranged lenv)):rest)

lastDescr :: [(Maybe (Range tp),c)] -> c
lastDescr [(_,descr)] = descr
lastDescr (d:ds) = lastDescr ds

last :: (Embed m e,GetType e,Composite c) => (e idx -> m (e idx)) -- ^ Successor
     -> CompArraySectioned idx c e
     -> m (c e)
last succ (CompList lst) = last' lst
  where
    last' [StaticSection el] = return el
    last' [DynamicSection arr (Ranged len)] = do
      idx <- succ len
      Array.select arr (idx ::: Nil)
    last' (_:xs) = last' xs

lengthDescr :: Num (Range tp) => [(Maybe (Range tp),c)] -> Range tp
lengthDescr = length' 0
  where
    length' cur [] = cur
    length' cur ((Just len,_):rest) = length' (cur+len) rest
    length' cur ((Nothing,_):rest) = length' (cur+1) rest

length :: (Embed m e,Num (Value tp)) => (e tp -> e tp -> m (e tp)) -- ^ Addition
       -> CompArraySectioned tp c e
       -> m (Ranged tp e)
length add (CompList lst) = do
  len <- length' 0 Nothing lst
  return (Ranged len)
  where
    length' len Nothing [] = constant len
    length' 0 (Just l) [] = return l
    length' len (Just l) [] = do
      clen <- constant len
      add clen l
    length' len dyn (StaticSection _:rest)
      = length' (len+1) dyn rest
    length' len dyn (DynamicSection _ (Ranged sz):rest) = case dyn of
      Nothing -> length' len (Just sz) rest
      Just sz' -> do
        nsz <- add sz' sz
        length' len (Just nsz) rest
