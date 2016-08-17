module Language.SMTLib2.Composite.List.Dynamic where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.List
import Language.SMTLib2.Composite.Array as Array

import Data.GADT.Compare
import Data.GADT.Show
import Data.List

data CompDynList c e = StaticList { staticList :: CompList c e }
                     | forall idx. DynamicList { indexType    :: Repr idx
                                               , dynamicArray :: CompArray '[idx] c e
                                               , dynamicSize  :: e idx }

data CompDynListDescr c = StaticListDescr (CompDescr (CompList c))
                        | forall idx. DynamicListDescr (CompDescr (CompArray '[idx] c))

data RevDynList c tp where
  RevStaticList :: RevComp (CompList c) tp -> RevDynList c tp
  RevDynamicList :: Repr idx -> RevComp (CompArray '[idx] c) tp -> RevDynList c tp
  RevDynamicSize :: Repr idx -> RevDynList c idx

instance Composite c => Composite (CompDynList c) where
  type CompDescr (CompDynList c) = CompDynListDescr c
  type RevComp (CompDynList c) = RevDynList c
  compositeType (StaticListDescr d) = StaticList $ compositeType d
  compositeType (DynamicListDescr d@(i ::: Nil,_)) = DynamicList i (compositeType d) i
  foldExprs f (StaticList l) = do
    nl <- foldExprs (f . RevStaticList) l
    return (StaticList nl)
  foldExprs f (DynamicList tp arr sz) = do
    narr <- foldExprs (f . RevDynamicList tp) arr
    nsz <- f (RevDynamicSize tp) sz
    return (DynamicList tp narr nsz)
  accessComposite (RevStaticList r) (StaticList l) = accessComposite r l
  accessComposite (RevDynamicList tp1 r) (DynamicList tp2 arr _) = do
    Refl <- geq tp1 tp2
    accessComposite r arr
  accessComposite (RevDynamicSize tp1) (DynamicList tp2 _ sz) = do
    Refl <- geq tp1 tp2
    return sz
  accessComposite _ _ = Nothing

instance Composite c => Eq (CompDynListDescr c) where
  (==) (StaticListDescr d1) (StaticListDescr d2) = d1==d2
  (==) (DynamicListDescr (i1 ::: Nil,d1)) (DynamicListDescr (i2 ::: Nil,d2)) = case geq i1 i2 of
    Just Refl -> d1==d2
    Nothing -> False
  (==) _ _ = False

instance Composite c => Ord (CompDynListDescr c) where
  compare (StaticListDescr d1) (StaticListDescr d2) = compare d1 d2
  compare (StaticListDescr _) _ = LT
  compare _ (StaticListDescr _) = GT
  compare (DynamicListDescr (i1 ::: Nil,d1)) (DynamicListDescr (i2 ::: Nil,d2)) = case gcompare i1 i2 of
    GLT -> LT
    GGT -> GT
    GEQ -> compare d1 d2

deriving instance Composite c => Show (RevDynList c tp)
instance Composite c => GShow (RevDynList c) where
  gshowsPrec = showsPrec

instance Composite c => GEq (RevDynList c) where
  geq (RevStaticList r1) (RevStaticList r2) = do
    Refl <- geq r1 r2
    return Refl
  geq (RevDynamicList tp1 r1) (RevDynamicList tp2 r2) = do
    Refl <- geq tp1 tp2
    Refl <- geq r1 r2
    return Refl
  geq (RevDynamicSize tp1) (RevDynamicSize tp2) = do
    Refl <- geq tp1 tp2
    return Refl

instance Composite c => GCompare (RevDynList c) where
  gcompare (RevStaticList r1) (RevStaticList r2) = case gcompare r1 r2 of
    GLT -> GLT
    GGT -> GGT
    GEQ -> GEQ
  gcompare (RevStaticList _) _ = GLT
  gcompare _ (RevStaticList _) = GGT
  gcompare (RevDynamicList tp1 r1) (RevDynamicList tp2 r2) = case gcompare tp1 tp2 of
    GLT -> GLT
    GGT -> GGT
    GEQ -> case gcompare r1 r2 of
      GLT -> GLT
      GGT -> GGT
      GEQ -> GEQ
  gcompare (RevDynamicList _ _) _ = GLT
  gcompare _ (RevDynamicList _ _) = GGT
  gcompare (RevDynamicSize tp1) (RevDynamicSize tp2) = case gcompare tp1 tp2 of
    GLT -> GLT
    GGT -> GGT
    GEQ -> GEQ
  
data DynListIndex (e :: Type -> *)
  = StaticListIndex Integer
  | forall idx. DynamicListIndex (e idx)

instance Composite DynListIndex where
  type CompDescr DynListIndex = DynListIndex Repr
  type RevComp DynListIndex = Repr
  compositeType = id
  foldExprs _ (StaticListIndex i) = return $ StaticListIndex i
  foldExprs f (DynamicListIndex i) = do
    ni <- f (getType i) i
    return (DynamicListIndex ni)
  accessComposite tp (DynamicListIndex i) = do
    Refl <- geq tp (getType i)
    return i
  accessComposite _ _ = Nothing
  
instance GEq e => Eq (DynListIndex e) where
  (==) (StaticListIndex i1) (StaticListIndex i2) = i1==i2
  (==) (DynamicListIndex i1) (DynamicListIndex i2) = case geq i1 i2 of
    Just Refl -> True
    Nothing -> False
  (==) _ _ = False

instance GCompare e => Ord (DynListIndex e) where
  compare (StaticListIndex i1) (StaticListIndex i2) = compare i1 i2
  compare (StaticListIndex _) _ = LT
  compare _ (StaticListIndex _) = GT
  compare (DynamicListIndex i1) (DynamicListIndex i2) = case gcompare i1 i2 of
    GLT -> LT
    GGT -> GT
    GEQ -> EQ

unionDescr :: (CompDescr c -> CompDescr c -> CompDescr c)
           -> CompDynListDescr c
           -> CompDynListDescr c
           -> CompDynListDescr c
unionDescr f (StaticListDescr lst1) (StaticListDescr lst2)
  = StaticListDescr $ union lst1 lst2
  where
    union [] ys = ys
    union xs [] = xs
    union (x:xs) (y:ys) = f x y:union xs ys
unionDescr f (DynamicListDescr (idx,d1)) (DynamicListDescr (_,d2))
  = DynamicListDescr (idx,f d1 d2)
unionDescr f (StaticListDescr lst1) (DynamicListDescr (idx,d2))
  = DynamicListDescr (idx,foldl f d2 lst1)
unionDescr f (DynamicListDescr (idx,d1)) (StaticListDescr lst2)
  = DynamicListDescr (idx,foldl f d1 lst2)

selectDescr :: Composite c => CompDynListDescr c -> DynListIndex Repr -> CompDescr c
selectDescr (StaticListDescr lst) (StaticListIndex i) = lst `genericIndex` i
selectDescr (DynamicListDescr (_,c)) _ = c

select :: (Composite c,Embed m e,Monad m,GetType e) => CompDynList c e -> DynListIndex e -> m (c e)
select (StaticList (CompList lst)) (StaticListIndex i) = return $ lst `genericIndex` i
select (DynamicList tp arr _) (DynamicListIndex i) = case geq tp (getType i) of
  Just Refl -> Array.select arr (i ::: Nil)

storeDescr :: Composite c => (CompDescr c -> CompDescr c -> CompDescr c)
           -> CompDynListDescr c -> DynListIndex Repr -> CompDescr c -> CompDynListDescr c
storeDescr _ (StaticListDescr lst) (StaticListIndex i) el = StaticListDescr (insert i el lst)
  where
    insert 0 el (_:xs) = el:xs
    insert n el (x:xs) = x:insert (n-1) el xs
storeDescr f (DynamicListDescr (i,d)) _ el = DynamicListDescr (i,f d el)

store :: (Composite c,Embed m e,Monad m,GetType e) => CompDynList c e -> DynListIndex e -> c e -> m (CompDynList c e)
store (StaticList (CompList lst)) (StaticListIndex i) el = return $ StaticList $ CompList $ insert i el lst
  where
    insert 0 el (_:xs) = el:xs
    insert n el (x:xs) = x:insert (n-1) el xs
store (DynamicList tp arr sz) (DynamicListIndex i) el = case geq tp (getType i) of
  Just Refl -> do
    narr <- Array.store arr (i:::Nil) el
    return $ DynamicList tp narr sz

pushDescr :: Composite c => (CompDescr c -> CompDescr c -> CompDescr c)
          -> CompDynListDescr c -> CompDescr c
          -> (DynListIndex Repr,CompDynListDescr c)
pushDescr _ (StaticListDescr lst) el = (StaticListIndex $ genericLength lst,StaticListDescr $ lst++[el])
pushDescr f (DynamicListDescr (i:::Nil,d)) el = (DynamicListIndex i,DynamicListDescr (i:::Nil,f d el))

push :: (Composite c,Embed m e,Monad m,GetType e) => CompDynList c e -> c e -> m (DynListIndex e,CompDynList c e)
push (StaticList (CompList lst)) el
  = return (StaticListIndex $ genericLength lst,StaticList $ CompList $ lst++[el])
push (DynamicList tp arr sz) el = do
  narr <- Array.store arr (sz:::Nil) el
  nsz <- next tp sz
  return (DynamicListIndex sz,DynamicList tp narr nsz)
  where
    next :: Embed m e => Repr tp -> e tp -> m (e tp)
    next IntRepr x = x .+. cint 1
    next (BitVecRepr bw) x = bvadd x (cbv 1 bw)

popDescr :: Composite c => CompDynListDescr c -> CompDynListDescr c
popDescr (StaticListDescr lst) = StaticListDescr $ dropLast lst
  where
    dropLast [x] = []
    dropLast (x:xs) = x:dropLast xs
popDescr (DynamicListDescr d) = DynamicListDescr d

pop :: (Composite c,Embed m e,Monad m,GetType e) => CompDynList c e -> m (CompDynList c e)
pop (StaticList (CompList lst)) = return $ StaticList $ CompList $ dropLast lst
  where
    dropLast [x] = []
    dropLast (x:xs) = x:dropLast xs
pop (DynamicList tp arr sz) = do
  nsz <- prev tp sz
  return (DynamicList tp arr sz)
  where
    prev :: Embed m e => Repr tp -> e tp -> m (e tp)
    prev IntRepr x = x .-. cint 1
    prev (BitVecRepr bw) x = bvsub x (cbv 1 bw)
