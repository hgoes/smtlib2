{-# LANGUAGE DataKinds,GADTs,TypeFamilies,ExistentialQuantification,ScopedTypeVariables,RankNTypes #-}
module Language.SMTLib2.Composite.Choice where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2
import Language.SMTLib2.Internals.Type
import qualified Language.SMTLib2.Internals.Type.List as List

import Data.GADT.Show
import Data.GADT.Compare
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Identity
import Data.Typeable

data Choice a e = ChoiceBool (Map a (e BoolType))
                | forall t. ChoiceValue (Map a (Value t)) (e t)

data ChoiceEncoding a = BooleanEncoding (Map a ())
                      | forall t. ValueEncoding (Repr t) (Map a (Value t))

boolEncoding :: Ord a => [a] -> ChoiceEncoding a
boolEncoding xs = BooleanEncoding (Map.fromList [ (x,()) | x <- xs ])

intEncoding :: Ord a => [a] -> ChoiceEncoding a
intEncoding xs = ValueEncoding int (Map.fromList $ zip xs [ IntValue n | n <- [0..] ])

bvEncoding :: Ord a => [a] -> ChoiceEncoding a
bvEncoding xs = reifyNat bits $ \bw -> ValueEncoding (bitvec bw) (Map.fromList $ zip xs [ BitVecValue n bw | n <- [0..] ])
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

dtEncoding :: (Ord a,Backend b) => String -> [(String,a)] -> SMT b (ChoiceEncoding a)
dtEncoding dtName els
  = reifyTypeList
  (\(con,el) f -> f (EncodingElement el (DynConstructor Nil con))) els $
  \(cons :: List (EncodingElement a) sig)
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
    return $ ValueEncoding (DataRepr tp') (Map.fromList vals)

instance Eq a => Eq (ChoiceEncoding a) where
  (==) (BooleanEncoding mp1) (BooleanEncoding mp2) = mp1==mp2
  (==) (ValueEncoding r1 mp1) (ValueEncoding r2 mp2) = case geq r1 r2 of
    Just Refl -> mp1==mp2
    Nothing -> False
  (==) _ _ = False

instance Ord a => Ord (ChoiceEncoding a) where
  compare (BooleanEncoding mp1) (BooleanEncoding mp2) = compare mp1 mp2
  compare (BooleanEncoding _) _ = LT
  compare _ (BooleanEncoding _) = GT
  compare (ValueEncoding r1 mp1) (ValueEncoding r2 mp2) = case gcompare r1 r2 of
    GEQ -> compare mp1 mp2
    GLT -> LT
    GGT -> GT

instance Show a => Show (ChoiceEncoding a) where
  showsPrec p (BooleanEncoding mp) = showParen (p>10) $
    showString "BooleanEncoding " .
    showsPrec 11 (Map.keys mp)
  showsPrec p (ValueEncoding tp mp) = showParen (p>10) $
    showString "ValueEncoding " .
    showsPrec 11 tp . showChar ' ' .
    showsPrec 11 (Map.toList mp)

data RevChoice a t where
  RevChoiceBool :: a -> RevChoice a BoolType
  RevChoiceValue :: Repr t -> RevChoice a t

instance Show a => GShow (RevChoice a) where
  gshowsPrec p (RevChoiceBool x) = showsPrec p x
  gshowsPrec p (RevChoiceValue _) = showString "RevChoice"

instance Eq a => GEq (RevChoice a) where
  geq (RevChoiceBool x) (RevChoiceBool y) = if x==y
                                            then Just Refl
                                            else Nothing
  geq (RevChoiceValue t1) (RevChoiceValue t2) = do
    Refl <- geq t1 t2
    return Refl

instance Ord a => GCompare (RevChoice a) where
  gcompare (RevChoiceBool x) (RevChoiceBool y) = case compare x y of
    EQ -> GEQ
    LT -> GLT
    GT -> GGT
  gcompare (RevChoiceBool _) _ = GLT
  gcompare _ (RevChoiceBool _) = GGT
  gcompare (RevChoiceValue x) (RevChoiceValue y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance (Show a,Ord a) => Composite (Choice a) where
  type CompDescr (Choice a) = ChoiceEncoding a
  type RevComp (Choice a) = RevChoice a
  compositeType (BooleanEncoding mp) = ChoiceBool (fmap (const bool) mp)
  compositeType (ValueEncoding tp mp) = ChoiceValue mp tp
  foldExprs f (ChoiceBool mp) = fmap ChoiceBool $ sequence $ Map.mapWithKey (\k -> f (RevChoiceBool k)) mp
  foldExprs f (ChoiceValue mp v) = do
    nv <- f (RevChoiceValue (getType v)) v
    return (ChoiceValue mp nv)
  accessComposite (RevChoiceBool e) (ChoiceBool mp) = Map.lookup e mp
  accessComposite (RevChoiceValue tp) (ChoiceValue _ e) = case geq tp (getType e) of
    Just Refl -> Just e
    Nothing -> Nothing
  createComposite f (BooleanEncoding mp) = fmap ChoiceBool $ sequence $ Map.mapWithKey (\k _ -> f bool (RevChoiceBool k)) mp
  createComposite f (ValueEncoding tp mp) = do
    v <- f tp (RevChoiceValue tp)
    return (ChoiceValue mp v)
  revType _ _ (RevChoiceBool _) = bool
  revType _ _ (RevChoiceValue e) = getType e

instance (Show a,Ord a) => CompositeExtract (Choice a) where
  type CompExtract (Choice a) = a
  compExtract f ch = do
    ch' <- foldExprs (const f) ch
    return $ selectedValue ch'

selectedValue :: Choice a Value -> a
selectedValue (ChoiceBool mp) = case [ k | (k,BoolValue True) <- Map.toList mp ] of
  [] -> error "Choice: No value selected."
  [x] -> x
  _ -> error "Choice: More than one value selected."
selectedValue (ChoiceValue mp v) = case [ k | (k,v') <- Map.toList mp, v==v' ] of
  [] -> error "Choice: No value selected."
  [x] -> x
  _ -> error "Choice: More than one value selected."

select :: (Ord a,Embed m e,GetType e) => a -> Choice a e -> m (Choice a e)
select x (ChoiceBool mp) = do
  t <- true
  nmp <- sequence $ fmap (const false) mp
  return $ ChoiceBool $ Map.insert x t nmp
select x (ChoiceValue mp v) = case Map.lookup x mp of
  Just repr -> do
    c <- constant repr
    return (ChoiceValue mp c)
  Nothing -> error "select: No representative for value."

change :: (Ord a,Embed m e,GetType e) => (a -> a) -> Choice a e -> m (Choice a e)
change f (ChoiceBool mp) = do
  nmp <- mapM or'' conds
  return $ ChoiceBool nmp
  where
    conds = Map.foldrWithKey' (\k c -> Map.insertWith (++) (f k) [c]) Map.empty mp
    or'' [] = false
    or'' [x] = return x
    or'' xs = or' xs
change f (ChoiceValue mp v) = do
  nv <- mkITE (Map.toList conds)
  return (ChoiceValue mp nv)
  where
    conds = Map.foldrWithKey (\k repr -> Map.insertWith (++) (f k) [v .==. constant repr]) Map.empty mp
    mkITE [(k,_)] = case Map.lookup k mp of
      Just repr -> constant repr
    mkITE ((k,cs):xs) = case Map.lookup k mp of
      Just repr -> ite (case cs of
                          [c] -> c
                          _ -> or' cs)
                   (constant repr)
                   (mkITE xs)

initial :: (Ord a,Embed m e) => ChoiceEncoding a -> a -> m (Choice a e)
initial (BooleanEncoding _) x = do
  t <- true
  return $ ChoiceBool (Map.singleton x t)
initial (ValueEncoding tp mp) x = case Map.lookup x mp of
  Just repr -> do
    v <- constant repr
    return (ChoiceValue mp v)
  Nothing -> error "initial: No representative for value."

choiceITE :: (Ord a,Embed m e,GetType e) => e BoolType -> Choice a e -> Choice a e -> m (Choice a e)
choiceITE cond (ChoiceBool x) (ChoiceBool y) = do
  z <- sequence $ Map.mergeWithKey (\_ x y -> Just (ite cond x y)) (fmap (cond .&.)) (fmap ((not' cond) .&.)) x y
  return (ChoiceBool z)
choiceITE cond (ChoiceValue mp x) (ChoiceValue _ y) = case geq (getType x) (getType y) of
  Just Refl -> do
    z <- ite cond x y
    return (ChoiceValue mp z)

choiceInvariant :: (Embed m e,GetType e) => Choice a e -> m (e BoolType)
choiceInvariant (ChoiceBool mp) = do
  conj <- mapM (\xs -> case xs of
                  [] -> true
                  [x] -> x
                  _ -> and' xs
              ) $ oneOf (Map.elems mp)
  case conj of
    [] -> true
    [x] -> return x
    _ -> or' conj
  where
    oneOf (x:xs) = ((return x):fmap not' xs):(fmap (not' x:) (oneOf xs))
    oneOf [] = [[]]
choiceInvariant (ChoiceValue mp v) = case typeSize (getType v) of
  Nothing -> restr
  Just sz -> if fromInteger sz == Map.size mp
             then true
             else restr
  where
    restr = do
      xs <- mapM (\repr -> v .==. constant repr) (Map.elems mp)
      case xs of
        [] -> true
        [x] -> return x
        _ -> or' xs
