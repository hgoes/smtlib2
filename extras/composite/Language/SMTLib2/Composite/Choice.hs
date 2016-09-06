{-# LANGUAGE DataKinds,GADTs,TypeFamilies,ExistentialQuantification,ScopedTypeVariables,RankNTypes #-}
module Language.SMTLib2.Composite.Choice
  (Choice(),
   -- * Encodings
   boolEncoding,intEncoding,bvEncoding,dtEncoding,possibleChoices,
   -- * Functions
   chosen,choiceValues,choices,initial
  ) where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2.Composite.List
import Language.SMTLib2.Composite.Tuple
import Language.SMTLib2.Composite.Singleton
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
import Control.Lens hiding (Choice,chosen)
import Control.Monad.Except
import Text.Show
import Data.Maybe

data Choice c e = ChoiceSingleton { _choiceSingleton :: c e }
                | ChoiceBool { _choiceBool :: [(c e,e BoolType)] }
                | forall t. ChoiceValue { _choiceValue :: [(c e,Value t)]
                                        , _choiceExpr :: e t }

choiceSingleton :: MaybeLens (Choice c e) (c e)
choiceSingleton = lens (\x -> case x of
                           ChoiceSingleton y -> Just y
                           _ -> Nothing)
                  (\_ new -> Just $ ChoiceSingleton new)

choiceBool :: MaybeLens (Choice c e) [(c e,e BoolType)]
choiceBool = lens (\x -> case x of
                      ChoiceBool xs -> Just xs
                      _ -> Nothing)
             (\_ new -> Just $ ChoiceBool new)

{-choiceValue :: MaybeLens (Choice c e) (forall t. [(c e,Value t)])
choiceValue = lens (\x -> case x of
                       ChoiceValue xs _ -> Just xs
                       _ -> Nothing)
              (\x new -> case x of
                  ChoiceValue _ e -> case new of
                    [] -> Just $ ChoiceValue [] e
                    (_,v):_ -> do
                      Refl <- geq (getType e) (getType v)
                      return $ ChoiceValue new e)

choiceExpr :: MaybeLens (Choice c e) (forall t. e t)
choiceExpr = lens (\x -> case x of
                      ChoiceValue _ e -> Just e
                      _ -> Nothing)
             undefined-}

type ChoiceEncoding c = Choice c Repr

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

compareListWith :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
compareListWith _ [] [] = EQ
compareListWith _ [] _ = LT
compareListWith _ _ [] = GT
compareListWith f (x:xs) (y:ys) = case f x y of
  EQ -> compareListWith f xs ys
  r -> r

boolEncoding :: Composite c => [CompDescr c] -> ChoiceEncoding c
boolEncoding [x] = ChoiceSingleton x
boolEncoding xs = ChoiceBool (zip (normalizeList compCompare xs) (repeat bool))

intEncoding :: Composite c => [CompDescr c] -> ChoiceEncoding c
intEncoding xs = ChoiceValue (zip (normalizeList compCompare xs) [ IntValue n | n <- [0..] ]) int

bvEncoding :: Composite c => [CompDescr c] -> ChoiceEncoding c
bvEncoding xs = reifyNat bits $ \bw -> ChoiceValue
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

dtEncoding :: (Composite c,Backend b) => Proxy c -> String -> [(String,CompDescr c)] -> SMT b (ChoiceEncoding c)
dtEncoding (_::Proxy c) dtName els
  = reifyTypeList
  (\(con,el) f -> f (EncodingElement el (DynConstructor Nil con))) (normalizeList (\(_,x) (_,y) -> compCompare x y) els) $
  \(cons :: List (EncodingElement (CompDescr c)) sig)
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
    return $ ChoiceValue vals (DataRepr tp')

-- | Get all the values represented by this encoding.
possibleChoices :: ChoiceEncoding c -> [CompDescr c]
possibleChoices (ChoiceBool vals) = fmap fst vals
possibleChoices (ChoiceValue mp _) = fmap fst mp

data RevChoice c t where
  RevChoiceBool :: Integer -> RevChoice c BoolType
  RevChoiceValue :: Repr t -> RevChoice c t
  RevChoiceElement :: Integer -> RevComp c tp -> RevChoice c tp

instance Composite c => GShow (RevChoice c) where
  gshowsPrec p (RevChoiceBool i) = showParen (p>10) $
    showString "RevChoiceBool " .
    showsPrec 11 i
  gshowsPrec p (RevChoiceValue tp) = showParen (p>10) $
    showString "RevChoiceValue " .
    showsPrec 11 tp
  gshowsPrec p (RevChoiceElement i rev) = showParen (p>10) $
    showString "RevChoiceElement " .
    showsPrec 11 i . showChar ' ' .
    gshowsPrec 11 rev

instance Composite c => GEq (RevChoice c) where
  geq (RevChoiceBool x) (RevChoiceBool y) = if x==y
                                            then Just Refl
                                            else Nothing
  geq (RevChoiceValue t1) (RevChoiceValue t2) = do
    Refl <- geq t1 t2
    return Refl
  geq (RevChoiceElement i1 r1) (RevChoiceElement i2 r2)
    = if i1==i2
      then do
    Refl <- geq r1 r2
    return Refl
      else Nothing
  geq _ _ = Nothing

instance Composite c => GCompare (RevChoice c) where
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
  gcompare (RevChoiceValue _) _ = GLT
  gcompare _ (RevChoiceValue _) = GGT
  gcompare (RevChoiceElement i1 r1) (RevChoiceElement i2 r2) = case compare i1 i2 of
    LT -> GLT
    GT -> GGT
    EQ -> case gcompare r1 r2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT

instance (Composite c) => Composite (Choice c) where
  type RevComp (Choice a) = RevChoice a

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
    nv <- f (RevChoiceValue (getType v)) v
    nlst <- mapM (\(i,(el,val)) -> do
                     nel <- foldExprs (\rev -> f (RevChoiceElement i rev)) el
                     return (nel,val)
                 ) $ zip [0..] lst
    return (ChoiceValue nlst nv)
  accessComposite (RevChoiceBool i)
    = choiceBool `composeMaybe`
      listElement' i `composeMaybe`
      maybeLens _2
  accessComposite (RevChoiceValue tp)
    = lens (\ch -> case ch of
               ChoiceValue _ e -> do
                 Refl <- geq (getType e) tp
                 return e)
      (\ch ne -> case ch of
          ChoiceValue vals e -> do
            Refl <- geq (getType e) tp
            return $ ChoiceValue vals ne)
  accessComposite (RevChoiceElement i r)
    = lens (\x -> case x of
               ChoiceSingleton c -> if i==0
                                    then c `getMaybe` accessComposite r
                                    else Nothing
               ChoiceBool cs -> cs `getMaybe` lensLst r
               ChoiceValue cs _ -> cs `getMaybe` lensLst r)
      (\x new -> case x of
          ChoiceSingleton c -> if i==0
                               then do
            nc <- c & accessComposite r .~ new
            return $ ChoiceSingleton nc
                               else Nothing
          ChoiceBool cs -> fmap ChoiceBool $ cs & lensLst r .~ new
          ChoiceValue cs e -> do
            ncs <- cs & lensLst r .~ new
            return $ ChoiceValue ncs e)
    where
      lensLst :: (Composite c,GetType e) => RevComp c tp -> MaybeLens [(c e,a)] (e tp)
      lensLst r = listElement' i `composeMaybe`
                  maybeLens _1 `composeMaybe`
                  accessComposite r
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
  compCompare (ChoiceSingleton x) (ChoiceSingleton y) = compCompare x y
  compCompare (ChoiceSingleton _) _ = LT
  compCompare _ (ChoiceSingleton _) = GT
  compCompare (ChoiceBool xs) (ChoiceBool ys)
    = compareListWith (\(cx,ex) (cy,ey) -> case gcompare ex ey of
                          GEQ -> compCompare cx cy
                          GLT -> LT
                          GGT -> GT) xs ys
  compCompare (ChoiceBool _) _ = LT
  compCompare _ (ChoiceBool _) = GT
  compCompare (ChoiceValue xs ex) (ChoiceValue ys ey) = case gcompare ex ey of
    GEQ -> compareListWith (\(cx,vx) (cy,vy) -> case compare vx vy of
                               EQ -> compCompare cx cy
                               r -> r) xs ys
    GLT -> LT
    GGT -> GT
  compShow p (ChoiceSingleton x) = showParen (p>10) $ showString "ChoiceSingleton " . compShow 11 x
  compShow p (ChoiceBool xs)
    = showParen (p>10) $ showString "ChoiceBool " .
      showListWith (\(x,ex) -> showChar '(' . compShow 0 x .
                               showChar ',' . gshowsPrec 0 ex .
                               showChar ')') xs
  compShow p (ChoiceValue xs e)
    = showParen (p>10) $ showString "ChoiceValue " .
      showListWith (\(x,vx) -> showChar '(' . compShow 0 x .
                               showChar ',' . gshowsPrec 0 vx .
                               showChar ')') xs . showChar ' ' .
      gshowsPrec 11 e
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

instance CompositeExtract c => CompositeExtract (Choice c) where
  type CompExtract (Choice a) = CompExtract a
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

chosen :: Composite c
       => CompLens (Choice c) c
chosen
  = lensM (\ch -> case ch of
              ChoiceSingleton x -> return x
              ChoiceBool xs -> mkITE xs
              ChoiceValue xs var -> do
                xs' <- mapM (\(c,val) -> do
                                cond <- var .==. constant val
                                return (c,cond)) xs
                mkITE xs')
    (\_ nel -> return $ ChoiceSingleton nel)
  where
    mkITE :: (Composite c,Embed m e,Monad m,GetType e,GCompare e)
          => [(c e,e BoolType)]
          -> m (c e)
    mkITE [(v,_)] = return v
    mkITE ((vT,c):rest) = do
      vF <- mkITE rest
      v <- compITE c vT vF
      case v of
        Just v' -> return v'
        Nothing -> error "Unmergable composite type used in chosen lens"

choiceValues :: CompLens (Choice c) (CompList c)
choiceValues
  = liftLens $ lens
    (\ch -> case ch of
        ChoiceSingleton x -> CompList [x]
        ChoiceBool lst -> CompList $ fmap fst lst
        ChoiceValue lst _ -> CompList $ fmap fst lst)
    (\ch (CompList nlst) -> case ch of
        ChoiceSingleton _ -> case nlst of
          [nx] -> ChoiceSingleton nx
          _ -> err
        ChoiceBool lst -> case zipSame (\(_,cond) el -> (el,cond)) lst nlst of
          Just res -> ChoiceBool res
          Nothing -> err
        ChoiceValue lst e -> case zipSame (\(_,val) el -> (el,val)) lst nlst of
          Just res -> ChoiceValue res e
          Nothing -> err)
  where
    err = error "choicesValues cannot change the number of choice elements."

-- | A lens accessing all possible values and their conditions.
--   Warning: Updating this lens for a value encoding will blow up the condition
--   expressions.
choices :: CompLens (Choice c) (CompList (CompTuple2 c (Comp BoolType)))
choices
  = lensM (\ch -> case ch of
              ChoiceSingleton x -> do
                cond <- true
                return $ CompList [CompTuple2 x (Comp cond)]
              ChoiceBool lst -> return $ CompList $ fmap (\(el,cond) -> CompTuple2 el (Comp cond)) lst
              ChoiceValue lst e -> do
                res <- mapM (\(c,val) -> do
                                cond <- e .==. constant val
                                return $ CompTuple2 c (Comp cond)
                            ) lst
                return $ CompList res)
    (\ch (CompList nlst) -> case ch of
        ChoiceValue lst e -> case zipSame (\(_,val) (CompTuple2 el (Comp cond)) -> (el,cond,val)) lst nlst of
          Nothing -> error "Cannot update the structure of a value encoding choice."
          Just rlst -> do
            ne <- mkITE rlst
            return (ChoiceValue (fmap (\(el,_,val) -> (el,val)) rlst) ne)
        _ -> case nlst of
          [CompTuple2 el _] -> return $ ChoiceSingleton el
          _ -> return $ ChoiceBool $ fmap (\(CompTuple2 el (Comp cond)) -> (el,cond)) nlst)
  where
    mkITE [(_,_,val)] = constant val
    mkITE ((_,cond,val):rest) = do
      ifF <- mkITE rest
      ite cond (constant val) ifF
                                      
zipSame :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipSame f [] [] = Just []
zipSame f (x:xs) (y:ys) = do
  rest <- zipSame f xs ys
  return (f x y:rest)
zipSame _ _ _ = Nothing

initial :: (Composite c,Embed m e,Monad m) => (CompDescr c -> m (c e,Maybe (e BoolType))) -> ChoiceEncoding c -> m (Choice c e)
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
