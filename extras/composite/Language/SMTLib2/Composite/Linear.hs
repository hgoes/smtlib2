module Language.SMTLib2.Composite.Linear where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2.Composite.List
--import Language.SMTLib2.Composite.Choice (insertByWith,mergeByWith)

import Data.GADT.Compare
import Data.GADT.Show
import Control.Lens
import Data.Monoid
import Text.Show
import Data.Foldable

data Linear c (e :: Type -> *) = Linear { _linConst :: Value (SingletonType c)
                                        , _linear :: [(Value (SingletonType c),c e)] }

makeLenses ''Linear

data RevLinear c tp where
  RevFactor :: Integer -> RevComp c tp -> RevLinear c tp

instance (IsNumeric c) => Composite (Linear c) where
  type RevComp (Linear c) = RevLinear c
  foldExprs f (Linear c facs) = do
    nfacs <- mapM (\(n,(c,v)) -> do
                      nv <- foldExprs (f . RevFactor n) v
                      return (c,nv)) $ zip [0..] facs
    return $ Linear c nfacs
  accessComposite (RevFactor i r)
    = maybeLens linear `composeMaybe`
      listElement' i `composeMaybe`
      maybeLens _2 `composeMaybe`
      accessComposite r
  compCombine f (Linear c1 lin1) (Linear c2 lin2)
    = case compare c1 c2 of
    EQ -> do
      nl <- mergeFactors f lin1 lin2
      case nl of
        Just nlin -> return $ Just $ Linear c1 nlin
        Nothing -> return Nothing
    LT -> do
      v <- compositeFromValue (fromInteger 1)
      nl2 <- mergeFactors f [(c2-c1,v)] lin2
      case nl2 of
        Just nlin2 -> do
          nl <- mergeFactors f lin1 nlin2
          case nl of
            Just nlin -> return $ Just $ Linear c1 nlin
            Nothing -> return Nothing
        Nothing -> return Nothing
    GT -> do
      v <- compositeFromValue (fromInteger 1)
      nl1 <- mergeFactors f [(c1-c2,v)] lin1
      case nl1 of
        Just nlin1 -> do
          nl <- mergeFactors f nlin1 lin2
          case nl of
            Just nlin -> return $ Just $ Linear c2 nlin
            Nothing -> return Nothing
        Nothing -> return Nothing
  compCompare (Linear c1 lin1) (Linear c2 lin2)
    = compare c1 c2 `mappend`
      comp lin1 lin2
    where
      comp [] [] = EQ
      comp [] _ = LT
      comp _ [] = GT
      comp ((cx,x):xs) ((cy,y):ys)
        = compare cx cy `mappend`
          compCompare x y `mappend`
          comp xs ys
  compShow p (Linear c lins) = showParen (p>10) $
    showString "Linear " .
    showsPrec 11 c . showChar ' ' .
    showListWith (\(c,v) -> showsPrec 10 c . showChar '*' . compShow 10 v) lins

instance (IsRanged c,IsNumeric c) => IsRanged (Linear c) where
  getRange (Linear c lin) = do
    let rc = rangedConst c
    rlin <- mapM (\(c,x) -> do
                     rx <- getRange x
                     return $ (rangedConst c) `rangeMult` rx) lin
    return $ foldl rangeAdd rc rlin

instance IsNumeric c => IsSingleton (Linear c) where
  type SingletonType (Linear c) = SingletonType c
  getSingleton (Linear c lin) = do
    ec <- compositeFromValue c
    elin <- mapM (\(c,x) -> do
                     rc <- compositeFromValue c
                     compositeMult rc x) lin
    res <- compositeSum $ ec:elin
    getSingleton res

instance (IsNumeric c,IsConstant c) => IsConstant (Linear c) where
  getConstant (Linear c lin) = do
    nlins <- mapM (\(c,x) -> do
                      rx <- getConstant x
                      return $ c*rx) lin
    return $ sum $ c:nlins

mergeFactors :: (Composite c,Embed m e,Monad m,GetType e,GCompare e)
             => (forall tp. e tp -> e tp -> m (e tp))
             -> [(Value tp,c e)]
             -> [(Value tp,c e)]
             -> m (Maybe [(Value tp,c e)])
mergeFactors _ [] ys = return $ Just ys
mergeFactors _ xs [] = return $ Just xs
mergeFactors f ((c1,x):xs) ((c2,y):ys) = case compare c1 c2 of
  EQ -> do
    z <- compCombine f x y
    case z of
      Just z' -> do
        zs <- mergeFactors f xs ys
        case zs of
          Just zs' -> return $ Just $ (c1,z'):zs'
          Nothing -> return Nothing
      Nothing -> return Nothing
  LT -> do
    rest <- mergeFactors f xs ((c2,y):ys)
    case rest of
      Just rest' -> return $ Just $ (c1,x):rest'
      Nothing -> return Nothing
  GT -> do
    rest <- mergeFactors f ((c1,x):xs) ys
    case rest of
      Just rest' -> return $ Just $ (c2,y):rest'
      Nothing -> return Nothing

instance Composite c => GEq (RevLinear c) where
  geq (RevFactor i1 r1) (RevFactor i2 r2)
    = if i1==i2
      then geq r1 r2
      else Nothing

instance Composite c => GCompare (RevLinear c) where
  gcompare (RevFactor i1 r1) (RevFactor i2 r2) = case compare i1 i2 of
    LT -> GLT
    GT -> GGT
    EQ -> gcompare r1 r2

instance Composite c => Show (RevLinear c tp) where
  showsPrec p (RevFactor i r) = showParen (p>10) $
    showString "RevFactor " .
    showsPrec 11 i . showChar ' ' .
    gshowsPrec 11 r

instance Composite c => GShow (RevLinear c) where
  gshowsPrec = showsPrec
