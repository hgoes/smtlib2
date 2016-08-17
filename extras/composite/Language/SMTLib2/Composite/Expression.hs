module Language.SMTLib2.Composite.Expression where

import Language.SMTLib2.Composite.Class

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Monad (backend)
import Language.SMTLib2.Internals.Backend (Var)
import qualified Language.SMTLib2.Internals.Expression as E
import qualified Language.SMTLib2.Internals.Type.List as List
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Data.GADT.Compare as GComp
import Data.GADT.Show
import Data.Dependent.Map (DMap,DSum(..))
import qualified Data.Dependent.Map as DMap
import Data.Functor.Identity
import Data.Proxy

data CompositeExpr a t
  = CompositeExpr { compositeDescr :: CompDescr a
                  , compositeExpr :: E.Expression (RevComp a) E.NoVar E.NoFun E.NoVar E.NoVar (CompositeExpr a) t }

instance Composite a => GetType (CompositeExpr a) where
  getType (CompositeExpr descr e :: CompositeExpr a t)
    = runIdentity $ E.expressionType
      (return . revType (Proxy::Proxy a) descr)
      (return.getType) (return.getFunType) (return.getType)
      (return.getType) (return.getType) e

createRevComp :: (Composite arg,Embed m e,Monad m,GetType e)
              => (forall t. Repr t -> RevComp arg t -> m (EmVar m e t))
              -> CompDescr arg
              -> m (arg e,DMap (EmVar m e) (RevComp arg))
createRevComp f descr
  = runStateT (createComposite (\tp rev -> do
                                   v <- lift (f tp rev)
                                   e <- lift (embed $ pure $ E.Var v)
                                   modify (DMap.insert v rev)
                                   return e
                               ) descr
              ) DMap.empty

instance Composite a => GEq (CompositeExpr a) where
  geq (CompositeExpr dx x) (CompositeExpr dy y)
    = if dx==dy
      then geq x y
      else Nothing
instance Composite a => GCompare (CompositeExpr a) where
  gcompare (CompositeExpr dx x) (CompositeExpr dy y)
    = case compare dx dy of
    EQ -> gcompare x y
    LT -> GLT
    GT -> GGT
instance Composite a => Eq (CompositeExpr a t) where
  (==) = GComp.defaultEq
instance Composite a => Ord (CompositeExpr a t) where
  compare = defaultCompare

instance Composite a => Show (CompositeExpr a t) where
  showsPrec p (CompositeExpr _ e) = E.renderExprDefault E.SMTRendering e

instance Composite a => GShow (CompositeExpr a) where
  gshowsPrec = showsPrec

instance (Composite a,d ~ CompDescr a) => Embed (Reader d) (CompositeExpr a) where
  type EmVar (Reader d) (CompositeExpr a) = RevComp a
  type EmQVar (Reader d) (CompositeExpr a) = E.NoVar
  type EmFun (Reader d) (CompositeExpr a) = E.NoFun
  type EmFunArg (Reader d) (CompositeExpr a) = E.NoVar
  type EmLVar (Reader d) (CompositeExpr a) = E.NoVar
  embed e = do
    re <- e
    descr <- ask
    return (CompositeExpr descr re)
  embedQuantifier _ _ _ = error "CompositeExpr does not support quantifier"
  embedTypeOf = return getType

instance Composite a => Extract () (CompositeExpr a) where
  type ExVar () (CompositeExpr a) = RevComp a
  type ExQVar () (CompositeExpr a) = E.NoVar
  type ExFun () (CompositeExpr a) = E.NoFun
  type ExFunArg () (CompositeExpr a) = E.NoVar
  type ExLVar () (CompositeExpr a) = E.NoVar
  extract _ (CompositeExpr _ x) = Just x

mkCompExpr :: Composite arg
           => (arg (CompositeExpr arg) -> Reader (CompDescr arg) (CompositeExpr arg tp))
           -> CompDescr arg
           -> CompositeExpr arg tp
mkCompExpr f descr
  = runReader (do
                  arg <- createComposite (\_ rev -> return (CompositeExpr descr (E.Var rev))) descr
                  f arg) descr

concretizeExpr :: (Embed m e,Monad m,Composite arg,GetType e)
               => arg e
               -> CompositeExpr arg tp
               -> m (e tp)
concretizeExpr arg (CompositeExpr _ (E.Var rev)) = case accessComposite rev arg of
  Just r -> return r
  Nothing -> error $ "concretizeExpr: Unknown key "++gshow rev
concretizeExpr arg (CompositeExpr _ (E.App fun args)) = do
  nfun <- E.mapFunction undefined fun
  nargs <- List.mapM (concretizeExpr arg) args
  embed $ pure $ E.App nfun nargs
concretizeExpr arg (CompositeExpr _ (E.Const c)) = embed $ pure $ E.Const c
concretizeExpr arg (CompositeExpr _ (E.AsArray fun)) = do
  nfun <- E.mapFunction undefined fun
  embed $ pure $ E.AsArray nfun

relativizeExpr :: (Backend b,Composite arg)
               => CompDescr arg
               -> DMap (Var b) (RevComp arg)
               -> Expr b tp
               -> SMT b (CompositeExpr arg tp)
relativizeExpr descr mp expr = do
  st <- get
  return $ relativizeExpr' descr mp DMap.empty (BackendInfo (backend st)) expr

relativizeExpr' :: (Extract i e,Composite arg,GShow (ExVar i e))
                => CompDescr arg
                -> DMap (ExVar i e) (RevComp arg)
                -> DMap (ExLVar i e) (CompositeExpr arg)
                -> i
                -> e tp
                -> CompositeExpr arg tp
relativizeExpr' descr mp lmp info e = case extract info e of
  Just (E.Var v) -> case DMap.lookup v mp of
    Just rev -> CompositeExpr descr (E.Var rev)
    Nothing -> error $ "Failed to relativize: "++gshowsPrec 0 v ""
  Just (E.LVar v) -> case DMap.lookup v lmp of
    Just e -> e
  Just (E.App fun args)
    -> let nfun = runIdentity $ E.mapFunction undefined fun
           nargs = runIdentity $ List.mapM (return . relativizeExpr' descr mp lmp info) args
       in CompositeExpr descr (E.App nfun nargs)
  Just (E.Const c) -> CompositeExpr descr (E.Const c)
  Just (E.AsArray fun)
    -> let nfun = runIdentity $ E.mapFunction undefined fun
       in CompositeExpr descr (E.AsArray nfun)
  -- TODO: Find a way not to flatten let bindings
  Just (E.Let bind body) -> relativizeExpr' descr mp nlmp info body
    where
      nlmp = runIdentity $ List.foldM (\lmp bind -> return $ DMap.insert (E.letVar bind)
                                                    (relativizeExpr' descr mp lmp info (E.letExpr bind)) lmp
                                      ) lmp bind

collectRevVars :: Composite arg
               => DMap (RevComp arg) E.NoVar
               -> CompositeExpr arg tp
               -> DMap (RevComp arg) E.NoVar
collectRevVars mp (CompositeExpr _ (E.Var v))
  = DMap.insert v E.NoVar' mp
collectRevVars mp (CompositeExpr _ (E.App fun args))
  = runIdentity $ List.foldM (\mp e -> return $ collectRevVars mp e) mp args
collectRevVars mp (CompositeExpr _ (E.Const _)) = mp
collectRevVars mp (CompositeExpr _ (E.AsArray _)) = mp
