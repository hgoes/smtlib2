module Language.SMTLib2.Internals.Embed where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Backend

import Data.Functor.Identity
import Control.Monad.State
import Data.GADT.Compare

type EmbedExpr m e tp = Expression (EmVar m e) (EmQVar m e) (EmFun m e) (EmFunArg m e) (EmLVar m e) e tp

class (Applicative m,
       GCompare (EmVar m e),
       GCompare (EmQVar m e),
       GCompare (EmFun m e),
       GCompare (EmFunArg m e),
       GCompare (EmLVar m e)
      ) => Embed m e where
  type EmVar m e :: Type -> *
  type EmQVar m e :: Type -> *
  type EmFun m e :: ([Type],Type) -> *
  type EmFunArg m e :: Type -> *
  type EmLVar m e :: Type -> *
  embed :: m (EmbedExpr m e tp)
        -> m (e tp)
  embedQuantifier :: Quantifier
                  -> List Repr arg
                  -> (forall m e. Embed m e => List (EmQVar m e) arg -> m (e BoolType))
                  -> m (e BoolType)
  embedTypeOf :: m (e tp -> Repr tp)

class (GCompare (ExVar i e),
       GCompare (ExQVar i e),
       GCompare (ExFun i e),
       GCompare (ExFunArg i e),
       GCompare (ExLVar i e)) => Extract i e where
  type ExVar i e :: Type -> *
  type ExQVar i e :: Type -> *
  type ExFun i e :: ([Type],Type) -> *
  type ExFunArg i e :: Type -> *
  type ExLVar i e :: Type -> *
  extract :: i -> e tp
          -> Maybe (Expression (ExVar i e) (ExQVar i e) (ExFun i e) (ExFunArg i e) (ExLVar i e) e tp)

instance (Backend b,e ~ Expr b) => Embed (SMT b) e where
  type EmVar (SMT b) e = Var b
  type EmQVar (SMT b) e = QVar b
  type EmFun (SMT b) e = Fun b
  type EmFunArg (SMT b) e = FunArg b
  type EmLVar (SMT b) e = LVar b
  embed x = do
    rx <- x
    embedSMT (toBackend rx)
  embedQuantifier quant tps f = do
    args <- List.mapM (\tp -> embedSMT (createQVar tp Nothing)) tps
    body <- f args
    embedSMT $ toBackend (Quantification quant args body)
  embedTypeOf = pure getType

newtype BackendInfo b = BackendInfo b

instance (Backend b,e ~ Expr b) => Extract (BackendInfo b) e where
  type ExVar (BackendInfo b) e = Var b
  type ExQVar (BackendInfo b) e = QVar b
  type ExFun (BackendInfo b) e = Fun b
  type ExFunArg (BackendInfo b) e = FunArg b
  type ExLVar (BackendInfo b) e = LVar b
  extract (BackendInfo b) e = Just (fromBackend b e)

data SMTExpr var qvar fun farg lvar tp where
  SMTExpr :: Expression var qvar fun farg lvar
             (SMTExpr var qvar fun farg lvar)
             tp -> SMTExpr var qvar fun farg lvar tp
  SMTQuant :: Quantifier
           -> List Repr args
           -> (List qvar args
               -> SMTExpr var qvar fun farg lvar BoolType)
           -> SMTExpr var qvar fun farg lvar BoolType

instance (GCompare var,GetType var,
          GCompare qvar,GetType qvar,
          GCompare fun,GetFunType fun,
          GCompare farg,GetType farg,
          GCompare lvar,GetType lvar
         ) => Embed Identity (SMTExpr var qvar fun farg lvar) where
  type EmVar Identity (SMTExpr var qvar fun farg lvar) = var
  type EmQVar Identity (SMTExpr var qvar fun farg lvar) = qvar
  type EmFun Identity (SMTExpr var qvar fun farg lvar) = fun
  type EmFunArg Identity (SMTExpr var qvar fun farg lvar) = farg
  type EmLVar Identity (SMTExpr var qvar fun farg lvar) = lvar
  embed e = do
    re <- e
    return $ SMTExpr re
  embedQuantifier quant tps f = return $ SMTQuant quant tps (runIdentity . f)
  embedTypeOf = pure getType

instance (GetType var,GetType qvar,GetFunType fun,GetType farg,GetType lvar)
         => GetType (SMTExpr var qvar fun farg lvar) where
  getType (SMTExpr e) = getType e
  getType (SMTQuant _ _ _) = BoolRepr

instance (GCompare var,
          GCompare qvar,
          GCompare fun,
          GCompare farg,
          GCompare lvar) => Extract () (SMTExpr var qvar fun farg lvar) where
  type ExVar () (SMTExpr var qvar fun farg lvar) = var
  type ExQVar () (SMTExpr var qvar fun farg lvar) = qvar
  type ExFun () (SMTExpr var qvar fun farg lvar) = fun
  type ExFunArg () (SMTExpr var qvar fun farg lvar) = farg
  type ExLVar () (SMTExpr var qvar fun farg lvar) = lvar
  extract _ (SMTExpr e) = Just e
  extract _ _ = Nothing

encodeExpr :: (Backend b)
           => SMTExpr (Var b) (QVar b) (Fun b) (FunArg b) (LVar b) tp
           -> SMT b (Expr b tp)
encodeExpr (SMTExpr e) = do
  e' <- mapExpr return return return return return
        encodeExpr e
  embedSMT $ toBackend e'
encodeExpr (SMTQuant q tps f) = do
  args <- List.mapM (\tp -> embedSMT (createQVar tp Nothing)) tps
  body <- encodeExpr (f args)
  embedSMT $ toBackend (Quantification q args body)

decodeExpr :: (Backend b) => Expr b tp
           -> SMT b (SMTExpr (Var b) (QVar b) (Fun b) (FunArg b) (LVar b) tp)
decodeExpr e = do
  st <- get
  let e' = fromBackend (backend st) e
  e'' <- mapExpr return return return return return decodeExpr e'
  return (SMTExpr e'')

data AnalyzedExpr i e tp
  = AnalyzedExpr (Maybe (Expression
                         (ExVar i e)
                         (ExQVar i e)
                         (ExFun i e)
                         (ExFunArg i e)
                         (ExLVar i e)
                         (AnalyzedExpr i e)
                         tp)) (e tp)

analyze' :: (Extract i e) => i -> e tp -> AnalyzedExpr i e tp
analyze' i expr
  = AnalyzedExpr expr' expr
  where
    expr' = do
      e <- extract i expr
      return $ runIdentity (mapExpr return return return return return
                            (return . analyze' i) e)

analyze :: (Backend b) => Expr b tp -> SMT b (AnalyzedExpr (BackendInfo b) (Expr b) tp)
analyze e = do
  st <- get
  return (analyze' (BackendInfo (backend st)) e)
