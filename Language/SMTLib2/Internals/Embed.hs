module Language.SMTLib2.Internals.Embed where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Backend
import Language.SMTLib2.Internals.Evaluate

import Data.Functor.Identity
import Control.Monad.State
import Control.Monad.Except
import Data.GADT.Compare
import Data.GADT.Show
import qualified Data.Dependent.Map as DMap

type EmbedExpr m e tp = Expression (EmVar m e) (EmQVar m e) (EmFun m e) (EmFunArg m e) (EmLVar m e) e tp

-- | A class of 'Monad's that can be used to form SMTLib expressions.
--   The default instance of this class is the 'SMT' monad, together with its
--   associated 'Expr' type. An interesting instance is the 'Identity' monad
--   with the 'Value' type, which allows evaluation of SMTLib expressions.
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
                  -> (forall m e. (Embed m e,Monad m) => List (EmQVar m e) arg -> m (e BoolType))
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

instance (Backend b) => Embed (SMT b) (Expr b) where
  type EmVar (SMT b) (Expr b) = Var b
  type EmQVar (SMT b) (Expr b) = QVar b
  type EmFun (SMT b) (Expr b) = Fun b
  type EmFunArg (SMT b) (Expr b) = FunArg b
  type EmLVar (SMT b) (Expr b) = LVar b
  embed x = do
    rx <- x
    embedSMT (toBackend rx)
  embedQuantifier quant tps f = do
    args <- List.mapM (\tp -> embedSMT (createQVar tp Nothing)) tps
    body <- f args
    embedSMT $ toBackend (Quantification quant args body)
  embedTypeOf = pure getType

instance Embed Identity Repr where
  type EmVar Identity Repr = Repr
  type EmQVar Identity Repr = Repr
  type EmFun Identity Repr = FunRepr
  type EmFunArg Identity Repr = Repr
  type EmLVar Identity Repr = Repr
  embed e = pure f <*> e
    where
      f e = runIdentity $ expressionType return return (\(FunRepr arg tp) -> return (arg,tp)) return return return e
  embedQuantifier _ _ _ = pure bool
  embedTypeOf = pure id

-- | A user-supplied function.
--   Can be used in embedding 'Value's or 'EvalResult's.
--   Since we don't have function equality in haskell, an integer is provided to distinguish functions.
data UserFun (m :: * -> *) (e :: Type -> *) (sig :: ([Type],Type))  where
  UserFun :: List Repr arg             -- Argument types
          -> Repr res                  -- Result type
          -> Int                       -- Number to distinguish functions
          -> (List e arg -> m (e res)) -- The function implementation
          -> UserFun m e '(arg,res)

instance GEq (UserFun m e) where
  geq (UserFun arg1 res1 n1 _) (UserFun arg2 res2 n2 _) = do
    Refl <- geq arg1 arg2
    Refl <- geq res1 res2
    if n1==n2
      then return Refl
      else Nothing

instance GCompare (UserFun m e) where
  gcompare (UserFun arg1 res1 n1 _) (UserFun arg2 res2 n2 _) = case gcompare arg1 arg2 of
    GLT -> GLT
    GGT -> GGT
    GEQ -> case gcompare res1 res2 of
      GLT -> GLT
      GGT -> GGT
      GEQ -> case compare n1 n2 of
        LT -> GLT
        GT -> GGT
        EQ -> GEQ

instance GetFunType (UserFun m e) where
  getFunType (UserFun arg res _ _) = (arg,res)

instance GShow (UserFun m e) where
  gshowsPrec p (UserFun idx res n _)
    = showParen (p>10) $ showsPrec 11 n . showString " : " .
      showsPrec 11 idx . showString " -> " .
      showsPrec 11 res

instance Embed Identity Value where
  type EmVar Identity Value = NoVar
  type EmQVar Identity Value = NoVar
  type EmFun Identity Value = UserFun Identity Value
  type EmFunArg Identity Value = NoVar
  type EmLVar Identity Value = NoVar
  embed e = do
    re <- e
    res <- evaluateExpr
           (error "embed: No variables in embedded values")
           (error "embed: No quantified variables in embedded values")
           (error "embed: No function variables in embedded values")
           (\(UserFun _ _ _ f) lst -> do
               lst' <- List.mapM (\res -> case res of
                                     ValueResult v -> return v) lst
               fmap ValueResult $ f lst')
           (error "embed: No fields in embedded values")
           (error "embed: No quantifier in embedded values")
           DMap.empty
           (\_ val -> return $ ValueResult val) re
    case res of
      ValueResult v -> return v
  embedTypeOf = pure getType

newtype ValueExt m tp = ValueExt { valueExt :: EvalResult (UserFun m (ValueExt m)) tp }

instance GetType (ValueExt m) where
  getType (ValueExt e) = getType e

instance GShow (ValueExt m) where
  gshowsPrec p (ValueExt e) = gshowsPrec p e

instance GEq (ValueExt m) where
  geq (ValueExt e1) (ValueExt e2) = geq e1 e2

instance GCompare (ValueExt m) where
  gcompare (ValueExt e1) (ValueExt e2) = gcompare e1 e2

instance Embed Identity (ValueExt Identity) where
  type EmVar Identity (ValueExt Identity) = NoVar
  type EmQVar Identity (ValueExt Identity) = NoVar
  type EmFun Identity (ValueExt Identity) = UserFun Identity (ValueExt Identity)
  type EmFunArg Identity (ValueExt Identity) = NoVar
  type EmLVar Identity (ValueExt Identity) = NoVar
  embed e = do
    re <- e
    fmap ValueExt $ evaluateExpr
           (error "embed: No variables in embedded values")
           (error "embed: No quantified variables in embedded values")
           (error "embed: No function variables in embedded values")
           (\(UserFun _ _ _ f) lst -> do
               lst' <- List.mapM (return.ValueExt) lst
               fmap valueExt $ f lst')
           (error "embed: No fields in embedded values")
           (error "embed: No quantifier in embedded values")
           DMap.empty
           (\_ val -> return $ valueExt val) re
  embedTypeOf = pure getType

newtype BackendInfo b = BackendInfo b

instance (Backend b) => Extract (BackendInfo b) (Expr b) where
  type ExVar (BackendInfo b) (Expr b) = Var b
  type ExQVar (BackendInfo b) (Expr b) = QVar b
  type ExFun (BackendInfo b) (Expr b) = Fun b
  type ExFunArg (BackendInfo b) (Expr b) = FunArg b
  type ExLVar (BackendInfo b) (Expr b) = LVar b
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

instance (Embed m e,Monad m) => Embed (ExceptT err m) e where
  type EmVar (ExceptT err m) e = EmVar m e
  type EmQVar (ExceptT err m) e = EmQVar m e
  type EmFun (ExceptT err m) e = EmFun m e
  type EmFunArg (ExceptT err m) e = EmFunArg m e
  type EmLVar (ExceptT err m) e = EmLVar m e
  embed e = do
    re <- e
    lift $ embed (pure re)
  embedQuantifier q arg body = lift $ embedQuantifier q arg body
  embedTypeOf = lift embedTypeOf

instance (Embed m e,Monad m) => Embed (StateT s m) e where
  type EmVar (StateT s m) e = EmVar m e
  type EmQVar (StateT s m) e = EmQVar m e
  type EmFun (StateT s m) e = EmFun m e
  type EmFunArg (StateT s m) e = EmFunArg m e
  type EmLVar (StateT s m) e = EmLVar m e
  embed e = do
    re <- e
    lift $ embed (pure re)
  embedQuantifier q arg body = lift $ embedQuantifier q arg body
  embedTypeOf = lift embedTypeOf
