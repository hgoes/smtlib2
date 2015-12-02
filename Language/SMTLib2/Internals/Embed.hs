module Language.SMTLib2.Internals.Embed where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Backend

import Data.Functor.Identity
import Data.Proxy
import Control.Monad.State
import qualified Control.Monad.State.Strict as S
import Control.Monad.Trans
import Data.Typeable
import Data.GADT.Compare

class (Monad m,
       GCompare (EmVar m e),
       GCompare (EmQVar m e),
       GCompare (EmFun m e),
       GCompare (EmConstr m e),
       GCompare (EmField m e),
       GCompare (EmFunArg m e),
       GCompare (EmLVar m e),
       Typeable (EmConstr m e)
      ) => Embed m e where
  type EmVar m e :: Type -> *
  type EmQVar m e :: Type -> *
  type EmFun m e :: ([Type],Type) -> *
  type EmConstr m e :: ([Type],*) -> *
  type EmField m e :: (*,Type) -> *
  type EmFunArg m e :: Type -> *
  type EmLVar m e :: Type -> *
  embed :: GetType tp => Expression (EmVar m e) (EmQVar m e) (EmFun m e) (EmConstr m e) (EmField m e) (EmFunArg m e) (EmLVar m e) e tp
        -> m (e tp)
  embedQuantifier :: GetTypes arg => Quantifier
                  -> (forall m e. Embed m e => Args (EmQVar m e) arg -> m (e BoolType))
                  -> m (e BoolType)
  embedConstrTest :: IsDatatype dt => String -> Proxy dt -> e (DataType dt)
                  -> m (e BoolType)
  embedGetField :: (IsDatatype dt,GetType tp)
                => String -> String -> Proxy dt -> Proxy tp
                -> e (DataType dt)
                -> m (e tp)
  embedConst :: GetType tp => ConcreteValue tp -> m (e tp)

class (GCompare (ExVar i e),
       GCompare (ExQVar i e),
       GCompare (ExFun i e),
       GCompare (ExConstr i e),
       GCompare (ExField i e),
       GCompare (ExFunArg i e),
       GCompare (ExLVar i e),
       Typeable (ExConstr i e)) => Extract i e where
  type ExVar i e :: Type -> *
  type ExQVar i e :: Type -> *
  type ExFun i e :: ([Type],Type) -> *
  type ExConstr i e :: ([Type],*) -> *
  type ExField i e :: (*,Type) -> *
  type ExFunArg i e :: Type -> *
  type ExLVar i e :: Type -> *
  extract :: GetType tp => i -> e tp
          -> Maybe (Expression (ExVar i e) (ExQVar i e) (ExFun i e) (ExConstr i e) (ExField i e) (ExFunArg i e) (ExLVar i e) e tp)

instance (Backend b,e ~ Expr b) => Embed (SMT b) e where
  type EmVar (SMT b) e = Var b
  type EmQVar (SMT b) e = QVar b
  type EmFun (SMT b) e = Fun b
  type EmConstr (SMT b) e = Constr b
  type EmField (SMT b) e = Field b
  type EmFunArg (SMT b) e = FunArg b
  type EmLVar (SMT b) e = LVar b
  embed = embedSMT . toBackend
  embedQuantifier quant f = do
    args <- withArgs (embedSMT (createQVar Nothing))
    body <- f args
    embedSMT $ toBackend (Quantification quant args body)
  embedConstrTest name (_::Proxy dt) e = do
    st <- get
    let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
    lookupConstructor name bdt $
      \bcon -> embedSMT $ toBackend (App (Test (bconRepr bcon)) (Arg e NoArg))
  embedGetField name fname (_::Proxy dt) _ e = do
    st <- get
    lookupDatatypeField (DTProxy::DTProxy dt) fname name (datatypes st) $
      \field -> case gcast (bfieldRepr field) of
      Just field' -> embedSMT $ toBackend (App (Field field') (Arg e NoArg))
  embedConst v = do
    rv <- mkAbstr v
    embedSMT $ toBackend (Const rv)

newtype BackendInfo b = BackendInfo b

instance (Backend b,e ~ Expr b) => Extract (BackendInfo b) e where
  type ExVar (BackendInfo b) e = Var b
  type ExQVar (BackendInfo b) e = QVar b
  type ExFun (BackendInfo b) e = Fun b
  type ExConstr (BackendInfo b) e = Constr b
  type ExField (BackendInfo b) e = Field b
  type ExFunArg (BackendInfo b) e = FunArg b
  type ExLVar (BackendInfo b) e = LVar b
  extract (BackendInfo b) e = Just (fromBackend b e)

data SMTExpr var qvar fun con field farg lvar tp where
  SMTExpr :: Expression var qvar fun con field farg lvar
             (SMTExpr var qvar fun con field farg lvar)
             tp -> SMTExpr var qvar fun con field farg lvar tp
  SMTQuant :: GetTypes args
           => Quantifier
           -> (Args qvar args
               -> SMTExpr var qvar fun con field farg lvar BoolType)
           -> SMTExpr var qvar fun con field farg lvar BoolType
  SMTTestCon :: IsDatatype dt => String -> Proxy dt
             -> SMTExpr var qvar fun con field farg lvar (DataType dt)
             -> SMTExpr var qvar fun con field farg lvar BoolType
  SMTGetField :: (IsDatatype dt,GetType tp)
              => String -> String -> Proxy dt -> Proxy tp
              -> SMTExpr var qvar fun con field farg lvar (DataType dt)
              -> SMTExpr var qvar fun con field farg lvar tp
  SMTConst :: ConcreteValue tp -> SMTExpr var qvar fun con field farg lvar tp

instance (GCompare var,
          GCompare qvar,
          GCompare fun,
          GCompare con,
          GCompare field,
          GCompare farg,
          GCompare lvar,
          Typeable con
         ) => Embed Identity (SMTExpr var qvar fun con field farg lvar) where
  type EmVar Identity (SMTExpr var qvar fun con field farg lvar) = var
  type EmQVar Identity (SMTExpr var qvar fun con field farg lvar) = qvar
  type EmFun Identity (SMTExpr var qvar fun con field farg lvar) = fun
  type EmConstr Identity (SMTExpr var qvar fun con field farg lvar) = con
  type EmField Identity (SMTExpr var qvar fun con field farg lvar) = field
  type EmFunArg Identity (SMTExpr var qvar fun con field farg lvar) = farg
  type EmLVar Identity (SMTExpr var qvar fun con field farg lvar) = lvar
  embed e = return (SMTExpr e)
  embedQuantifier quant f = return $ SMTQuant quant (runIdentity . f)
  embedConstrTest name pr e = return $ SMTTestCon name pr e
  embedGetField name fname dt pr e = return $ SMTGetField name fname dt pr e
  embedConst = return . SMTConst

instance (GCompare var,
          GCompare qvar,
          GCompare fun,
          GCompare con,
          GCompare field,
          GCompare farg,
          GCompare lvar,
          Typeable con) => Extract () (SMTExpr var qvar fun con field farg lvar) where
  type ExVar () (SMTExpr var qvar fun con field farg lvar) = var
  type ExQVar () (SMTExpr var qvar fun con field farg lvar) = qvar
  type ExFun () (SMTExpr var qvar fun con field farg lvar) = fun
  type ExConstr () (SMTExpr var qvar fun con field farg lvar) = con
  type ExField () (SMTExpr var qvar fun con field farg lvar) = field
  type ExFunArg () (SMTExpr var qvar fun con field farg lvar) = farg
  type ExLVar () (SMTExpr var qvar fun con field farg lvar) = lvar
  extract _ (SMTExpr e) = Just e
  extract _ _ = Nothing

encodeExpr :: (Backend b,GetType tp)
           => SMTExpr (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (LVar b) tp
           -> SMT b (Expr b tp)
encodeExpr (SMTExpr e) = do
  e' <- mapExpr return return return return return return return
        encodeExpr e
  embedSMT $ toBackend e'
encodeExpr (SMTQuant q f) = do
  args <- withArgs (embedSMT (createQVar Nothing))
  body <- encodeExpr (f args)
  embedSMT $ toBackend (Quantification q args body)
encodeExpr (SMTTestCon name (_::Proxy dt) e) = do
  e' <- encodeExpr e
  st <- get
  let bdt = lookupDatatype (DTProxy::DTProxy dt) (datatypes st)
  lookupConstructor name bdt $
    \bcon -> embedSMT $ toBackend (App (Test (bconRepr bcon)) (Arg e' NoArg))
encodeExpr (SMTGetField name fname (_::Proxy dt) _ e) = do
  e' <- encodeExpr e
  st <- get
  lookupDatatypeField (DTProxy::DTProxy dt) fname name (datatypes st) $
    \field -> case gcast (bfieldRepr field) of
    Just field' -> embedSMT $ toBackend (App (Field field') (Arg e' NoArg))
encodeExpr (SMTConst c) = do
  rc <- mkAbstr c
  embedSMT $ toBackend (Const rc)

decodeExpr :: (Backend b,GetType tp) => Expr b tp
           -> SMT b (SMTExpr (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (LVar b) tp)
decodeExpr e = do
  st <- get
  let e' = fromBackend (backend st) e
  e'' <- mapExpr return return return return return return return decodeExpr e'
  return (SMTExpr e'')

instance Embed m e => Embed (StateT s m) e where
  type EmVar (StateT s m) e = EmVar m e
  type EmQVar (StateT s m) e = EmQVar m e
  type EmFun (StateT s m) e = EmFun m e
  type EmConstr (StateT s m) e = EmConstr m e
  type EmField (StateT s m) e = EmField m e
  type EmFunArg (StateT s m) e = EmFunArg m e
  type EmLVar (StateT s m) e = EmLVar m e
  embed = lift . embed
  embedQuantifier q f = lift (embedQuantifier q f)
  embedConstrTest name dt e = lift (embedConstrTest name dt e)
  embedGetField name fname dt pr e = lift (embedGetField name fname dt pr e)
  embedConst = lift . embedConst

instance Embed m e => Embed (S.StateT s m) e where
  type EmVar (S.StateT s m) e = EmVar m e
  type EmQVar (S.StateT s m) e = EmQVar m e
  type EmFun (S.StateT s m) e = EmFun m e
  type EmConstr (S.StateT s m) e = EmConstr m e
  type EmField (S.StateT s m) e = EmField m e
  type EmFunArg (S.StateT s m) e = EmFunArg m e
  type EmLVar (S.StateT s m) e = EmLVar m e
  embed = lift . embed
  embedQuantifier q f = lift (embedQuantifier q f)
  embedConstrTest name dt e = lift (embedConstrTest name dt e)
  embedGetField name fname dt pr e = lift (embedGetField name fname dt pr e)
  embedConst = lift . embedConst

data AnalyzedExpr i e tp
  = AnalyzedExpr (Maybe (Expression
                         (ExVar i e)
                         (ExQVar i e)
                         (ExFun i e)
                         (ExConstr i e)
                         (ExField i e)
                         (ExFunArg i e)
                         (ExLVar i e)
                         (AnalyzedExpr i e)
                         tp)) (e tp)

analyze' :: (Extract i e,GetType tp) => i -> e tp -> AnalyzedExpr i e tp
analyze' i expr
  = AnalyzedExpr expr' expr
  where
    expr' = do
      e <- extract i expr
      return $ runIdentity (mapExpr return return return return return return return
                            (return . analyze' i) e)

analyze :: (Backend b,GetType tp) => Expr b tp -> SMT b (AnalyzedExpr (BackendInfo b) (Expr b) tp)
analyze e = do
  st <- get
  return (analyze' (BackendInfo (backend st)) e)
