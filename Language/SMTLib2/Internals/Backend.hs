module Language.SMTLib2.Internals.Backend where

import Language.SMTLib2.Internals.Value
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Expression

class Monad (MonadB b) => Backend b where
  type MonadB b :: * -> *
  type Expr b :: Type -> *
  type Var b :: Type -> *
  type QVar b :: Type -> *
  assert :: b -> Expr b BoolType -> MonadB b ()  
  toBackend :: b -> Expression (Var b) (QVar b) (Expr b) t -> MonadB b (Expr b t)
  fromBackend :: b -> Expr b t -> MonadB b (Expression (Var b) (QVar b) (Expr b) t)
