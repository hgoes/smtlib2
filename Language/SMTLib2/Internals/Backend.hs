module Language.SMTLib2.Internals.Backend where

import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Expression

class Monad b => Backend (b :: * -> *) where
  type Expr b :: Type -> *
  type Var b :: Type -> *
  type QVar b :: Type -> *
  type Fun b :: [Type] -> Type -> *
  type Constr b :: [Type] -> * -> *
  type Field b :: * -> Type -> *
  type FunArg b :: Type -> *
  declareVar :: b (Var b t)
  defineVar :: Expr b t -> b (Var b t)
  declareFun :: b (Fun b arg t)
  funArgs :: (Args (FunArg b) arg -> b a) -> b a
  defineFun :: Args (FunArg b) arg -> Expr b r -> b (Fun b arg r)
  assert :: Expr b BoolType -> b ()
  toBackend :: Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t -> b (Expr b t)
  fromBackend :: Expr b t -> Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t
  declareDatatype :: Constrs Type.Constr sigs t -> b (Constrs (Constr b) sigs t)
