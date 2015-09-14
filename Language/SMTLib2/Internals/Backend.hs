module Language.SMTLib2.Internals.Backend where

import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Strategy

import Data.Typeable

class (Typeable b,Monad (SMTMonad b),
       Typeable (Expr b),
       Typeable (Var b),
       Typeable (QVar b),
       Typeable (Fun b),
       Typeable (Constr b),
       Typeable (Field b),
       Typeable (FunArg b),
       Typeable (ClauseId b)) => Backend b where
  type SMTMonad b :: * -> *
  type Expr b :: Type -> *
  type Var b :: Type -> *
  type QVar b :: Type -> *
  type Fun b :: [Type] -> Type -> *
  type Constr b :: [Type] -> * -> *
  type Field b :: * -> Type -> *
  type FunArg b :: Type -> *
  type ClauseId b :: *
  compareQVar :: Proxy b -> QVar b x -> QVar b y -> Ordering
  push :: b -> SMTMonad b b
  pop :: b -> SMTMonad b b
  declareVar :: GetType t => b -> Maybe String -> SMTMonad b (Var b t,b)
  createQVar :: GetType t => b -> Maybe String -> SMTMonad b (QVar b t,b)
  defineVar :: GetType t => b -> Maybe String -> Expr b t -> SMTMonad b (Var b t,b)
  declareFun :: (Liftable arg,GetType t) => b -> Maybe String -> SMTMonad b (Fun b arg t,b)
  defineFun :: (Liftable arg,GetType r) => b -> Maybe String
            -> (Args (FunArg b) arg -> Expr b r) -> SMTMonad b (Fun b arg r,b)
  assert :: b -> Expr b BoolType -> SMTMonad b b
  assertId :: b -> Expr b BoolType -> SMTMonad b (ClauseId b,b)
  checkSat :: b -> Maybe Tactic -> CheckSatLimits -> SMTMonad b (CheckSatResult,b)
  getUnsatCore :: b -> SMTMonad b ([ClauseId b],b)
  getValue :: GetType t => b -> Expr b t -> SMTMonad b (Value (Constr b) t,b)
  getModel :: b -> SMTMonad b (Model b,b)
  getProof :: b -> SMTMonad b (Expr b BoolType,b)
  simplify :: GetType t => b -> Expr b t -> SMTMonad b (Expr b t,b)
  toBackend :: b -> Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t -> SMTMonad b (Expr b t,b)
  fromBackend :: b -> Expr b t
              -> SMTMonad b (Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t,b)
  declareDatatype :: b -> Constrs Type.Constr sigs t
                  -> SMTMonad b (Constrs (Constr b) sigs t,b)

-- | The result of a check-sat query
data CheckSatResult
  = Sat -- ^ The formula is satisfiable
  | Unsat -- ^ The formula is unsatisfiable
  | Unknown -- ^ The solver cannot determine the satisfiability of a formula
  deriving (Show,Eq,Ord,Typeable)

-- | Describe limits on the ressources that an SMT-solver can use
data CheckSatLimits = CheckSatLimits { limitTime :: Maybe Integer -- ^ A limit on the amount of time the solver can spend on the problem (in milliseconds)
                                     , limitMemory :: Maybe Integer -- ^ A limit on the amount of memory the solver can use (in megabytes)
                                     } deriving (Show,Eq,Ord,Typeable)

newtype Model b
  = Model { assignments :: [Assignment b] }

data Assignment b
  = forall (t :: Type). VarAssignment (Var b t) (Expr b t)
  | forall (arg :: [Type]) (t :: Type). FunAssignment (Fun b arg t) (Args (FunArg b) arg) (Expr b t)
