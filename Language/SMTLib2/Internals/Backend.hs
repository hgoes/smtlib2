module Language.SMTLib2.Internals.Backend where

import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import qualified Language.SMTLib2.Internals.Type as Type
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Strategy

import Data.Typeable

class (Typeable b,Functor (SMTMonad b),Monad (SMTMonad b),
       Typeable (Expr b),
       Typeable (Var b),
       Typeable (QVar b),
       Typeable (Fun b),
       Typeable (Constr b),
       Typeable (Field b),
       Typeable (FunArg b),
       Typeable (ClauseId b),
       OrdVar (Expr b),ShowVar (Expr b),
       OrdVar (Var b),ShowVar (Var b),
       OrdVar (QVar b),ShowVar (QVar b),
       OrdFun (Fun b),ShowFun (Fun b),
       OrdCon (Constr b),ShowCon (Constr b),
       OrdField (Field b),ShowField (Field b),
       OrdVar (FunArg b),ShowVar (FunArg b)) => Backend b where
  type SMTMonad b :: * -> *
  type Expr b :: Type -> *
  type Var b :: Type -> *
  type QVar b :: Type -> *
  type Fun b :: [Type] -> Type -> *
  type Constr b :: [Type] -> * -> *
  type Field b :: * -> Type -> *
  type FunArg b :: Type -> *
  type ClauseId b :: *
  setOption :: b -> SMTOption -> SMTMonad b b
  getInfo :: b -> SMTInfo i -> SMTMonad b (i,b)
  comment :: b -> String -> SMTMonad b b
  push :: b -> SMTMonad b b
  pop :: b -> SMTMonad b b
  declareVar :: GetType t => b -> Maybe String -> SMTMonad b (Var b t,b)
  createQVar :: GetType t => b -> Maybe String -> SMTMonad b (QVar b t,b)
  createFunArg :: GetType t => b -> Maybe String -> SMTMonad b (FunArg b t,b)
  defineVar :: GetType t => b -> Maybe String -> Expr b t -> SMTMonad b (Var b t,b)
  declareFun :: (Liftable arg,GetType t) => b -> Maybe String -> SMTMonad b (Fun b arg t,b)
  defineFun :: (Liftable arg,GetType r) => b -> Maybe String
            -> Args (FunArg b) arg -> Expr b r -> SMTMonad b (Fun b arg r,b)
  assert :: b -> Expr b BoolType -> SMTMonad b b
  assertId :: b -> Expr b BoolType -> SMTMonad b (ClauseId b,b)
  assertPartition :: b -> Expr b BoolType -> Partition -> SMTMonad b b
  checkSat :: b -> Maybe Tactic -> CheckSatLimits -> SMTMonad b (CheckSatResult,b)
  getUnsatCore :: b -> SMTMonad b ([ClauseId b],b)
  getValue :: GetType t => b -> Expr b t -> SMTMonad b (Value (Constr b) t,b)
  getModel :: b -> SMTMonad b (Model b,b)
  getProof :: b -> SMTMonad b (Expr b BoolType,b)
  simplify :: GetType t => b -> Expr b t -> SMTMonad b (Expr b t,b)
  toBackend :: GetType t => b -> Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t -> SMTMonad b (Expr b t,b)
  fromBackend :: GetType t => b -> Expr b t
              -> SMTMonad b (Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t,b)
  declareDatatypes :: b -> TypeCollection sigs
                   -> SMTMonad b (BackendTypeCollection (Constr b) (Field b) sigs,b)
  interpolate :: b -> SMTMonad b (Expr b BoolType,b)

type BackendTypeCollection con field sigs
  = Datatypes (BackendDatatype con field) sigs

newtype BackendDatatype con field (sigs::[[Type]]) dt
  = BackendDatatype { bconstructors :: Constrs (BackendConstr con field) sigs dt }

data BackendConstr con field (arg :: [Type]) dt
  = BackendConstr { bconName :: String
                  , bconRepr :: con arg dt
                  , bconFields :: Args (BackendField field dt) arg
                  , bconstruct :: Args ConcreteValue arg -> dt
                  , bconTest :: dt -> Bool
                  }

data BackendField field dt (t::Type)
  = BackendField { bfieldName :: String
                 , bfieldRepr :: field dt t
                 , bfieldGet :: dt -> ConcreteValue t }

-- | The interpolation partition
data Partition = PartitionA
               | PartitionB
               deriving (Show,Eq,Ord,Typeable)

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

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print \"success\" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     | ProduceProofs Bool -- ^ Produce a proof of unsatisfiability after each failed checkSat
     | ProduceUnsatCores Bool -- ^ Enable the querying of unsatisfiable cores after a failed checkSat
     | ProduceInterpolants Bool -- ^ Enable the generation of craig interpolants
     | SMTLogic String
     deriving (Show,Eq,Ord)

data SMTInfo i where
  SMTSolverName :: SMTInfo String
  SMTSolverVersion :: SMTInfo String

newtype UntypedVar v (t :: Type) = UntypedVar { untypedVar :: v } deriving Typeable

instance Ord v => OrdVar (UntypedVar v) where
  cmpVar (UntypedVar v1) (UntypedVar v2) = compare v1 v2

instance Show v => ShowVar (UntypedVar v) where
  showVar p (UntypedVar v) = showsPrec p v
