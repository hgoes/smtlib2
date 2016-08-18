module Language.SMTLib2.Internals.Backend where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Expression hiding (Map)
import qualified Language.SMTLib2.Internals.Proof as P
import Language.SMTLib2.Strategy

import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show
import Data.Functor.Identity
import Text.Show

type SMTAction b r = b -> SMTMonad b (r,b)

mapAction :: Backend b => (r -> r') -> SMTAction b r -> SMTAction b r'
mapAction f act b = do
  (r,nb) <- act b
  return (f r,nb)

-- | A backend represents a specific type of SMT solver.
class (Typeable b,Functor (SMTMonad b),Monad (SMTMonad b),
       GetType (Expr b),GetType (Var b),GetType (QVar b),
       GetFunType (Fun b),
       GetType (FunArg b),
       GetType (LVar b),
       Typeable (Expr b),
       Typeable (Var b),
       Typeable (QVar b),
       Typeable (Fun b),
       Typeable (FunArg b),
       Typeable (LVar b),
       Typeable (ClauseId b),
       GCompare (Expr b),GShow (Expr b),
       GCompare (Var b),GShow (Var b),
       GCompare (QVar b),GShow (QVar b),
       GCompare (Fun b),GShow (Fun b),
       GCompare (FunArg b),GShow (FunArg b),
       GCompare (LVar b),GShow (LVar b),
       Ord (ClauseId b),Show (ClauseId b),
       Ord (Proof b),Show (Proof b),
       Show (Model b)) => Backend b where
  -- | The monad in which the backend executes queries.
  type SMTMonad b :: * -> *
  -- | The internal type of expressions.
  data Expr b :: Type -> *
  -- | The internal type of variables.
  type Var b :: Type -> *
  -- | The internal type of quantified variables.
  type QVar b :: Type -> *
  -- | The internal type of user-defined functions.
  type Fun b :: ([Type],Type) -> *
  type FunArg b :: Type -> *
  type LVar b :: Type -> *
  type ClauseId b :: *
  type Model b :: *
  type Proof b :: *
  setOption :: SMTOption -> SMTAction b ()
  getInfo :: SMTInfo i -> SMTAction b i
  comment :: String -> SMTAction b ()
  comment _ b = return ((),b)
  push :: SMTAction b ()
  pop :: SMTAction b ()
  declareVar :: Repr t -> Maybe String -> SMTAction b (Var b t)
  createQVar :: Repr t -> Maybe String -> SMTAction b (QVar b t)
  createFunArg :: Repr t -> Maybe String -> SMTAction b (FunArg b t)
  defineVar :: Maybe String -> Expr b t -> SMTAction b (Var b t)
  declareFun :: List Repr arg -> Repr t -> Maybe String -> SMTAction b (Fun b '(arg,t))
  defineFun :: Maybe String -> List (FunArg b) arg -> Expr b r -> SMTAction b (Fun b '(arg,r))
  assert :: Expr b BoolType -> SMTAction b ()
  assertId :: Expr b BoolType -> SMTAction b (ClauseId b)
  assertPartition :: Expr b BoolType -> Partition -> SMTAction b ()
  checkSat :: Maybe Tactic -> CheckSatLimits -> SMTAction b CheckSatResult
  getUnsatCore :: SMTAction b [ClauseId b]
  getValue :: Expr b t -> SMTAction b (Value t)
  getModel :: SMTAction b (Model b)
  modelEvaluate :: Model b -> Expr b t -> SMTAction b (Value t)
  getProof :: SMTAction b (Proof b)
  analyzeProof :: b -> Proof b -> P.Proof String (Expr b) (Proof b)
  simplify :: Expr b t -> SMTAction b (Expr b t)
  toBackend :: Expression (Var b) (QVar b) (Fun b) (FunArg b) (LVar b) (Expr b) t -> SMTAction b (Expr b t)
  fromBackend :: b -> Expr b t
              -> Expression (Var b) (QVar b) (Fun b) (FunArg b) (LVar b) (Expr b) t
  declareDatatypes :: [AnyDatatype] -> SMTAction b ()
  interpolate :: SMTAction b (Expr b BoolType)
  exit :: SMTAction b ()

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

newtype AssignmentModel b
  = AssignmentModel { assignments :: [Assignment b] }

data Assignment b
  = forall (t :: Type). VarAssignment (Var b t) (Expr b t)
  | forall (arg :: [Type]) (t :: Type).
    FunAssignment (Fun b '(arg,t)) (List (FunArg b) arg) (Expr b t)

-- | Options controling the behaviour of the SMT solver
data SMTOption
     = PrintSuccess Bool -- ^ Whether or not to print \"success\" after each operation
     | ProduceModels Bool -- ^ Produce a satisfying assignment after each successful checkSat
     | ProduceProofs Bool -- ^ Produce a proof of unsatisfiability after each failed checkSat
     | ProduceUnsatCores Bool -- ^ Enable the querying of unsatisfiable cores after a failed checkSat
     | ProduceInterpolants Bool -- ^ Enable the generation of craig interpolants
     | SMTLogic String
     deriving (Show,Eq,Ord)

-- | Solver information query type. Used with `Language.SMTLib2.getInfo`.
data SMTInfo i where
  SMTSolverName :: SMTInfo String
  SMTSolverVersion :: SMTInfo String

data UntypedVar v (t :: Type) = UntypedVar v (Repr t) deriving Typeable
 
data UntypedFun v (sig::([Type],Type)) where
  UntypedFun :: v -> List Repr arg -> Repr ret -> UntypedFun v '(arg,ret)
  deriving Typeable

data RenderedSubExpr t = RenderedSubExpr (Int -> ShowS)

instance GShow RenderedSubExpr where
  gshowsPrec p (RenderedSubExpr f) = f p

showsBackendExpr :: (Backend b) => b -> Int -> Expr b t -> ShowS
showsBackendExpr b p expr = showsPrec p recE
  where
    recE = runIdentity $ mapExpr return return return return return
           (\e -> return $ RenderedSubExpr (\p -> showsBackendExpr b p e)) load
    load = fromBackend b expr

instance Eq v => Eq (UntypedVar v t) where
  (==) (UntypedVar x _) (UntypedVar y _) = x==y

instance Eq v => Eq (UntypedFun v sig) where
  (==) (UntypedFun x _ _) (UntypedFun y _ _) = x==y

instance Ord v => Ord (UntypedVar v t) where
  compare (UntypedVar x _) (UntypedVar y _) = compare x y

instance Ord v => Ord (UntypedFun v sig) where
  compare (UntypedFun x _ _) (UntypedFun y _ _) = compare x y

instance Eq v => GEq (UntypedVar v) where
  geq (UntypedVar v1 tp1) (UntypedVar v2 tp2) = do
    Refl <- geq tp1 tp2
    if v1==v2
      then return Refl
      else Nothing

instance Eq v => GEq (UntypedFun v) where
  geq (UntypedFun v1 a1 r1) (UntypedFun v2 a2 r2) = do
    Refl <- geq a1 a2
    Refl <- geq r1 r2
    if v1==v2
      then return Refl
      else Nothing

instance Ord v => GCompare (UntypedVar v) where
  gcompare (UntypedVar v1 t1) (UntypedVar v2 t2)
    = case gcompare t1 t2 of
        GEQ -> case compare v1 v2 of
          EQ -> GEQ
          LT -> GLT
          GT -> GGT
        r -> r

instance Ord v => GCompare (UntypedFun v) where
  gcompare (UntypedFun v1 a1 t1) (UntypedFun v2 a2 t2)
    = case gcompare a1 a2 of
        GEQ -> case gcompare t1 t2 of
          GEQ -> case compare v1 v2 of
            EQ -> GEQ
            LT -> GLT
            GT -> GGT
          GLT -> GLT
          GGT -> GGT
        GLT -> GLT
        GGT -> GGT

instance Show v => Show (UntypedVar v t) where
  showsPrec p (UntypedVar v _) = showsPrec p v

instance Show v => Show (UntypedFun v sig) where
  showsPrec p (UntypedFun v _ _) = showsPrec p v

instance Show v => GShow (UntypedVar v) where
  gshowsPrec = showsPrec

instance Show v => GShow (UntypedFun v) where
  gshowsPrec = showsPrec

instance GetType (UntypedVar v) where
  getType (UntypedVar _ tp) = tp

instance GetFunType (UntypedFun v) where
  getFunType (UntypedFun _ arg tp) = (arg,tp)

instance (GShow (Var b),GShow (Expr b),GShow (Fun b),GShow (FunArg b))
         => Show (Assignment b) where
  showsPrec p (VarAssignment var expr)
    = showParen (p>10) $
      gshowsPrec 9 var .
      showString " = " .
      gshowsPrec 9 expr
  showsPrec p (FunAssignment fun args body)
    = showParen (p>10) $
      gshowsPrec 9 fun .
      showListWith id (runIdentity $ List.toList (return . gshowsPrec 0) args) .
      showString " = " .
      gshowsPrec 9 body

instance (GShow (Var b),GShow (Expr b),GShow (Fun b),GShow (FunArg b))
         => Show (AssignmentModel b) where
  showsPrec p (AssignmentModel assign)
    = showsPrec p assign
