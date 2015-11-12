module Language.SMTLib2.Internals.Backend where

import Language.SMTLib2.Internals.Type hiding (Constr,Field)
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Strategy

import Data.Typeable
import Data.GADT.Compare
import Data.GADT.Show
import Data.Functor.Identity

type SMTAction b r = b -> SMTMonad b (r,b)

class (Typeable b,Functor (SMTMonad b),Monad (SMTMonad b),
       Typeable (Expr b),
       Typeable (Var b),
       Typeable (QVar b),
       Typeable (Fun b),
       Typeable (Constr b),
       Typeable (Field b),
       Typeable (FunArg b),
       Typeable (ClauseId b),
       GCompare (Expr b),GShow (Expr b),
       GCompare (Var b),GShow (Var b),
       GCompare (QVar b),GShow (QVar b),
       GCompare (Fun b),GShow (Fun b),
       GCompare (Constr b),GShow (Constr b),
       GCompare (Field b),GShow (Field b),
       GCompare (FunArg b),GShow (FunArg b),
       Ord (ClauseId b),Show (ClauseId b)) => Backend b where
  type SMTMonad b :: * -> *
  type Expr b :: Type -> *
  type Var b :: Type -> *
  type QVar b :: Type -> *
  type Fun b :: ([Type],Type) -> *
  type Constr b :: ([Type],*) -> *
  type Field b :: (*,Type) -> *
  type FunArg b :: Type -> *
  type ClauseId b :: *
  setOption :: SMTOption -> SMTAction b ()
  getInfo :: SMTInfo i -> SMTAction b i
  comment :: String -> SMTAction b ()
  push :: SMTAction b ()
  pop :: SMTAction b ()
  declareVar :: GetType t => Maybe String -> SMTAction b (Var b t)
  createQVar :: GetType t => Maybe String -> SMTAction b (QVar b t)
  createFunArg :: GetType t => Maybe String -> SMTAction b (FunArg b t)
  defineVar :: GetType t => Maybe String -> Expr b t -> SMTAction b (Var b t)
  declareFun :: (GetTypes arg,GetType t) => Maybe String -> SMTAction b (Fun b '(arg,t))
  defineFun :: (GetTypes arg,GetType r) => Maybe String
            -> Args (FunArg b) arg -> Expr b r -> SMTAction b (Fun b '(arg,r))
  assert :: Expr b BoolType -> SMTAction b ()
  assertId :: Expr b BoolType -> SMTAction b (ClauseId b)
  assertPartition :: Expr b BoolType -> Partition -> SMTAction b ()
  checkSat :: Maybe Tactic -> CheckSatLimits -> SMTAction b CheckSatResult
  getUnsatCore :: SMTAction b [ClauseId b]
  getValue :: GetType t => Expr b t -> SMTAction b (Value (Constr b) t)
  getModel :: SMTAction b (Model b)
  getProof :: SMTAction b (Expr b BoolType)
  simplify :: GetType t => Expr b t -> SMTAction b (Expr b t)
  toBackend :: GetType t => Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t -> SMTAction b (Expr b t)
  fromBackend :: GetType t => b -> Expr b t
              -> Expression (Var b) (QVar b) (Fun b) (Constr b) (Field b) (FunArg b) (Expr b) t
  declareDatatypes :: TypeCollection sigs
                   -> SMTAction b (BackendTypeCollection (Constr b) (Field b) sigs)
  interpolate :: SMTAction b (Expr b BoolType)
  exit :: SMTAction b ()

type BackendTypeCollection con field sigs
  = Datatypes (BackendDatatype con field) sigs

newtype BackendDatatype con field (sig :: ([[Type]],*)) --(sigs::[[Type]]) dt
  = BackendDatatype { bconstructors :: Constrs (BackendConstr con field) (Fst sig) (Snd sig) }

data BackendConstr con field (sig :: ([Type],*))
  = BackendConstr { bconName :: String
                  , bconRepr :: con sig
                  , bconFields :: Args (BackendField field (Snd sig)) (Fst sig)
                  , bconstruct :: Args ConcreteValue (Fst sig) -> (Snd sig)
                  , bconTest :: Snd sig -> Bool
                  }

data BackendField (field :: (*,Type) -> *) dt (t :: Type)
  = BackendField { bfieldName :: String
                 , bfieldRepr :: field '(dt,t)
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
  = forall (t :: Type). GetType t => VarAssignment (Var b t) (Expr b t)
  | forall (arg :: [Type]) (t :: Type). (GetTypes arg,GetType t) => FunAssignment (Fun b '(arg,t)) (Args (FunArg b) arg) (Expr b t)

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

data UntypedVar v (t :: Type) where
  UntypedVar :: GetType t => v -> UntypedVar v t
 
data UntypedFun v (sig::([Type],Type)) where
  UntypedFun :: (GetTypes arg,GetType ret) => v -> UntypedFun v '(arg,ret)

data UntypedCon v (sig::([Type],*)) where
  UntypedCon :: (GetTypes arg,IsDatatype dt) => v -> UntypedCon v '(arg,dt)

data UntypedField v (sig::(*,Type)) where
  UntypedField :: (IsDatatype dt,GetType t) => v -> UntypedField v '(dt,t)

data RenderedSubExpr t = RenderedSubExpr (Int -> ShowS)

instance GShow RenderedSubExpr where
  gshowsPrec p (RenderedSubExpr f) = f p

showsBackendExpr :: (Backend b,GetType t) => b -> Int -> Expr b t -> ShowS
showsBackendExpr b p expr = showsPrec p recE
  where
    recE = runIdentity $ mapExpr return return return return return return
           (\e -> return $ RenderedSubExpr (\p -> showsBackendExpr b p e)) load
    load = fromBackend b expr

instance Eq v => Eq (UntypedVar v t) where
  (==) (UntypedVar x) (UntypedVar y) = x==y

instance Eq v => Eq (UntypedFun v sig) where
  (==) (UntypedFun x) (UntypedFun y) = x==y

instance Eq v => Eq (UntypedCon v sig) where
  (==) (UntypedCon x) (UntypedCon y) = x==y

instance Eq v => Eq (UntypedField v sig) where
  (==) (UntypedField x) (UntypedField y) = x==y

instance Ord v => Ord (UntypedVar v t) where
  compare (UntypedVar x) (UntypedVar y) = compare x y

instance Ord v => Ord (UntypedFun v sig) where
  compare (UntypedFun x) (UntypedFun y) = compare x y

instance Ord v => Ord (UntypedCon v sig) where
  compare (UntypedCon x) (UntypedCon y) = compare x y

instance Ord v => Ord (UntypedField v sig) where
  compare (UntypedField x) (UntypedField y) = compare x y

instance Eq v => GEq (UntypedVar v) where
  geq x1@(UntypedVar v1) x2@(UntypedVar v2) = case x1 of
    (_::UntypedVar v p) -> case x2 of
      (_::UntypedVar v q) -> do
        Refl <- geq (getType::Repr p)
                    (getType::Repr q)
        if v1==v2
          then return Refl
          else Nothing

instance Eq v => GEq (UntypedFun v) where
  geq x1@(UntypedFun v1) x2@(UntypedFun v2) = case x1 of
    (_::UntypedFun v '(arg1,t1)) -> case x2 of
      (_::UntypedFun v '(arg2,t2)) -> do
        Refl <- geq (getTypes::Args Repr arg1)
                    (getTypes::Args Repr arg2)
        Refl <- geq (getType::Repr t1)
                    (getType::Repr t2)
        if v1==v2
          then return Refl
          else Nothing

instance Eq v => GEq (UntypedCon v) where
  geq x1@(UntypedCon v1) x2@(UntypedCon v2) = case x1 of
    (_::UntypedCon v '(arg1,dt1)) -> case x2 of
      (_::UntypedCon v '(arg2,dt2)) -> do
        Refl <- geq (getTypes::Args Repr arg1)
                    (getTypes::Args Repr arg2)
        Refl <- eqT :: Maybe (dt1 :~: dt2)
        if v1==v2
          then return Refl
          else Nothing

instance Eq v => GEq (UntypedField v) where
  geq x1@(UntypedField v1) x2@(UntypedField v2) = case x1 of
    (_::UntypedField v '(dt1,t1)) -> case x2 of
      (_::UntypedField v '(dt2,t2)) -> do
        Refl <- eqT :: Maybe (dt1 :~: dt2)
        Refl <- geq (getType::Repr t1)
                    (getType::Repr t2)
        if v1==v2
          then return Refl
          else Nothing

instance Ord v => GCompare (UntypedVar v) where
  gcompare x1@(UntypedVar v1) x2@(UntypedVar v2) = case x1 of
    (_::UntypedVar v p) -> case x2 of
      (_::UntypedVar v q) -> case gcompare (getType::Repr p)
                                           (getType::Repr q) of
        GEQ -> case compare v1 v2 of
          EQ -> GEQ
          LT -> GLT
          GT -> GGT
        r -> r

instance Ord v => GCompare (UntypedFun v) where
  gcompare x1@(UntypedFun v1) x2@(UntypedFun v2) = case x1 of
    (_::UntypedFun v '(arg1,t1)) -> case x2 of
      (_::UntypedFun v '(arg2,t2)) -> case gcompare (getTypes::Args Repr arg1)
                                                    (getTypes::Args Repr arg2) of
        GEQ -> case gcompare (getType::Repr t1)
                             (getType::Repr t2) of
          GEQ -> case compare v1 v2 of
            EQ -> GEQ
            LT -> GLT
            GT -> GGT
          GLT -> GLT
          GGT -> GGT
        GLT -> GLT
        GGT -> GGT

instance Ord v => GCompare (UntypedCon v) where
  gcompare x1@(UntypedCon v1) x2@(UntypedCon v2) = case x1 of
    (_::UntypedCon v '(arg1,dt1)) -> case x2 of
      (_::UntypedCon v '(arg2,dt2)) -> case gcompare (getTypes::Args Repr arg1)
                                                     (getTypes::Args Repr arg2) of
        GEQ -> case eqT :: Maybe (dt1 :~: dt2) of
          Just Refl -> case compare v1 v2 of
            EQ -> GEQ
            LT -> GLT
            GT -> GGT
          Nothing -> case compare (typeOf (Proxy::Proxy dt1))
                                  (typeOf (Proxy::Proxy dt2)) of
            LT -> GLT
            GT -> GGT
        GLT -> GLT
        GGT -> GGT

instance Ord v => GCompare (UntypedField v) where
  gcompare x1@(UntypedField v1) x2@(UntypedField v2) = case x1 of
    (_::UntypedField v '(dt1,t1)) -> case x2 of
      (_::UntypedField v '(dt2,t2)) -> case gcompare (getType::Repr t1)
                                                     (getType::Repr t2) of
        GEQ -> case eqT :: Maybe (dt1 :~: dt2) of
          Just Refl -> case compare v1 v2 of
            EQ -> GEQ
            LT -> GLT
            GT -> GGT
          Nothing -> case compare (typeOf (Proxy::Proxy dt1))
                                  (typeOf (Proxy::Proxy dt2)) of
            LT -> GLT
            GT -> GGT
        GLT -> GLT
        GGT -> GGT

instance Show v => Show (UntypedVar v t) where
  showsPrec p (UntypedVar v) = showsPrec p v

instance Show v => Show (UntypedFun v sig) where
  showsPrec p (UntypedFun v) = showsPrec p v

instance Show v => Show (UntypedCon v sig) where
  showsPrec p (UntypedCon v) = showsPrec p v

instance Show v => Show (UntypedField v sig) where
  showsPrec p (UntypedField v) = showsPrec p v

instance Show v => GShow (UntypedVar v) where
  gshowsPrec = showsPrec

instance Show v => GShow (UntypedFun v) where
  gshowsPrec = showsPrec

instance Show v => GShow (UntypedCon v) where
  gshowsPrec = showsPrec

instance Show v => GShow (UntypedField v) where
  gshowsPrec = showsPrec
