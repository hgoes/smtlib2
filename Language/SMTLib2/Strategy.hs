module Language.SMTLib2.Strategy where

data Tactic
  = Skip
  | AndThen [Tactic]
  | OrElse [Tactic]
  | ParOr [Tactic]
  | ParThen Tactic Tactic
  | TryFor Tactic Integer
  | If (Probe Bool) Tactic Tactic
  | FailIf (Probe Bool)
  | forall p. Show p => UsingParams (BuiltInTactic p) [p]

data Probe a where
  ProbeBoolConst :: Bool -> Probe Bool
  ProbeIntConst :: Integer -> Probe Integer
  ProbeAnd :: [Probe Bool] -> Probe Bool
  ProbeOr :: [Probe Bool] -> Probe Bool
  ProbeNot :: Probe Bool -> Probe Bool
  ProbeEq :: Show a => Probe a -> Probe a -> Probe Bool
  ProbeGt :: Probe Integer -> Probe Integer -> Probe Bool
  ProbeGe :: Probe Integer -> Probe Integer -> Probe Bool
  ProbeLt :: Probe Integer -> Probe Integer -> Probe Bool
  ProbeLe :: Probe Integer -> Probe Integer -> Probe Bool
  IsPB :: Probe Bool
  ArithMaxDeg :: Probe Integer
  ArithAvgDeg :: Probe Integer
  ArithMaxBW :: Probe Integer
  ArithAvgBW :: Probe Integer
  IsQFLIA :: Probe Bool
  IsQFLRA :: Probe Bool
  IsQFLIRA :: Probe Bool
  IsILP :: Probe Bool
  IsQFNIA :: Probe Bool
  IsQFNRA :: Probe Bool
  IsNIA :: Probe Bool
  IsNRA :: Probe Bool
  IsUnbounded :: Probe Bool
  Memory :: Probe Integer
  Depth :: Probe Integer
  Size :: Probe Integer
  NumExprs :: Probe Integer
  NumConsts :: Probe Integer
  NumBoolConsts :: Probe Integer
  NumArithConsts :: Probe Integer
  NumBVConsts :: Probe Integer
  ProduceProofs :: Probe Bool
  ProduceModel :: Probe Bool
  ProduceUnsatCores :: Probe Bool
  HasPatterns :: Probe Bool
  IsPropositional :: Probe Bool
  IsQFBV :: Probe Bool
  IsQFBVEQ :: Probe Bool

data AnyPar = ParBool Bool
            | ParInt Integer
            | ParDouble Double
            deriving Show

data BuiltInTactic p where
  QFLRATactic :: BuiltInTactic QFLRATacticP
  CustomTactic :: String -> BuiltInTactic (String,AnyPar)

data QFLRATacticP
  = ArithBranchCutRatio Integer
  deriving Show

instance Show Tactic where
  showsPrec _ Skip = showString "Skip"
  showsPrec p (AndThen ts) = showParen (p>10) (showString "AndThen " .
                                               showsPrec 0 ts)
  showsPrec p (OrElse ts) = showParen (p>10) (showString "OrElse " .
                                              showsPrec 0 ts)
  showsPrec p (ParOr ts) = showParen (p>10) (showString "ParOr " .
                                             showsPrec 0 ts)
  showsPrec p (ParThen t1 t2) = showParen (p>10) (showString "ParThen " .
                                                  showsPrec 11 t1 .
                                                  showChar ' ' .
                                                  showsPrec 11 t2)
  showsPrec p (TryFor t n) = showParen (p>10) (showString "TryFor " .
                                               showsPrec 11 t .
                                               showChar ' ' .
                                               showsPrec 11 n)
  showsPrec p (If c t1 t2) = showParen (p>10) (showString "If " .
                                               showsPrec 11 c .
                                               showChar ' ' .
                                               showsPrec 11 t1 .
                                               showChar ' ' .
                                               showsPrec 11 t2)
  showsPrec p (FailIf c) = showParen (p>10) (showString "FailIf " .
                                             showsPrec 11 c)
  showsPrec p (UsingParams t []) = showsPrec p t
  showsPrec p (UsingParams t pars) = showParen (p>10) (showString "UsingParams " .
                                                       showsPrec 11 t .
                                                       showChar ' ' .
                                                       showsPrec 11 pars)

instance Show (BuiltInTactic p) where
  showsPrec _ QFLRATactic = showString "QFLRATactic"
  showsPrec _ (CustomTactic name) = showString name

instance Show a => Show (Probe a) where
  showsPrec p (ProbeBoolConst c) = showParen (p>10) (showString "ProbeBoolConst " .
                                                     showsPrec 11 c)
  showsPrec p (ProbeIntConst c) = showParen (p>10) (showString "ProbeIntConst " .
                                                    showsPrec 11 c)
  showsPrec p (ProbeAnd ps) = showParen (p>10) (showString "ProbeAnd " .
                                                showsPrec 11 ps)
  showsPrec p (ProbeOr ps) = showParen (p>10) (showString "ProbeOr " .
                                                showsPrec 11 ps)
  showsPrec p (ProbeNot c) = showParen (p>10) (showString "ProbeNot " .
                                               showsPrec 11 c)
  showsPrec p (ProbeEq p1 p2) = showParen (p>10) (showString "ProbeEq " .
                                                  showsPrec 11 p1 .
                                                  showChar ' ' .
                                                  showsPrec 11 p2)
  showsPrec p (ProbeGe p1 p2) = showParen (p>10) (showString "ProbeGe " .
                                                  showsPrec 11 p1 .
                                                  showChar ' ' .
                                                  showsPrec 11 p2)
  showsPrec p (ProbeGt p1 p2) = showParen (p>10) (showString "ProbeGt " .
                                                  showsPrec 11 p1 .
                                                  showChar ' ' .
                                                  showsPrec 11 p2)
  showsPrec p (ProbeLe p1 p2) = showParen (p>10) (showString "ProbeLe " .
                                                  showsPrec 11 p1 .
                                                  showChar ' ' .
                                                  showsPrec 11 p2)
  showsPrec p (ProbeLt p1 p2) = showParen (p>10) (showString "ProbeLt " .
                                                  showsPrec 11 p1 .
                                                  showChar ' ' .
                                                  showsPrec 11 p2)
  showsPrec _ IsPB = showString "IsPB"
  showsPrec _ ArithMaxDeg = showString "ArithMaxDeg"
  showsPrec _ ArithAvgDeg = showString "ArithAvgDeg"
  showsPrec _ ArithMaxBW = showString "ArithMaxBW"
  showsPrec _ ArithAvgBW = showString "ArithAvgBW"
  showsPrec _ IsQFLIA = showString "IsQFLIA"
  showsPrec _ IsQFLRA = showString "IsQFLRA"
  showsPrec _ IsQFLIRA = showString "IsQFLIRA"
  showsPrec _ IsILP = showString "IsILP"
  showsPrec _ IsQFNIA = showString "IsQFNIA"
  showsPrec _ IsQFNRA = showString "IsQFNRA"
  showsPrec _ IsNIA = showString "IsNIA"
  showsPrec _ IsNRA = showString "IsNRA"
  showsPrec _ IsUnbounded = showString "IsUnbounded"
  showsPrec _ Memory = showString "Memory"
  showsPrec _ Depth = showString "Depth"
  showsPrec _ Size = showString "Size"
  showsPrec _ NumExprs = showString "NumExprs"
  showsPrec _ NumConsts = showString "NumConsts"
  showsPrec _ NumBoolConsts = showString "NumBoolConsts"
  showsPrec _ NumArithConsts = showString "NumArithConsts"
  showsPrec _ NumBVConsts = showString "NumBVConsts"
  showsPrec _ ProduceProofs = showString "ProduceProofs"
  showsPrec _ ProduceModel = showString "ProduceModel"
  showsPrec _ ProduceUnsatCores = showString "ProduceUnsatCores"
  showsPrec _ HasPatterns = showString "HasPatterns"
  showsPrec _ IsPropositional = showString "IsPropositional"
  showsPrec _ IsQFBV = showString "IsQFBV"
  showsPrec _ IsQFBVEQ = showString "IsQFBVEQ"
