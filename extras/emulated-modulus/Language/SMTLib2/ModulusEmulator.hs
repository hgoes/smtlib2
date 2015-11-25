module Language.SMTLib2.ModulusEmulator
       (ModulusEmulator(),
        modulusEmulator,
        emulationAssertions) where

import Language.SMTLib2.Internals.Backend
import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Type hiding (Constr,Field)

import Data.Foldable
import Data.Typeable (gcast)
import Data.GADT.Compare

data ModulusEmulator b = ModulusEmulator { emulatedBackend :: b
                                         , emulations :: [Emulation b]
                                         , addAssertions :: Maybe [Emulation b]
                                         }

data Emulation b = EmulatedMod { modulusResultVar :: Var b IntType
                               , modulusResult :: Expr b IntType
                               , modulus :: Integer
                               , modulusConst :: Expr b IntType
                               , modulusExpr :: Expr b IntType }
               | EmulatedDiv { divResult :: Var b IntType
                             , divExpr :: Expr b IntType
                             , divisor :: Expr b IntType
                             , divDiff :: Var b IntType }

modulusEmulator :: Bool -> b -> ModulusEmulator b
modulusEmulator addAssert b = ModulusEmulator { emulatedBackend = b
                                              , emulations = []
                                              , addAssertions = if addAssert then Just [] else Nothing }

toAsserts :: Backend b => [Emulation b] -> SMTAction b [Expr b BoolType]
toAsserts [] b = return ([],b)
toAsserts (x:xs) b = do
  (x',b1) <- toAssert x b
  (xs',b2) <- toAsserts xs b1
  return (x'++xs',b2)

emulationAssertions :: Backend b => ModulusEmulator b -> SMTAction b [Expr b BoolType]
emulationAssertions me = toAsserts (emulations me)

toAssert :: Backend b => Emulation b -> SMTAction b [Expr b BoolType]
toAssert (EmulatedMod res resVar mod modE expr) b = do
  (diff,b1) <- toBackend (App (ArithInt Minus) (Arg expr (Arg resVar NoArg))) b
  (div,b2) <- toBackend (App (Divisible mod) (Arg diff NoArg)) b1
  (c0,b3) <- toBackend (Const (IntValue 0)) b2
  (lt,b4) <- toBackend (App (OrdInt Lt) (Arg resVar (Arg modE NoArg))) b3
  (ge,b5) <- toBackend (App (OrdInt Ge) (Arg resVar (Arg c0 NoArg))) b4
  return ([div,lt,ge],b5)
toAssert (EmulatedDiv res expr div diff) b = do
  (resVar,b1) <- toBackend (Var res) b
  (diffVar,b2) <- toBackend (Var diff) b1
  (prod,b3) <- toBackend (App (ArithInt Mult) (Arg resVar (Arg div NoArg))) b2
  (diff',b4) <- toBackend (App (ArithInt Minus) (Arg expr (Arg diffVar NoArg))) b3
  (eq,b5) <- toBackend (App Eq (Arg prod (Arg diff' NoArg))) b4
  (c0,b6) <- toBackend (Const (IntValue 0)) b5
  (ge,b7) <- toBackend (App (OrdInt Ge) (Arg diffVar (Arg c0 NoArg))) b6
  (lt,b8) <- toBackend (App (OrdInt Lt) (Arg diffVar (Arg div NoArg))) b7
  return ([eq,ge,lt],b8)

addEmulation :: Emulation b -> ModulusEmulator b -> ModulusEmulator b
addEmulation emul b
  = b2
  where
    b1 = case addAssertions b of
      Nothing -> b
      Just stack -> b { addAssertions = Just $ emul:stack }
    b2 = b1 { emulations = emul:emulations b1 }

flushAssertions :: Backend b => Maybe Partition -> ModulusEmulator b
                -> SMTMonad b (ModulusEmulator b)
flushAssertions interp me = case addAssertions me of
  Nothing -> return me
  Just [] -> return me
  Just stack -> do
    (ass,b1) <- toAsserts stack (emulatedBackend me)
    b2 <- foldlM (\cb e -> fmap snd $ case interp of
                   Nothing -> assert e cb
                   Just p -> assertPartition e p cb
                 ) b1 ass
    return (me { emulatedBackend = b2
               , addAssertions = Just [] })

instance (Backend b) => Backend (ModulusEmulator b) where
  type SMTMonad (ModulusEmulator b) = SMTMonad b
  type Expr (ModulusEmulator b) = Expr b
  type Var (ModulusEmulator b) = Var b
  type QVar (ModulusEmulator b) = QVar b
  type Fun (ModulusEmulator b) = Fun b
  type Constr (ModulusEmulator b) = Constr b
  type Field (ModulusEmulator b) = Field b
  type FunArg (ModulusEmulator b) = FunArg b
  type ClauseId (ModulusEmulator b) = ClauseId b
  type Model (ModulusEmulator b) = Model b
  setOption opt = liftSMT (setOption opt)
  getInfo info = liftSMT (getInfo info)
  comment str = liftSMT (comment str)
  push = liftSMT push
  pop = liftSMT pop
  declareVar name = liftSMT (declareVar name)
  createQVar name = liftSMT (createQVar name)
  createFunArg name = liftSMT (createFunArg name)
  defineVar name body = liftSMT (defineVar name body)
  declareFun name = liftSMT (declareFun name)
  defineFun name args body = liftSMT (defineFun name args body)
  assert expr me = do
    ((),me1) <- liftSMT (assert expr) me
    me2 <- flushAssertions Nothing me1
    return ((),me2)
  assertId expr me = do
    (cl,me1) <- liftSMT (assertId expr) me
    me2 <- flushAssertions Nothing me1
    return (cl,me2)
  assertPartition expr p me = do
    ((),me1) <- liftSMT (assertPartition expr p) me
    me2 <- flushAssertions (Just p) me1
    return ((),me2)
  checkSat tactic limits = liftSMT (checkSat tactic limits)
  getUnsatCore = liftSMT getUnsatCore
  getValue e = liftSMT (getValue e)
  getModel = liftSMT getModel
  modelEvaluate mdl e = liftSMT (modelEvaluate mdl e)
  getProof = liftSMT getProof
  simplify e = liftSMT (simplify e)
  toBackend (App (ArithIntBin Mod) (Arg x (Arg y NoArg))) me
    = case fromBackend (emulatedBackend me) y of
    Const (IntValue y') -> do
      (resVar,b1) <- declareVar Nothing (emulatedBackend me)
      (resE,b2) <- toBackend (Var resVar) b1
      (res,b3) <- if y'>=0
                  then return (resE,b2)
                  else toBackend (App (ArithInt Minus) (Arg resE NoArg)) b2
      return (res,addEmulation (EmulatedMod resVar resE y' y x)
                  (me { emulatedBackend = b3 }))
  toBackend (App (ArithIntBin Rem) (Arg x (Arg y NoArg))) me
    = case fromBackend (emulatedBackend me) y of
    Const (IntValue y') -> do
      (resVar,b1) <- declareVar Nothing (emulatedBackend me)
      (resE,b2) <- toBackend (Var resVar) b1
      return (resE,addEmulation (EmulatedMod resVar resE y' y x)
                   (me { emulatedBackend = b2 }))
  toBackend (App (ArithIntBin Div) (Arg x (Arg y NoArg))) me = do
    (resVar,b1) <- declareVar Nothing (emulatedBackend me)
    (diffVar,b2) <- declareVar Nothing b1
    (resE,b3) <- toBackend (Var resVar) b2
    return (resE,addEmulation (EmulatedDiv resVar x y diffVar)
                 (me { emulatedBackend = b3 }))
  toBackend e me = liftSMT (toBackend e) me
  fromBackend me e = case fromBackend (emulatedBackend me) e of
    Var v -> case [ (modE,expr,refl) | EmulatedMod res resE mod modE expr <- emulations me
                                    , Just refl <- [geq v res] ] of
             (cmod,expr,Refl):_ -> App (ArithIntBin Mod) (Arg expr (Arg cmod NoArg))
             [] -> case [ (expr,div,diff,refl) | EmulatedDiv res expr div diff <- emulations me
                                               , Just refl <- [geq v res] ] of
                   (expr,div,diff,Refl):_ -> App (ArithIntBin Div) (Arg expr (Arg div NoArg))
                   [] -> case [ (res,expr,div,refl)
                              | EmulatedDiv res expr div diff <- emulations me
                              , Just refl <- [geq v diff] ] of
                     (res,expr,div,Refl):_ -> App (ArithIntBin Mod) (Arg expr (Arg div NoArg))
                     [] -> Var v
    res -> res
  declareDatatypes tps = liftSMT (declareDatatypes tps)
  interpolate = liftSMT interpolate
  exit = liftSMT exit
  
liftSMT :: Backend b => SMTAction b r -> SMTAction (ModulusEmulator b) r
liftSMT act me = do
  (res,nb) <- act (emulatedBackend me)
  return (res,me { emulatedBackend = nb })
