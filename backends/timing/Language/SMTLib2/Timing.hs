module Language.SMTLib2.Timing
       (TimingBackend()
       ,timingBackend)
       where

import Language.SMTLib2.Internals.Backend
import Language.SMTLib2.Internals.Type (GetType)
import Language.SMTLib2.Internals.Proof (mapProof)
import Language.SMTLib2.Internals.Expression (mapExpr)
import Data.Time.Clock
import Control.Monad.Trans
import Data.Typeable
import Data.GADT.Show
import Data.GADT.Compare
import Data.Functor.Identity

timingBackend :: (Backend b,MonadIO (SMTMonad b))
              => (NominalDiffTime -> SMTMonad b ())
              -> b -> TimingBackend b
timingBackend act b = TimingBackend { timingBackend' = b
                                    , reportTime = act }

data TimingBackend b = MonadIO (SMTMonad b) => TimingBackend { timingBackend' :: b
                                                             , reportTime :: NominalDiffTime -> SMTMonad b ()
                                                             } deriving Typeable

withTiming :: SMTAction b r
           -> SMTAction (TimingBackend b) r
withTiming act (TimingBackend b rep) = do
  timeBefore <- liftIO getCurrentTime
  (res,nb) <- act b
  timeAfter <- liftIO getCurrentTime
  rep (diffUTCTime timeAfter timeBefore)
  return (res,TimingBackend nb rep)

deriving instance Backend b => GShow (Expr (TimingBackend b))
deriving instance Backend b => GEq (Expr (TimingBackend b))
deriving instance Backend b => GCompare (Expr (TimingBackend b))
deriving instance Backend b => GetType (Expr (TimingBackend b))

instance Backend b => Backend (TimingBackend b) where
  type SMTMonad (TimingBackend b) = SMTMonad b
  newtype Expr (TimingBackend b) tp = TimingExpr (Expr b tp)
  type Var (TimingBackend b) = Var b
  type QVar (TimingBackend b) = QVar b
  type Fun (TimingBackend b) = Fun b
  type FunArg (TimingBackend b) = FunArg b
  type LVar (TimingBackend b) = LVar b
  type ClauseId (TimingBackend b) = ClauseId b
  type Model (TimingBackend b) = Model b
  type Proof (TimingBackend b) = Proof b
  setOption = withTiming . setOption
  getInfo = withTiming . getInfo
  comment = withTiming . comment
  push = withTiming push
  pop = withTiming pop
  declareVar tp = withTiming . declareVar tp
  createQVar tp = withTiming . createQVar tp
  createFunArg tp = withTiming . createFunArg tp
  defineVar name (TimingExpr expr) = withTiming (defineVar name expr)
  defineFun name args (TimingExpr body) = withTiming (defineFun name args body)
  declareFun arg tp = withTiming . declareFun arg tp
  assert (TimingExpr e) = withTiming (assert e)
  assertId (TimingExpr e) = withTiming (assertId e)
  assertPartition (TimingExpr expr) part = withTiming (assertPartition expr part)
  checkSat tact limit = withTiming (checkSat tact limit)
  getUnsatCore = withTiming getUnsatCore
  getValue (TimingExpr e) = withTiming (getValue e)
  getModel = withTiming getModel
  modelEvaluate mdl (TimingExpr e) = withTiming (modelEvaluate mdl e)
  getProof = withTiming getProof
  analyzeProof b = mapProof TimingExpr . analyzeProof (timingBackend' b)
  simplify (TimingExpr e) = mapAction TimingExpr $ withTiming (simplify e)
  toBackend e = mapAction TimingExpr $ withTiming
                (toBackend $ runIdentity $ mapExpr return return return return return (\(TimingExpr e) -> return e) e)
  fromBackend b (TimingExpr e) = runIdentity $ mapExpr return return return return return (return . TimingExpr) $
                                 fromBackend (timingBackend' b) e
  declareDatatypes = withTiming . declareDatatypes
  interpolate = mapAction TimingExpr $ withTiming interpolate
  exit = withTiming exit
  builtIn name arg ret = withTiming (builtIn name arg ret)
