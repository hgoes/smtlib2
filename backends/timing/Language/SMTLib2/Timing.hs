module Language.SMTLib2.Timing
       (TimingBackend()
       ,timingBackend)
       where

import Language.SMTLib2.Internals.Backend
import Data.Time.Clock
import Control.Monad.Trans

timingBackend :: (Backend b,MonadIO (SMTMonad b))
              => (NominalDiffTime -> SMTMonad b ())
              -> b -> TimingBackend b
timingBackend act b = TimingBackend { timingBackend' = b
                                    , reportTime = act }

data TimingBackend b = MonadIO (SMTMonad b) => TimingBackend { timingBackend' :: b
                                                             , reportTime :: NominalDiffTime -> SMTMonad b ()
                                                             }

withTiming :: SMTAction b r
           -> SMTAction (TimingBackend b) r
withTiming act (TimingBackend b rep) = do
  timeBefore <- liftIO getCurrentTime
  (res,nb) <- act b
  timeAfter <- liftIO getCurrentTime
  rep (diffUTCTime timeAfter timeBefore)
  return (res,TimingBackend nb rep)

instance (Backend b) => Backend (TimingBackend b) where
  type SMTMonad (TimingBackend b) = SMTMonad b
  type Expr (TimingBackend b) = Expr b
  type Var (TimingBackend b) = Var b
  type QVar (TimingBackend b) = QVar b
  type Fun (TimingBackend b) = Fun b
  type Constr (TimingBackend b) = Constr b
  type Field (TimingBackend b) = Field b
  type FunArg (TimingBackend b) = FunArg b
  type LVar (TimingBackend b) = LVar b
  type ClauseId (TimingBackend b) = ClauseId b
  type Model (TimingBackend b) = Model b
  setOption = withTiming . setOption
  getInfo = withTiming . getInfo
  comment = withTiming . comment
  push = withTiming push
  pop = withTiming pop
  declareVar = withTiming . declareVar
  createQVar = withTiming . createQVar
  createFunArg = withTiming . createFunArg
  defineVar name expr = withTiming (defineVar name expr)
  defineFun name args body = withTiming (defineFun name args body)
  declareFun = withTiming . declareFun
  assert = withTiming . assert
  assertId = withTiming . assertId
  assertPartition expr part = withTiming (assertPartition expr part)
  checkSat tact limit = withTiming (checkSat tact limit)
  getUnsatCore = withTiming getUnsatCore
  getValue = withTiming . getValue
  getModel = withTiming getModel
  getProof = withTiming getProof
  simplify = withTiming . simplify
  toBackend = withTiming . toBackend
  fromBackend b = fromBackend (timingBackend' b)
  declareDatatypes = withTiming . declareDatatypes
  interpolate = withTiming interpolate
  exit = withTiming exit
  
