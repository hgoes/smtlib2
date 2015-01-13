module Language.SMTLib2.Timing
       (TimingBackend()
       ,timingBackend)
       where

import Language.SMTLib2.Internals
import Data.Time.Clock
import Control.Monad.Trans

timingBackend :: (NominalDiffTime -> m ()) -> b -> TimingBackend b m
timingBackend act b = TimingBackend { timingBackend' = b
                                    , reportTime = act }

data TimingBackend b m = TimingBackend { timingBackend' :: b
                                       , reportTime :: NominalDiffTime -> m ()
                                       }

instance (SMTBackend b m,MonadIO m) => SMTBackend (TimingBackend b m) m where
  smtGetNames b = smtGetNames (timingBackend' b)
  smtNextName b = smtNextName (timingBackend' b)
  smtHandle b req = do
    timeBefore <- liftIO getCurrentTime
    (resp,nb) <- smtHandle (timingBackend' b) req
    timeAfter <- liftIO getCurrentTime
    reportTime b (diffUTCTime timeAfter timeBefore)
    return (resp,b { timingBackend' = nb })
