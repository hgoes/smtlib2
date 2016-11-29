module Language.SMTLib2.Pipe
       (SMTPipe(),
        createPipe,
        createPipeFromHandle,
        withPipe
       ) where

import Language.SMTLib2.Pipe.Internals
import Language.SMTLib2 (SMT,withBackendExitCleanly)

withPipe :: String -> [String] -> SMT SMTPipe a -> IO a
withPipe solver args act
  = withBackendExitCleanly (createPipe solver args) act
