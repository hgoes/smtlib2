module Language.SMTLib2.Composite
  (Composite(..),
   CompositeExtract(..),
   -- * Expressions
   CompositeExpr(..),
   createRevComp,
   concretizeExpr,
   relativizeExpr,
   collectRevVars,
   -- * Instances
   -- ** Nullary
   NoComp(..),
   NoRev,
   -- ** Singleton
   Comp(..),
   -- ** Tuple
   CompTuple2(..),
   CompTuple3(..),
   RevTuple2(..),
   RevTuple3(..),
   -- ** Maybe
   CompMaybe(..),
   -- ** Either
   CompEither(..),
   RevEither(..),
   -- ** List
   CompList(..),
   RevList(..),
   -- ** Map
   CompMap(..),
   RevMap(..),
   -- ** Array
   CompArray(..),
   RevArray(..),
   selectArray,storeArray,
   -- ** Data-structures
   makeComposite
  ) where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Expression
import Language.SMTLib2.Composite.Null
import Language.SMTLib2.Composite.Singleton
import Language.SMTLib2.Composite.Tuple
import Language.SMTLib2.Composite.Maybe
import Language.SMTLib2.Composite.Either
import Language.SMTLib2.Composite.List
import Language.SMTLib2.Composite.Map
import Language.SMTLib2.Composite.Array
import Language.SMTLib2.Composite.Data
import Language.SMTLib2.Composite.Convert
import Language.SMTLib2.Composite.Convert.Instances

import Language.SMTLib2 hiding (select,store)

extract :: (Backend b,CompositeExtract c) => c (Expr b) -> SMT b (CompExtract c)
extract = compExtract getValue
