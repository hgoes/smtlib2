module Language.SMTLib2.Internals.Value where

import Language.SMTLib2.Internals.Type

import Data.Ratio
import GHC.TypeLits

data Constr (arg :: List Type) a
  = Constr { conName :: String
           , conFields :: Args (Field a) arg
           , construct :: Args Value arg -> a
           , conTest :: a -> Bool }

data Field a (t :: Type) = Field { fieldName :: String
                                 , fieldGet :: a -> Value t }

data Value (a :: Type) where
  BoolValue :: Bool -> Value BoolType
  IntValue :: Integer -> Value IntType
  RealValue :: Rational -> Value RealType
  BitVecValue :: Integer -> Value (BitVecType n)

