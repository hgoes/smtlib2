module Language.SMTLib2.Internals.Type where

import GHC.TypeLits

data List a = Nil | Cons a (List a)

data Type = BoolType
          | IntType
          | RealType
          | BitVecType Nat
          | ArrayType (List Type) Type
          | forall a. DataType a

data Args (e :: Type -> *) (a :: List Type) where
  NoArg :: Args e Nil
  Arg :: e t -> Args e ts -> Args e (Cons t ts)
