module Language.SMTLib2.Composite.Convert.Instances () where

import Language.SMTLib2 hiding (store)
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains
import Language.SMTLib2.Composite.Convert
import Language.SMTLib2.Composite.Array.Static
import Language.SMTLib2.Composite.Array
import Language.SMTLib2.Composite.Singleton
import Language.SMTLib2.Composite.Null
import Language.SMTLib2.Composite.Either
import Language.SMTLib2.Composite.Choice

import Data.Foldable
import qualified Data.Map as Map

-- Static to dynamic array:

instance Composite el => Convert (StaticArray idx el) (CompArray idx el) where
  convert (StaticArray idx def mp) = do
    arr0 <- mapExprs (\e -> do
                         ne <- constArray idx e
                         return $ Arrayed ne
                     ) def
    foldlM (\arr (val,el) -> case arr of
               Nothing -> return Nothing
               Just rarr -> do
                 entr <- List.mapM constant val
                 storeArray rarr entr el
           ) (Just $ CompArray idx arr0) (Map.toList mp)

-- Constant to dynamic:

instance (Composite c,Ord (c Value),Show (c Value)) => Convert (NoComp (c Value)) c where
  convert (NoComp val) = do
    res <- mapExprs constant val
    return (Just res)

-- Either:

instance (Convert from1 to1,Convert from2 to2) => Convert (CompEither from1 from2) (CompEither to1 to2) where
  convert (CompEither (Left x)) = do
    nx <- convert x
    return $ fmap (CompEither . Left) nx
  convert (CompEither (Right x)) = do
    nx <- convert x
    return $ fmap (CompEither . Right) nx
