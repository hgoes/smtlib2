module Language.SMTLib2.Internals.Proof where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.List (List(..))
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Expression

import Data.GADT.Compare
import Data.GADT.Show
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

data ProofResult (e :: Type -> *)
  = ProofExpr (e BoolType)
  | EquivSat (e BoolType) (e BoolType)

data Proof r (e :: Type -> *) p = Rule r [p] (ProofResult e)

verifyProof :: (Monad m,Ord p,Show r,Show p)
            => (p -> m (Proof r e p))
            -> (r -> [ProofResult e] -> ProofResult e -> ExceptT String m ())
            -> p
            -> StateT (Map p (ProofResult e)) (ExceptT String m) (ProofResult e)
verifyProof f v p = do
  computed <- gets (Map.lookup p)
  case computed of
    Just res -> return res
    Nothing -> do
      proof <- lift $ lift $ f p
      case proof of
        Rule r ante res -> do
          ante' <- mapM (verifyProof f v) ante
          lift $ withExceptT (\e -> "In rule "++show r++show ante++": "++e) $ v r ante' res
          modify $ Map.insert p res
          return res

renderProof :: (Monad m,Ord p,Show r)
            => (forall tp. e tp -> ShowS)
            -> (p -> m (Proof r e p))
            -> p
            -> m ShowS
renderProof renderE f p = do
  Endo res <- execWriterT (evalStateT (renderProof' renderE f p) Map.empty)
  return (showString "digraph proof {\n" . res . showString "}")

renderProof' :: (Monad m,Ord p,Show r)
            => (forall tp. e tp -> ShowS)
            -> (p -> m (Proof r e p))
            -> p
            -> StateT (Map p Int) (WriterT (Endo String) m) Int
renderProof' renderE f p = do
  rendered <- gets (Map.lookup p)
  case rendered of
    Just r -> return r
    Nothing -> do
      proof <- lift $ lift $ f p
      case proof of
        Rule r ante res -> do
          ident <- gets Map.size
          modify $ Map.insert p ident
          tell $ Endo $ showChar 'n' . shows ident . showString "_T[label=" . shows r . showString "];\n"
          tell $ Endo $ showChar 'n' . shows ident . showString "[label=\"" .
            renderProofResult renderE res . showString "\"];\n"
          tell $ Endo $ showChar 'n' . shows ident . showString "_T -> " . showChar 'n' . shows ident . showString ";\n"
          mapM_ (\pre -> do
                    preId <- renderProof' renderE f pre
                    tell $ Endo $ showChar 'n' . shows preId . showString " -> " . showChar 'n' . shows ident . showString "_T;\n"
                ) ante
          return ident

renderProofResult :: (forall tp. e tp -> ShowS) -> ProofResult e -> ShowS
renderProofResult f (ProofExpr e) = f e
renderProofResult f (EquivSat lhs rhs)
  = showString "(~ " . f lhs . showChar ' ' . f rhs . showChar ')'

instance GShow e => Show (ProofResult e) where
  showsPrec p (ProofExpr e) = gshowsPrec p e
  showsPrec p (EquivSat lhs rhs)
    = showString "(~ " . gshowsPrec 10 lhs . showChar ' ' . gshowsPrec 10 rhs . showChar ')'
