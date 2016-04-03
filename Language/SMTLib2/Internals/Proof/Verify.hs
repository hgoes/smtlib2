module Language.SMTLib2.Internals.Proof.Verify where

import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Proof
import Language.SMTLib2
import qualified Language.SMTLib2.Internals.Expression as E

import Data.GADT.Compare
import Data.GADT.Show
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map

verifyZ3Proof :: B.Backend b => B.Proof b -> SMT b ()
verifyZ3Proof pr = do
  res <- runExceptT (evalStateT (verifyProof analyzeProof (\name args res -> do
                                                              b <- gets backend
                                                              verifyZ3Rule (BackendInfo b) name args res) pr) Map.empty)
  case res of
    Right _ -> return ()
    Left err -> error $ "Error in proof: "++err

verifyZ3Rule :: (GetType e,Extract i e,GEq e,Monad m,GShow e)
             => i -> String -> [ProofResult e] -> ProofResult e -> ExceptT String m ()
verifyZ3Rule _ "asserted" [] q = return ()
verifyZ3Rule i "mp" [p,impl] q = case p of
  ProofExpr p' -> case q of
    ProofExpr q' -> case impl of
      ProofExpr (extract i -> Just (Implies (rp ::: rq ::: Nil)))
        -> case geq p' rp of
        Just Refl -> case geq q' rq of
          Just Refl -> return ()
          Nothing -> throwError "right hand side of implication doesn't match result"
        Nothing -> throwError "left hand side of implication doesn't match argument"
      ProofExpr (extract i -> Just (Eq (rp ::: rq ::: Nil)))
        -> case geq p' rp of
        Just Refl -> case geq q' rq of
          Just Refl -> return ()
          Nothing -> throwError "right hand side of implication doesn't match result"
        Nothing -> throwError "left hand side of implication doesn't match argument"
      _ -> throwError "second argument isn't an implication"
    _ -> throwError "result type can't be equisatisfiable equality"
  _ -> throwError "first argument can't be equisatisfiable equality"
verifyZ3Rule i "reflexivity" [] res = case res of
  EquivSat e1 e2 -> case geq e1 e2 of
    Just Refl -> return ()
    Nothing -> throwError "arguments must be the same"
  ProofExpr (extract i -> Just (Eq (x ::: y ::: Nil)))
    -> case geq x y of
    Just Refl -> return ()
    Nothing -> throwError "arguments must be the same"
  _ -> throwError "result must be equality"
verifyZ3Rule i "symmetry" [rel] res = case rel of
  EquivSat x y -> case res of
    EquivSat y' x' -> case geq x x' of
      Just Refl -> case geq y y' of
        Just Refl -> return ()
        Nothing -> throwError "argument mismatch"
      Nothing -> throwError "argument mismatch"
    _ -> throwError "argument mismatch"
  ProofExpr (extract i -> Just (E.App r1 (x ::: y ::: Nil)))
    -> case res of
    ProofExpr (extract i -> Just (E.App r2 (ry ::: rx ::: Nil)))
      -> case geq x rx of
      Just Refl -> case geq y ry of
        Just Refl -> case geq r1 r2 of
          Just Refl -> case r1 of
            E.Eq _ _ -> return ()
            E.Logic E.And _ -> return ()
            E.Logic E.Or _ -> return ()
            E.Logic E.XOr _ -> return ()
            _ -> throwError "relation is not symmetric"
          _ -> throwError "result must be the same relation"
        _ -> throwError "argument mismatch"
      _ -> throwError "argument mismatch"
    _ -> throwError "result must be a relation"
  _ -> throwError "argument must be a relation"
--verifyZ3Rule i "transitivity"
verifyZ3Rule i name args res = error $ "Cannot verify rule "++show name++" "++show args++" => "++show res

