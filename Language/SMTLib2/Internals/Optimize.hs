module Language.SMTLib2.Internals.Optimize (optimizeBackend,optimizeExpr) where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances ()
import Data.Proxy
import Data.Bits

optimizeBackend :: b -> OptimizeBackend b
optimizeBackend = OptB

data OptimizeBackend b = OptB b

instance SMTBackend b m => SMTBackend (OptimizeBackend b) m where
  smtSetLogic (OptB b) = smtSetLogic b
  smtGetInfo (OptB b) = smtGetInfo b
  smtSetOption (OptB b) = smtSetOption b
  smtAssert (OptB b) expr grp = let nexpr = case optimizeExpr expr of
                                      Just e -> e
                                      Nothing -> expr
                                in case nexpr of
                                  Const True _ -> return ()
                                  _ -> smtAssert b nexpr grp
  smtCheckSat (OptB b) = smtCheckSat b
  smtDeclareDataTypes (OptB b) = smtDeclareDataTypes b
  smtDeclareSort (OptB b) = smtDeclareSort b
  smtPush (OptB b) = smtPush b
  smtPop (OptB b) = smtPop b
  smtDefineFun (OptB b) name args body = let nbody = case optimizeExpr body of
                                               Just e -> e
                                               Nothing -> body
                                         in smtDefineFun b name args nbody
  smtDeclareFun (OptB b) = smtDeclareFun b
  smtGetValue (OptB b) mp dts expr = let nexpr = case optimizeExpr expr of
                                           Just e -> e
                                           Nothing -> expr
                                     in smtGetValue b mp dts nexpr
  smtGetProof (OptB b) mp dts = do
    res <- smtGetProof b mp dts
    case optimizeExpr res of
      Just e -> return e
      Nothing -> return res
  smtGetUnsatCore (OptB b) = smtGetUnsatCore b
  smtSimplify (OptB b) mp dts expr = do
    let nexpr = case optimizeExpr expr of
          Just e -> e
          Nothing -> expr
    simp <- smtSimplify b mp dts nexpr
    case optimizeExpr simp of
      Nothing -> return simp
      Just simp' -> return simp'
  smtGetInterpolant (OptB b) mp dts grps = do
    inter <- smtGetInterpolant b mp dts grps
    case optimizeExpr inter of
      Nothing -> return inter
      Just e -> return e
  smtComment (OptB b) = smtComment b
  smtExit (OptB b) = smtExit b

optimizeExpr :: SMTExpr t -> Maybe (SMTExpr t)
optimizeExpr (App fun x) = let (opt,x') = foldExprs (\opt expr ann -> case optimizeExpr expr of
                                                        Nothing -> (opt,expr)
                                                        Just expr' -> (True,expr')
                                                    ) False x (extractArgAnnotation x)
                           in case optimizeCall fun x' of
                             Nothing -> if opt
                                        then Just $ App fun x'
                                        else Nothing
                             Just res -> Just res

optimizeExpr _ = Nothing

optimizeCall :: SMTFunction arg res -> arg -> Maybe (SMTExpr res)
optimizeCall SMTEq [] = Just (Const True ())
optimizeCall SMTEq [_] = Just (Const True ())
optimizeCall SMTEq [x,y] = case eqExpr 0 x y of
  Nothing -> Nothing
  Just res -> Just (Const res ())
optimizeCall (SMTLogic _) [x] = Just x
optimizeCall (SMTLogic And) xs = case removeConstsOf False xs of
  Just _ -> Just $ Const False ()
  Nothing -> case removeConstsOf True xs of
    Nothing -> case xs of
      [] -> Just $ Const True ()
      _ -> Nothing
    Just [] -> Just $ Const True ()
    Just [x] -> Just x
    Just xs' -> Just $ App (SMTLogic And) xs'
optimizeCall (SMTLogic Or) xs = case removeConstsOf True xs of
  Just _ -> Just $ Const True ()
  Nothing -> case removeConstsOf False xs of
    Nothing -> case xs of
      [] -> Just $ Const False ()
      _ -> Nothing
    Just [] -> Just $ Const False ()
    Just [x] -> Just x
    Just xs' -> Just $ App (SMTLogic Or) xs'
optimizeCall (SMTLogic XOr) [] = Just $ Const False ()
optimizeCall (SMTLogic Implies) [] = Just $ Const True ()
optimizeCall (SMTLogic Implies) xs
  = let (args,res) = splitLast xs
    in case res of
      Const True _ -> Just (Const True ())
      _ -> case removeConstsOf False args of
        Just _ -> Just $ Const True ()
        Nothing -> case removeConstsOf True args of
          Nothing -> case args of
            [] -> Just res
            _ -> Nothing
          Just [] -> Just res
          Just args' -> Just $ App (SMTLogic Implies) (args'++[res])
optimizeCall SMTITE (Const True _,ifT,_) = Just ifT
optimizeCall SMTITE (Const False _,_,ifF) = Just ifF
optimizeCall SMTITE (_,ifT,ifF) = case eqExpr 0 ifT ifF of
  Just True -> Just ifT
  _ -> Nothing
optimizeCall (SMTBVBin op) args = bvBinOpOptimize op args
optimizeCall SMTConcat (Const (BitVector v1::BitVector b1) ann1,Const (BitVector v2::BitVector b2) ann2)
  = Just (Const (BitVector $ (v1 `shiftL` (fromInteger $ getBVSize (Proxy::Proxy b2) ann2)) .|. v2) (concatAnnotation (undefined::b1) (undefined::b2) ann1 ann2))
optimizeCall _ _ = Nothing

removeConstsOf :: Bool -> [SMTExpr Bool] -> Maybe [SMTExpr Bool]
removeConstsOf val = removeItems (\e -> case e of
                                     Const c _ -> c==val
                                     _ -> False)

removeItems :: (a -> Bool) -> [a] -> Maybe [a]
removeItems f [] = Nothing
removeItems f (x:xs) = if f x
                       then (case removeItems f xs of
                                Nothing -> Just xs
                                Just xs' -> Just xs')
                       else (case removeItems f xs of
                                Nothing -> Nothing
                                Just xs' -> Just (x:xs'))

splitLast :: [a] -> ([a],a)
splitLast [x] = ([],x)
splitLast (x:xs) = let (xs',last) = splitLast xs
                   in (x:xs',last)

bvBinOpOptimize :: SMTBVBinOp -> (SMTExpr (BitVector a),SMTExpr (BitVector a)) -> Maybe (SMTExpr (BitVector a))
bvBinOpOptimize BVAdd (Const (BitVector 0) _,y) = Just y
bvBinOpOptimize BVAdd (x,Const (BitVector 0) _) = Just x
bvBinOpOptimize BVAdd (Const (BitVector x) w,Const (BitVector y) _) = Just (Const (BitVector $ x+y) w)
bvBinOpOptimize _ _ = Nothing
