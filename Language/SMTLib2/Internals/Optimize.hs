module Language.SMTLib2.Internals.Optimize (optimizeBackend,optimizeExpr) where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances (bvSigned,bvUnsigned,bvRestrict)
import Language.SMTLib2.Internals.Operators
import Data.Proxy
import Data.Bits

optimizeBackend :: b -> OptimizeBackend b
optimizeBackend = OptB

data OptimizeBackend b = OptB b

instance SMTBackend b m => SMTBackend (OptimizeBackend b) m where
  smtHandle (OptB b) st (SMTAssert expr grp)
    = let nexpr = case optimizeExpr expr of
            Just e -> e
            Nothing -> expr
      in case nexpr of
        Const True _ -> return ()
        _ -> smtHandle b st (SMTAssert nexpr grp)
  smtHandle (OptB b) st (SMTDefineFun name args body)
    = let nbody = case optimizeExpr body of
            Just e -> e
            Nothing -> body
      in smtHandle b st (SMTDefineFun name args nbody)
  smtHandle (OptB b) st (SMTGetValue expr)
    = let nexpr = case optimizeExpr expr of
            Just e -> e
            Nothing -> expr
      in smtHandle b st (SMTGetValue nexpr)
  smtHandle (OptB b) st SMTGetProof = do
    res <- smtHandle b st SMTGetProof
    case optimizeExpr res of
      Just e -> return e
      Nothing -> return res
  smtHandle (OptB b) st (SMTSimplify expr) = do
    let nexpr = case optimizeExpr expr of
          Just e -> e
          Nothing -> expr
    simp <- smtHandle b st (SMTSimplify nexpr)
    case optimizeExpr simp of
      Nothing -> return simp
      Just simp' -> return simp'
  smtHandle (OptB b) st (SMTGetInterpolant grps) = do
    inter <- smtHandle b st (SMTGetInterpolant grps)
    case optimizeExpr inter of
      Nothing -> return inter
      Just e -> return e
  smtHandle (OptB b) st req = smtHandle b st req

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
optimizeCall SMTNot (Const x _) = Just $ Const (not x) ()
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
  = Just (Const (BitVector $ (v1 `shiftL` (fromInteger $ getBVSize (Proxy::Proxy b2) ann2)) .|. v2)
          (concatAnnotation (undefined::b1) (undefined::b2) ann1 ann2))
optimizeCall (SMTExtract pstart plen) (Const from@(BitVector v) ann)
  = let start = reflectNat pstart 0
        undefFrom :: BitVector from -> from
        undefFrom _ = undefined
        undefLen :: SMTExpr (BitVector len) -> len
        undefLen _ = undefined
        len = reflectNat plen 0
        res = Const (BitVector $ (v `shiftR` (fromInteger start)) .&. (1 `shiftL` (fromInteger $ reflectNat plen 0) - 1))
              (extractAnn (undefFrom from) (undefLen res) len ann)
    in Just res
optimizeCall (SMTBVComp op) args = bvCompOptimize op args
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

bvBinOpOptimize :: IsBitVector a => SMTBVBinOp -> (SMTExpr (BitVector a),SMTExpr (BitVector a)) -> Maybe (SMTExpr (BitVector a))
bvBinOpOptimize BVAdd (Const (BitVector 0) _,y) = Just y
bvBinOpOptimize BVAdd (x,Const (BitVector 0) _) = Just x
bvBinOpOptimize BVAdd (Const (BitVector x) w,Const (BitVector y) _) = Just (Const (bvRestrict (BitVector $ x+y) w) w)
bvBinOpOptimize BVAnd (Const (BitVector x) w,Const (BitVector y) _) = Just (Const (BitVector $ x .&. y) w)
bvBinOpOptimize BVOr (Const (BitVector x) w,Const (BitVector y) _) = Just (Const (BitVector $ x .|. y) w)
bvBinOpOptimize BVOr (Const (BitVector 0) _,oth) = Just oth
bvBinOpOptimize BVOr (oth,Const (BitVector 0) _) = Just oth
bvBinOpOptimize BVSHL (Const (BitVector x) w,Const (BitVector y) _)
  = Just (Const (bvRestrict (BitVector $ x `shiftL` (fromInteger y)) w) w)
bvBinOpOptimize BVSHL (Const (BitVector 0) w,_) = Just (Const (BitVector 0) w)
bvBinOpOptimize BVSHL (oth,Const (BitVector 0) w) = Just oth
bvBinOpOptimize _ _ = Nothing

bvCompOptimize :: IsBitVector a => SMTBVCompOp -> (SMTExpr (BitVector a),SMTExpr (BitVector a)) -> Maybe (SMTExpr Bool)
bvCompOptimize op (Const b1 ann1,Const b2 ann2)
  = Just $ Const (case op of
                     BVULE -> u1 <= u2
                     BVULT -> u1 < u2
                     BVUGE -> u1 >= u2
                     BVUGT -> u1 > u2
                     BVSLE -> s1 <= s2
                     BVSLT -> s1 < s2
                     BVSGE -> s1 >= s2
                     BVSGT -> s1 > s2) ()
  where
    u1 = bvUnsigned b1 ann1
    u2 = bvUnsigned b2 ann2
    s1 = bvSigned b1 ann1
    s2 = bvSigned b2 ann2
bvCompOptimize _ _ = Nothing
