{-# LANGUAGE RankNTypes,TypeFamilies,OverloadedStrings,GADTs,FlexibleContexts #-}
module Language.SMTLib2.Internals.Translation where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.SMTMonad
import Language.SMTLib2.Internals.Instances ()

import qualified Data.AttoLisp as L
import Data.Typeable
import Data.Text as T
import Data.Word
import Data.Array

import Data.Unit

instance L.ToLisp (SMTExpr t) where
  toLisp e = fst $ exprToLisp e 0

instance Show (SMTExpr t) where
  show x = show $ fst (exprToLisp x 0)

-- | After a successful 'checkSat' call, extract values from the generated model.
--   The 'ProduceModels' option must be enabled for this.
getValue :: SMTValue t => SMTExpr t -> SMT t
getValue expr = do
  let ann = case expr of
        Var _ a -> a
        Const _ a -> a
        _ -> error "Can't use getValue on complex expressions. Use getValue' instead."
  getValue' ann expr
  
getValue' :: SMTValue t => SMTAnnotation t -> SMTExpr t -> SMT t
getValue' ann expr = do
  res <- getRawValue expr
  rres <- unmangle res ann
  case rres of
    Nothing -> error $ "Couldn't unmangle "++show res
    Just r -> return r

getRawValue :: SMTType t => SMTExpr t -> SMT L.Lisp
getRawValue expr = do
  clearInput
  putRequest $ L.List [L.Symbol "get-value"
                      ,L.List [L.toLisp expr]]
  val <- parseResponse
  case val of
    L.List [L.List [_,res]] -> return res
    _ -> error $ "unknown response to get-value: "++show val

-- | Define a new function with a body
defFun :: (Args a,SMTType r,Unit (ArgAnnotation a),Unit (SMTAnnotation r)) => (a -> SMTExpr r) -> SMT (SMTExpr (SMTFun a r))
defFun = defFunAnn unit unit

-- | Define a new constant
defConst :: (SMTType r,Unit (SMTAnnotation r)) => SMTExpr r -> SMT (SMTExpr r)
defConst = defConstAnn unit

-- | Define a new constant with a type annotation.
defConstAnn :: (SMTType r) => SMTAnnotation r -> SMTExpr r -> SMT (SMTExpr r)
defConstAnn ann e = do
  f <- defFunAnn () ann (const e)
  return $ App f ()

-- | Define a new function with a body and custom type annotations for arguments and result.
defFunAnn :: (Args a,SMTType r) => ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT (SMTExpr (SMTFun a r))
defFunAnn ann_arg ann_res f = do
  (c,decl,mp) <- getSMT

  let name = T.pack $ "fun"++show c
      res = Fun name ann_arg ann_res
      
      (_,rtp) = getFunUndef res
      
      (au,tps,c1) = createArgs ann_arg (c+1)
      
      (expr',c2) = exprToLisp (f au) c1
  putSMT (c2,decl,mp)
  defineFun name tps (getSort rtp ann_res) expr'
  return res

-- | Extract all values of an array by giving the range of indices.
unmangleArray :: (LiftArgs i,Ix (Unpacked i),SMTValue v,Unit (SMTAnnotation (Unpacked i)),Unit (ArgAnnotation i)) => (Unpacked i,Unpacked i) -> SMTExpr (SMTArray i v) -> SMT (Array (Unpacked i) v)
unmangleArray b expr = mapM (\i -> do
                                v <- getValue (Select expr (liftArgs i unit))
                                return (i,v)
                            ) (range b) >>= return.array b

exprsToLisp :: [SMTExpr t] -> Integer -> ([L.Lisp],Integer)
exprsToLisp [] c = ([],c)
exprsToLisp (e:es) c = let (e',c') = exprToLisp e c
                           (es',c'') = exprsToLisp es c'
                       in (e':es',c'')

exprToLisp :: SMTExpr t -> Integer -> (L.Lisp,Integer)
exprToLisp (Var name _) c = (L.Symbol name,c)
exprToLisp (Const x ann) c = (mangle x ann,c)
exprToLisp (Eq l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "=",l',r'],c'')
exprToLisp (Distinct lst) c = let (lst',c') = exprsToLisp lst c
                              in (L.List $ [L.Symbol "distinct"] ++ lst',c')
exprToLisp (Plus lst) c = let (lst',c') = exprsToLisp lst c
                          in (L.List $ [L.Symbol "+"] ++ lst',c')
exprToLisp (Mult lst) c = let (lst',c') = exprsToLisp lst c
                          in (L.List $ [L.Symbol "*"] ++ lst',c')
exprToLisp (Minus l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "-",l',r'],c'')
exprToLisp (Div l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "div",l',r'],c'')
exprToLisp (Divide l r) c = let (l',c') = exprToLisp l c
                                (r',c'') = exprToLisp r c'
                            in (L.List [L.Symbol "/",l',r'],c'')
exprToLisp (Mod l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "mod",l',r'],c'')
exprToLisp (Neg e) c = let (e',c') = exprToLisp e c
                       in (L.List [L.Symbol "-",e'],c')
exprToLisp (ITE cond tt ff) c = let (cond',c') = exprToLisp cond c
                                    (tt',c'') = exprToLisp tt c'
                                    (ff',c''') = exprToLisp ff c''
                                in (L.List [L.Symbol "ite",cond',tt',ff'],c''')
exprToLisp (Ge l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol ">=",l',r'],c'')
exprToLisp (Gt l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol ">",l',r'],c'')
exprToLisp (Le l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "<=",l',r'],c'')
exprToLisp (Lt l r) c = let (l',c') = exprToLisp l c
                            (r',c'') = exprToLisp r c'
                        in (L.List [L.Symbol "<",l',r'],c'')
exprToLisp (And lst) c = let (lst',c') = exprsToLisp lst c
                         in (L.List $ [L.Symbol "and"] ++ lst',c')
exprToLisp (Or lst) c = let (lst',c') = exprsToLisp lst c
                        in (L.List $ [L.Symbol "or"] ++ lst',c')
exprToLisp (XOr l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "xor",l',r'],c'')
exprToLisp (Implies l r) c = let (l',c') = exprToLisp l c
                                 (r',c'') = exprToLisp r c'
                             in (L.List [L.Symbol "=>",l',r'],c'')
exprToLisp (Not expr) c = let (expr',c') = exprToLisp expr c
                          in (L.List [L.Symbol "not",expr'],c')
exprToLisp (Select arr idx) c = let (arr',c') = exprToLisp arr c
                                    (idx',c'') = unpackArgs (\e _ i -> exprToLisp e i) idx undefined c'
                                in (L.List (L.Symbol "select":arr':idx'),c'')
exprToLisp (Store arr idx val) c = let (arr',c1) = exprToLisp arr c
                                       (idx',c2) = unpackArgs (\e _ i -> exprToLisp e i) idx undefined c1
                                       (val',c3) = exprToLisp val c2
                                   in (L.List (L.Symbol "store":arr':idx'++[val']),c3)
exprToLisp (AsArray f) c = let (f',c') = exprToLisp f c
                           in (L.List [L.Symbol "_",L.Symbol "as-array",f'],c')
exprToLisp (BVAdd l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvadd",l',r'],c'')
exprToLisp (BVSub l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsub",l',r'],c'')
exprToLisp (BVMul l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvmul",l',r'],c'')
exprToLisp (BVUDiv l r) c = let (l',c') = exprToLisp l c
                                (r',c'') = exprToLisp r c'
                            in (L.List [L.Symbol "bvudiv",l',r'],c'')
exprToLisp (BVSDiv l r) c = let (l',c') = exprToLisp l c
                                (r',c'') = exprToLisp r c'
                            in (L.List [L.Symbol "bvsdiv",l',r'],c'')
exprToLisp (BVULE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvule",l',r'],c'')
exprToLisp (BVULT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvult",l',r'],c'')
exprToLisp (BVUGE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvuge",l',r'],c'')
exprToLisp (BVUGT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvugt",l',r'],c'')
exprToLisp (BVSLE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsle",l',r'],c'')
exprToLisp (BVSLT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvslt",l',r'],c'')
exprToLisp (BVSGE l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsge",l',r'],c'')
exprToLisp (BVSGT l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvsgt",l',r'],c'')
exprToLisp (BVSHL l r) c = let (l',c') = exprToLisp l c
                               (r',c'') = exprToLisp r c'
                           in (L.List [L.Symbol "bvshl",l',r'],c'')
exprToLisp (BVExtract i j _ v) c = let (v',c') = exprToLisp v c
                                   in (L.List [L.List [L.Symbol "_"
                                                      ,L.Symbol "extract"
                                                      ,L.toLisp i
                                                      ,L.toLisp j]
                                              ,v'],c')
exprToLisp (BVConcat v1 v2) c = let (v1',c') = exprToLisp v1 c
                                    (v2',c'') = exprToLisp v2 c'
                                in (L.List [L.Symbol "concat"
                                           ,v1'
                                           ,v2'],c'')
exprToLisp (BVConcats v) c = let (v',c') = exprsToLisp v c
                             in (Prelude.foldl1 (\cur nxt -> L.List [L.Symbol "concat",cur,nxt]) v',c')
exprToLisp (BVXor v1 v2) c = let (v1',c') = exprToLisp v1 c
                                 (v2',c'') = exprToLisp v2 c'
                             in (L.List [L.Symbol "bvxor"
                                        ,v1'
                                        ,v2'],c'')
exprToLisp (BVAnd v1 v2) c = let (v1',c') = exprToLisp v1 c
                                 (v2',c'') = exprToLisp v2 c'
                             in (L.List [L.Symbol "bvand"
                                        ,v1'
                                        ,v2'],c'')
exprToLisp (BVOr v1 v2) c = let (v1',c') = exprToLisp v1 c
                                (v2',c'') = exprToLisp v2 c'
                            in (L.List [L.Symbol "bvor"
                                       ,v1'
                                       ,v2'],c'')
exprToLisp (BVURem v1 v2) c = let (v1',c') = exprToLisp v1 c
                                  (v2',c'') = exprToLisp v2 c'
                              in (L.List [L.Symbol "bvurem"
                                         ,v1'
                                         ,v2'],c'')
exprToLisp (BVSRem v1 v2) c = let (v1',c') = exprToLisp v1 c
                                  (v2',c'') = exprToLisp v2 c'
                              in (L.List [L.Symbol "bvsrem"
                                         ,v1'
                                         ,v2'],c'')
exprToLisp (Forall ann f) c = let (arg,tps,nc) = createArgs ann c
                                  (arg',nc') = exprToLisp (f arg) nc
                              in (L.List [L.Symbol "forall"
                                         ,L.List [L.List [L.Symbol name,tp]
                                                  | (name,tp) <- tps]
                                         ,arg'],nc')
exprToLisp (Exists ann f) c = let (arg,tps,nc) = createArgs ann c
                                  (arg',nc') = exprToLisp (f arg) nc
                              in (L.List [L.Symbol "exists"
                                         ,L.List [L.List [L.Symbol name,tp]
                                                  | (name,tp) <- tps ]
                                         ,arg'],nc')
exprToLisp (Let ann x f) c = let (arg,tps,nc) = createArgs ann c
                                 (arg',nc') = unpackArgs (\e _ cc -> exprToLisp e cc
                                                         ) x ann nc
                                 (arg'',nc'') = exprToLisp (f arg) nc'
                             in (L.List [L.Symbol "let"
                                        ,L.List [L.List [L.Symbol name,lisp] | ((name,_),lisp) <- Prelude.zip tps arg' ]
                                        ,arg''],nc'')
exprToLisp (Fun name _ _) c = (L.Symbol name,c)
exprToLisp (App (Fun name arg_ann _) x) c = let ~(x',c') = unpackArgs (\e _ i -> exprToLisp e i) x arg_ann c
                                            in if Prelude.null x'
                                               then (L.Symbol name,c')
                                               else (L.List $ (L.Symbol name):x',c')
exprToLisp (App _ _) c = error "Internal smtlib2 error: Left hand side of function application is not a function"
exprToLisp (ConTest (Constructor name) e) c = let (e',c') = exprToLisp e c
                                              in (L.List [L.Symbol $ T.append "is-" name
                                                         ,e'],c')
exprToLisp (FieldSel (Field name) e) c = let (e',c') = exprToLisp e c
                                         in (L.List [L.Symbol name,e'],c')
exprToLisp (Head xs) c = let (e,c') = exprToLisp xs c
                         in (L.List [L.Symbol "head",e],c')
exprToLisp (Tail xs) c = let (e,c') = exprToLisp xs c
                         in (L.List [L.Symbol "tail",e],c')
exprToLisp (Insert x xs) c = let (x',c') = exprToLisp x c
                                 (xs',c'') = exprToLisp xs c'
                             in (L.List [L.Symbol "insert",x',xs'],c'')
exprToLisp (Named expr name) c = let (expr',c') = exprToLisp expr c
                                 in (L.List [L.Symbol "!",expr',L.Symbol ":named",L.Symbol name],c')
exprToLisp (InternalFun args) c = (L.List (L.Symbol "_":args),c)

withUndef :: TypeRep -> (forall a. (SMTValue a,Typeable a,SMTAnnotation a ~ ()) => a -> b) -> b
withUndef rep f
  | rep == typeOf (undefined :: Bool) = f (undefined::Bool)
  | rep == typeOf (undefined :: Integer) = f (undefined::Integer)
  | rep == typeOf (undefined :: Word8) = f (undefined::Word8)
  | rep == typeOf (undefined :: Word16) = f (undefined::Word16)
  | rep == typeOf (undefined :: Word32) = f (undefined::Word32)
  | rep == typeOf (undefined :: Word64) = f (undefined::Word64)
  | otherwise = error $ "Language.SMTLib2.Instances.withUndef not implemented for "++show rep

asType :: a -> g a -> g a
asType = const id

binT :: (SMTValue b1,Typeable b1,SMTValue b2,Typeable b2,SMTValue c,Typeable c,SMTAnnotation b1 ~ (),SMTAnnotation b2 ~ (),SMTAnnotation c ~ ()) => (forall a. (SMTValue a,Typeable a,SMTAnnotation a ~ ()) => SMTExpr a -> SMT d)
        -> (SMTExpr b1 -> SMTExpr b2 -> SMTExpr c) -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> SMT (Maybe d)
binT f con g lhs rhs = do
  lhs' <- lispToExprT () g lhs
  rhs' <- lispToExprT () g rhs
  res <- f (con lhs' rhs')
  return $ Just res

lispToExprU :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> SMT b)
               -> (T.Text -> TypeRep)
               -> L.Lisp -> SMT (Maybe b)
lispToExprU f g l
  = firstJust [(unmangle l () :: SMT (Maybe Bool)) >>= maybe (return Nothing) (fmap Just . f . flip Const unit)
              ,(unmangle l () :: SMT (Maybe Integer)) >>= maybe (return Nothing) (fmap Just . f . flip Const unit)
              ,(unmangle l () :: SMT (Maybe Word8)) >>= maybe (return Nothing) (fmap Just . f . flip Const unit)
              ,(unmangle l () :: SMT (Maybe Word16)) >>= maybe (return Nothing) (fmap Just . f . flip Const unit)
              ,(unmangle l () :: SMT (Maybe Word32)) >>= maybe (return Nothing) (fmap Just . f . flip Const unit)
              ,(unmangle l () :: SMT (Maybe Word64)) >>= maybe (return Nothing) (fmap Just . f . flip Const unit)
              ,case l of
                L.Symbol name -> withUndef (g name) $ \u -> fmap Just $ f $ asType u (Var name ())
                L.List [L.Symbol "=",lhs,rhs] -> do
                  lhs' <- lispToExprU (\lhs' -> do
                                          rhs' <- lispToExprT (extractAnnotation lhs') g rhs
                                          f (Eq lhs' rhs')) g lhs
                  case lhs' of
                    Just r -> return $ Just r
                    Nothing -> lispToExprU (\rhs' -> do
                                               lhs' <- lispToExprT (extractAnnotation rhs') g lhs
                                               f (Eq lhs' rhs')) g rhs
                L.List [L.Symbol ">",lhs,rhs] -> binT f (Gt::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List [L.Symbol ">=",lhs,rhs] -> binT f (Ge::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List [L.Symbol "<",lhs,rhs] -> binT f (Lt::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List [L.Symbol "<=",lhs,rhs] -> binT f (Le::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List (L.Symbol "+":args) -> fmap Just $ mapM (lispToExprT () g) args >>= f . (Plus::[SMTExpr Integer] -> SMTExpr Integer)
                L.List [L.Symbol "-",lhs,rhs] -> binT f (Minus::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer) g lhs rhs
                L.List (L.Symbol "*":args) -> fmap Just $ mapM (lispToExprT () g) args >>= f . (Mult::[SMTExpr Integer] -> SMTExpr Integer)
                L.List [L.Symbol "/",lhs,rhs] -> binT f Div g lhs rhs
                L.List [L.Symbol "mod",lhs,rhs] -> binT f Mod g lhs rhs
                L.List (L.Symbol "and":args) -> fmap Just $ mapM (lispToExprT () g) args >>= f . And
                L.List (L.Symbol "or":args) -> fmap Just $ mapM (lispToExprT () g) args >>= f . Or
                L.List [L.Symbol "not",arg] -> fmap Just $ (lispToExprT () g arg :: SMT (SMTExpr Bool)) >>= f
                L.List [L.Symbol "bvule",lhs,rhs] -> fmap Just $ binBV BVULE g lhs rhs >>= f
                L.List [L.Symbol "bvult",lhs,rhs] -> fmap Just $ binBV BVULT g lhs rhs >>= f
                L.List [L.Symbol "bvuge",lhs,rhs] -> fmap Just $ binBV BVUGE g lhs rhs >>= f
                L.List [L.Symbol "bvugt",lhs,rhs] -> fmap Just $ binBV BVUGT g lhs rhs >>= f
                L.List [L.Symbol "bvsle",lhs,rhs] -> fmap Just $ binBV BVSLE g lhs rhs >>= f
                L.List [L.Symbol "bvslt",lhs,rhs] -> fmap Just $ binBV BVSLT g lhs rhs >>= f
                L.List [L.Symbol "bvsge",lhs,rhs] -> fmap Just $ binBV BVSGE g lhs rhs >>= f
                L.List [L.Symbol "bvsgt",lhs,rhs] -> fmap Just $ binBV BVSGT g lhs rhs >>= f
                L.List (L.Symbol fn:args) -> fmap Just $ fnToExpr f g fn args
                _ -> return Nothing
              ]

asBV :: Typeable a => (forall b. (SMTBV b,Typeable b) => SMTExpr b -> c) -> SMTExpr a -> c
asBV f e = case (gcast e :: Maybe (SMTExpr Word8)) of
  Just r -> f r
  Nothing -> case (gcast e :: Maybe (SMTExpr Word16)) of
    Just r -> f r
    Nothing -> case (gcast e :: Maybe (SMTExpr Word32)) of
      Just r -> f r
      Nothing -> case (gcast e :: Maybe (SMTExpr Word64)) of
        Just r -> f r
        Nothing -> error $ "Cannot treat expression of type "++show (typeOf e)++" as bitvector"

fnToExpr :: (forall a. (SMTValue a,Typeable a,SMTAnnotation a ~ ()) => SMTExpr a -> SMT b)
            -> (T.Text -> TypeRep)
            -> T.Text -> [L.Lisp] -> SMT b
fnToExpr f g fn args = case splitTyConApp $ g fn of
  (_,[targs,res]) -> withUndef res $ \res' -> case splitTyConApp targs of
    (_,rargs) -> case rargs of
      [] -> let [a0] = args in withUndef targs $ \t0' -> do
        p0 <- lispToExprT () g a0
        f $ asType res' $ App (Fun fn undefined undefined) (asType t0' p0)
      [t0,t1] -> let [a0,a1] = args in withUndef t0 $ \t0' ->
        withUndef t1 $ \t1' -> do
          p0 <- lispToExprT () g a0
          p1 <- lispToExprT () g a1
          f $ asType res' $ App (Fun fn undefined undefined) (asType t0' p0,
                                                              asType t1' p1)
      [t0,t1,t2] -> let [a0,a1,a2] = args in withUndef t0 $ \t0' ->
        withUndef t1 $ \t1' -> 
        withUndef t2 $ \t2' -> do
          p0 <- lispToExprT () g a0
          p1 <- lispToExprT () g a1
          p2 <- lispToExprT () g a2
          f $ asType res' $ App (Fun fn undefined undefined) (asType t0' p0,
                                                              asType t1' p1,
                                                              asType t2' p2)

fgcast :: (Typeable a,Typeable b) => L.Lisp -> c a -> c b
fgcast l x = case gcast x of
  Just r -> r
  Nothing -> error $ "Type error in expression "++show l

binBV :: (forall a. (SMTBV a,Typeable a) => SMTExpr a -> SMTExpr a -> SMTExpr b) -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> SMT (SMTExpr b)
binBV f g lhs rhs = do
  r0 <- lispToExprU (asBV (\lhs0 -> do
                              rhs0 <- lispToExprT (extractAnnotation lhs0) g rhs
                              return $ f lhs0 rhs0
                          )) g lhs
  case r0 of
    Just r -> return r
    Nothing -> do
      r1 <- lispToExprU (asBV (\rhs1 -> do
                                  lhs1 <- lispToExprT (extractAnnotation rhs1) g lhs
                                  return $ f lhs1 rhs1
                              )) g rhs
      case r1 of
        Just r -> return r
        Nothing -> error $ "Parsing bitvector expression failed"

lispToExprT :: (SMTValue a,Typeable a) => SMTAnnotation a -> (T.Text -> TypeRep) -> L.Lisp -> SMT (SMTExpr a)
lispToExprT ann g l = do
  ll <- unmangle l ann
  case ll of
    Just v -> return $ Const v ann
    Nothing -> case l of
      L.Symbol name -> return $ Var name ann
      L.List [L.Symbol "=",lhs,rhs] -> do
        lhs' <- lispToExprU (\lhs' -> do
                                rhs' <- lispToExprT (extractAnnotation lhs') g rhs
                                return $ fgcast l $ Eq lhs' rhs') g lhs
        case lhs' of
          Just r -> return r
          Nothing -> do
            rhs' <- lispToExprU (\rhs' -> do
                                    lhs' <- lispToExprT (extractAnnotation rhs') g lhs
                                    return $ fgcast l $ Eq lhs' rhs') g rhs
            case rhs' of
              Just r -> return r
              Nothing -> error $ "Failed to parse expression "++show l
      L.List [L.Symbol ">",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Gt (l' :: SMTExpr Integer) r'
      L.List [L.Symbol ">=",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Ge (l' :: SMTExpr Integer) r'
      L.List [L.Symbol "<",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Lt (l' :: SMTExpr Integer) r'
      L.List [L.Symbol "<=",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Le (l' :: SMTExpr Integer) r'
      L.List (L.Symbol "+":args) -> do
        args' <- mapM (lispToExprT () g) args
        return $ fgcast l $ Plus (args' :: [SMTExpr Integer])
      L.List [L.Symbol "-",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Minus (l' :: SMTExpr Integer) r'
      L.List (L.Symbol "*":args) -> do
        args' <- mapM (lispToExprT () g) args
        return $ fgcast l $ Mult (args' :: [SMTExpr Integer])
      L.List [L.Symbol "/",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Div l' r'
      L.List [L.Symbol "mod",lhs,rhs] -> do
        l' <- lispToExprT () g lhs
        r' <- lispToExprT () g rhs
        return $ fgcast l $ Mod l' r'
      L.List (L.Symbol "and":args) -> do
        args' <- mapM (lispToExprT () g) args
        return $ fgcast l $ And args'
      L.List (L.Symbol "or":args) -> do
        args' <- mapM (lispToExprT () g) args
        return $ fgcast l $ Or args'
      L.List [L.Symbol "not",arg] -> lispToExprT () g arg >>= return . fgcast l . Not
      L.List [L.Symbol "let",L.List syms,arg] -> letToExpr g syms arg
      L.List [L.Symbol "bvule",lhs,rhs] -> fgcast l $ binBV BVULE g lhs rhs
      L.List [L.Symbol "bvult",lhs,rhs] -> fgcast l $ binBV BVULT g lhs rhs
      L.List [L.Symbol "bvuge",lhs,rhs] -> fgcast l $ binBV BVUGE g lhs rhs
      L.List [L.Symbol "bvugt",lhs,rhs] -> fgcast l $ binBV BVUGT g lhs rhs
      L.List [L.Symbol "bvsle",lhs,rhs] -> fgcast l $ binBV BVSLE g lhs rhs
      L.List [L.Symbol "bvslt",lhs,rhs] -> fgcast l $ binBV BVSLT g lhs rhs
      L.List [L.Symbol "bvsge",lhs,rhs] -> fgcast l $ binBV BVSGE g lhs rhs
      L.List [L.Symbol "bvsgt",lhs,rhs] -> fgcast l $ binBV BVSGT g lhs rhs
      L.List (L.Symbol fn:args) -> fnToExpr (return . fgcast l) g fn args
      L.List [L.List (L.Symbol "_":args),expr] -> do
        expr' <- lispToExprT () g expr
        return $ fgcast l $ App (InternalFun args) expr'
      _ -> error $ "Cannot parse "++show l
      where
        replSymbol name name' (L.Symbol x)
          | x == name = L.Symbol name'
          | otherwise = L.Symbol x
        replSymbol name name' (L.List xs) = L.List (fmap (replSymbol name name') xs)
        replSymbol _ _ x = x
      
        letToExpr g' (L.List [L.Symbol name,expr]:rest) arg
          = do
            res <- lispToExprU (\expr' -> do
                                   rest' <- letToExpr (\txt -> if txt==name
                                                               then typeOf expr'
                                                               else g txt) rest arg
                                   return $ Let (extractAnnotation expr') expr' (\var@(Var name' _) -> replaceName (\n -> if n==name 
                                                                                                                          then name' 
                                                                                                                          else n) rest')
                               ) g' expr
            case res of
              Just r -> return r
              Nothing -> error $ "Unparseable expression "++show expr++" in let expression"
        letToExpr g [] arg = lispToExprT ann g arg
        letToExpr _ (x:xs) _ = error $ "Unparseable entry "++show x++" in let expression"

extractAnnotation :: SMTExpr a -> SMTAnnotation a
extractAnnotation (Var _ ann) = ann
extractAnnotation (Const _ ann) = ann
extractAnnotation (Eq _ _) = ()
extractAnnotation (Ge _ _) = ()
extractAnnotation (Le _ _) = ()
extractAnnotation (Lt _ _) = ()
extractAnnotation (Distinct _) = ()
extractAnnotation (Plus (x:_)) = extractAnnotation x
extractAnnotation (Minus x _) = extractAnnotation x
extractAnnotation (Mult (x:_)) = extractAnnotation x
extractAnnotation (Div _ _) = ()
extractAnnotation (Mod _ _) = ()
extractAnnotation (Divide _ _) = ()
extractAnnotation (Neg x) = extractAnnotation x
extractAnnotation (ITE _ x _) = extractAnnotation x
extractAnnotation (And _) = ()
extractAnnotation (Or _) = ()
extractAnnotation (XOr _ _) = ()
extractAnnotation (Implies _ _) = ()
extractAnnotation (Not _) = ()
extractAnnotation (Select arr _) = snd (extractAnnotation arr)
extractAnnotation (Store arr _ _) = extractAnnotation arr
extractAnnotation (BVAdd x _) = extractAnnotation x
extractAnnotation (BVSub x _) = extractAnnotation x
extractAnnotation (BVMul x _) = extractAnnotation x
extractAnnotation (BVURem x _) = extractAnnotation x
extractAnnotation (BVSRem x _) = extractAnnotation x
extractAnnotation (BVUDiv x _) = extractAnnotation x
extractAnnotation (BVSDiv x _) = extractAnnotation x
extractAnnotation (BVConcat x y) = concatAnn (getUndef x) (getUndef y) (extractAnnotation x) (extractAnnotation y)
extractAnnotation (BVExtract _ _ ann _) = ann
extractAnnotation (BVULE _ _) = ()
extractAnnotation (BVULT _ _) = ()
extractAnnotation (BVUGE _ _) = ()
extractAnnotation (BVUGT _ _) = ()
extractAnnotation (BVSLE _ _) = ()
extractAnnotation (BVSLT _ _) = ()
extractAnnotation (BVSGE _ _) = ()
extractAnnotation (BVSGT _ _) = ()
extractAnnotation (BVSHL x _) = extractAnnotation x
extractAnnotation (BVXor x _) = extractAnnotation x
extractAnnotation (BVAnd x _) = extractAnnotation x
extractAnnotation (BVOr x _) = extractAnnotation x
extractAnnotation (Forall _ _) = ()
extractAnnotation (Exists _ _) = ()
extractAnnotation (Let _ x f) = extractAnnotation (f x)
extractAnnotation (ConTest _ _) = ()
extractAnnotation (Head x) = extractAnnotation x
extractAnnotation (Tail x) = extractAnnotation x
extractAnnotation (Insert _ x) = extractAnnotation x
extractAnnotation (Named x _) = extractAnnotation x
extractAnnotation (InterpolationGrp _ _) = ()

instance (SMTValue a) => LiftArgs (SMTExpr a) where
  type Unpacked (SMTExpr a) = a
  liftArgs = Const
  unliftArgs = getValue
