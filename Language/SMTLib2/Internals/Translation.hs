{-# LANGUAGE RankNTypes,TypeFamilies,OverloadedStrings,GADTs,FlexibleContexts #-}
module Language.SMTLib2.Internals.Translation where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances ()

import qualified Data.AttoLisp as L
import Data.Typeable
import Data.Text as T
import Data.Word
import Data.Array
import qualified Data.Map as Map (Map,lookup,elems)

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
  
-- | Extract values of compound expressions from the generated model.
getValue' :: SMTValue t => SMTAnnotation t -> SMTExpr t -> SMT t
getValue' ann expr = do
  res <- fmap removeLets $ getRawValue expr
  case unmangle res ann of
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
defFunAnnNamed :: (Args a,SMTType r) => String -> ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT (SMTExpr (SMTFun a r))
defFunAnnNamed name ann_arg ann_res f = do
  fname <- freeName name
  (names,_,_) <- getSMT
  let c_args = case Map.lookup "arg" names of
        Nothing -> 0
        Just n -> n

      res = Fun fname ann_arg ann_res
      
      (_,rtp) = getFunUndef res
      
      (au,tps,c_args') = createArgs ann_arg (c_args+1)
      
      (expr',_) = exprToLisp (f au) c_args'
  defineFun fname tps (getSort rtp ann_res) expr'
  return res

-- | Like `defFunAnnNamed`, but defaults the function name to "fun".
defFunAnn :: (Args a,SMTType r) => ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT (SMTExpr (SMTFun a r))
defFunAnn = defFunAnnNamed "fun"

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
exprToLisp (Rem l r) c = let (l',c') = exprToLisp l c
                             (r',c'') = exprToLisp r c'
                         in (L.List [L.Symbol "rem",l',r'],c'')
exprToLisp (Neg e) c = let (e',c') = exprToLisp e c
                       in (L.List [L.Symbol "-",e'],c')
exprToLisp (Abs e) c = let (e',c') = exprToLisp e c
                       in (L.List [L.Symbol "abs",e'],c')
exprToLisp (ToReal e) c = let (e',c') = exprToLisp e c
                          in (L.List [L.Symbol "to_real",e'],c')
exprToLisp (ToInt e) c = let (e',c') = exprToLisp e c
                         in (L.List [L.Symbol "to_int",e'],c')
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
exprToLisp expr@(ConstArray v ann) c = let (v',c') = exprToLisp v c
                                           (ui,_,uv) = getArrayUndef expr
                                       in (L.List [L.List [L.Symbol "as",L.Symbol "const",
                                                           L.List ((L.Symbol "Array"):(argSorts ui ann)++[getSort uv (extractAnnotation v)])]
                                                  ,v'],c')
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
exprToLisp (BVLSHR l r) c = let (l',c') = exprToLisp l c
                                (r',c'') = exprToLisp r c'
                            in (L.List [L.Symbol "bvlshr",l',r'],c'')
exprToLisp (BVASHR l r) c = let (l',c') = exprToLisp l c
                                (r',c'') = exprToLisp r c'
                            in (L.List [L.Symbol "bvashr",l',r'],c'')
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
exprToLisp (BVNot expr) c = let (expr',c') = exprToLisp expr c
                            in (L.List [L.Symbol "bvnot",expr'],c')
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
exprToLisp (App fun x) c = let (l,arg_ann,_) = getFunAnn fun
                               ~(x',c') = unpackArgs (\e _ i -> exprToLisp e i) x arg_ann c
                           in if Prelude.null x'
                              then (l,c')
                              else (L.List $ l:x',c')
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
exprToLisp (InternalFun arguments) c = (L.List (L.Symbol "_":arguments),c)
exprToLisp Undefined _ = error "Language.SMTLib2.Internals.Translation.exprToLisp: Called on Undefined expression."

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

binT :: (SMTValue b1,Typeable b1,
         SMTValue b2,Typeable b2,
         SMTValue c,Typeable c,
         SMTAnnotation b1 ~ (),
         SMTAnnotation b2 ~ (),
         SMTAnnotation c ~ ()) 
        => (forall a. (SMTValue a,Typeable a,SMTAnnotation a ~ ()) => SMTExpr a -> d)
        -> (SMTExpr b1 -> SMTExpr b2 -> SMTExpr c) -> Map.Map TyCon DeclaredType -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> Maybe d
binT f con tps g lhs rhs 
  = let lhs' = lispToExprT tps () g lhs
        rhs' = lispToExprT tps () g rhs
    in Just $ f (con lhs' rhs')

unmangleDeclared :: ((forall a. (SMTValue a,Typeable a) => SMTExpr a -> b)) -> DeclaredType -> L.Lisp -> Maybe b
unmangleDeclared f d l
  = case withDeclaredValueType
         (\u ann -> case unmangle' u l ann of
             Nothing -> Nothing
             Just r -> Just $ f (Const r ann)) d of
      Just (Just x) -> Just x
      _ -> Nothing
  where
    unmangle' :: SMTValue a => a -> L.Lisp -> SMTAnnotation a -> Maybe a
    unmangle' _ = unmangle

createVarDeclared :: ((forall a. (SMTValue a,Typeable a) => SMTExpr a -> b)) -> DeclaredType -> Text -> Maybe b
createVarDeclared f d name
  = withDeclaredValueType (\u ann -> f (eq u (Var name ann))) d
  where
    eq :: a -> SMTExpr a -> SMTExpr a
    eq = const id

lispToExprU :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> b)
               -> Map.Map TyCon DeclaredType
               -> (T.Text -> TypeRep)
               -> L.Lisp -> Maybe b
lispToExprU f tps g l
  = firstJust $
    [ unmangleDeclared f tp l | tp <- Map.elems tps ] ++
    [case l of
        L.Symbol name -> let (tycon,_) = splitTyConApp (g name)
                         in case Map.lookup tycon tps of
                           Nothing -> Nothing
                           Just decl -> createVarDeclared f decl name
        L.List [L.Symbol "=",lhs,rhs] 
          -> let lhs' = lispToExprU (\lhs' -> let rhs' = lispToExprT tps (extractAnnotation lhs') g rhs
                                              in f (Eq lhs' rhs')
                                    ) tps g lhs
             in case lhs' of
               Just r -> Just r
               Nothing -> lispToExprU (\rhs' -> let lhs'' = lispToExprT tps (extractAnnotation rhs') g lhs
                                                in f (Eq lhs'' rhs')
                                      ) tps g rhs
        L.List [L.Symbol ">=",lhs,rhs] -> binT f (Ge::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) tps g lhs rhs
        L.List [L.Symbol ">",lhs,rhs] -> binT f (Gt::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) tps g lhs rhs
        L.List [L.Symbol "<=",lhs,rhs] -> binT f (Le::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) tps g lhs rhs
        L.List [L.Symbol "<",lhs,rhs] -> binT f (Lt::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) tps g lhs rhs
        L.List (L.Symbol "distinct":first:rest)
          -> lispToExprU (\first' -> let rest' = fmap (lispToExprT tps (extractAnnotation first') g) rest
                                     in f $ Distinct (first':rest')) tps g first
        L.List (L.Symbol "+":arg) -> Just $ f $ (Plus::[SMTExpr Integer] -> SMTExpr Integer) $ 
                                     fmap (lispToExprT tps () g) arg
        L.List [L.Symbol "-",lhs,rhs] -> binT f (Minus::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer) tps g lhs rhs
        L.List (L.Symbol "*":arg) -> Just $ f $ (Mult::[SMTExpr Integer] -> SMTExpr Integer) $
                                     fmap (lispToExprT tps () g) arg
        L.List [L.Symbol "div",lhs,rhs] -> binT f Div tps g lhs rhs
        L.List [L.Symbol "mod",lhs,rhs] -> binT f Mod tps g lhs rhs
        L.List [L.Symbol "rem",lhs,rhs] -> binT f Rem tps g lhs rhs
        L.List [L.Symbol "/",lhs,rhs] -> binT f Divide tps g lhs rhs
        L.List [L.Symbol "-",arg] -> Just $ f $ Neg (lispToExprT tps () g arg :: SMTExpr Integer)
        L.List [L.Symbol "abs",arg] -> Just $ f $ Abs (lispToExprT tps () g arg :: SMTExpr Integer)
        L.List [L.Symbol "to_real",arg] -> Just $ f $ ToReal (lispToExprT tps () g arg :: SMTExpr Integer)
        L.List [L.Symbol "to_int",arg] -> Just $ f $ ToInt (lispToExprT tps () g arg :: SMTExpr Rational)
        L.List [L.Symbol "ite",cond,lhs,rhs]
          -> let cond' = lispToExprT tps () g cond
             in case lispToExprU (\lhs' -> let rhs' = lispToExprT tps (extractAnnotation lhs') g rhs
                                           in f (ITE cond' lhs' rhs')
                                 ) tps g lhs of
                  Just r -> Just r
                  Nothing -> lispToExprU (\rhs' -> let lhs'' = lispToExprT tps (extractAnnotation rhs') g lhs
                                                   in f (ITE cond' lhs'' rhs')
                                         ) tps g rhs
        L.List (L.Symbol "and":arg) -> Just $ f $ And $ fmap (lispToExprT tps () g) arg
        L.List (L.Symbol "or":arg) -> Just $ f $ Or $ fmap (lispToExprT tps () g) arg
        L.List [L.Symbol "xor",lhs,rhs] 
          -> let lhs' = lispToExprT tps () g lhs
                 rhs' = lispToExprT tps () g rhs
             in Just $ f (XOr lhs' rhs')
        L.List [L.Symbol "=>",lhs,rhs] 
          -> let lhs' = lispToExprT tps () g lhs
                 rhs' = lispToExprT tps () g rhs
             in Just $ f (Implies lhs' rhs')
        L.List [L.Symbol "not",arg] -> Just $ f $ Not (lispToExprT tps () g arg :: SMTExpr Bool)
        L.List [L.Symbol "bvule",lhs,rhs] -> Just $ f $ binBV BVULE tps g lhs rhs
        L.List [L.Symbol "bvult",lhs,rhs] -> Just $ f $ binBV BVULT tps g lhs rhs
        L.List [L.Symbol "bvuge",lhs,rhs] -> Just $ f $ binBV BVUGE tps g lhs rhs
        L.List [L.Symbol "bvugt",lhs,rhs] -> Just $ f $ binBV BVUGT tps g lhs rhs
        L.List [L.Symbol "bvsle",lhs,rhs] -> Just $ f $ binBV BVSLE tps g lhs rhs
        L.List [L.Symbol "bvslt",lhs,rhs] -> Just $ f $ binBV BVSLT tps g lhs rhs
        L.List [L.Symbol "bvsge",lhs,rhs] -> Just $ f $ binBV BVSGE tps g lhs rhs
        L.List [L.Symbol "bvsgt",lhs,rhs] -> Just $ f $ binBV BVSGT tps g lhs rhs
        L.List [L.Symbol "forall",L.List args,body] -> Just $ f $ quantToExpr Forall tps g args body
        L.List [L.Symbol "exists",L.List args,body] -> Just $ f $ quantToExpr Exists tps g args body
        L.List [L.Symbol "let",L.List args,body] -> letToExpr f tps g args body
        L.List (L.Symbol fn:arg) -> Just $ fnToExpr f tps g fn arg
        _ -> Nothing
    ]
  where
    letToExpr :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> b)
                 -> Map.Map TyCon DeclaredType
                 -> (T.Text -> TypeRep)
                 -> [L.Lisp] -> L.Lisp -> Maybe b
    letToExpr f tps' g' (L.List [L.Symbol name,expr]:rest) arg
      = case lispToExprU 
             (\expr' -> letToExpr
                        (\body -> f $ Let (extractAnnotation expr') expr' 
                                  (\sym -> replaceName (\n -> if n==name
                                                              then gcast sym
                                                              else Nothing) body)
                        ) tps' (\txt -> if txt==name
                                        then typeOf $ getUndef expr'
                                        else g' txt) rest arg
             ) tps' g' expr of
          Just r -> r
          Nothing -> Nothing
    letToExpr f tps' g' [] arg = lispToExprU f tps' g' arg
    letToExpr _ _ _ (x:_) _ = error $ "Unparseable entry "++show x++" in let expression"

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

fnToExpr :: (forall a. (SMTValue a,Typeable a,SMTAnnotation a ~ ()) => SMTExpr a -> b)
            -> Map.Map TyCon DeclaredType
            -> (T.Text -> TypeRep)
            -> T.Text -> [L.Lisp] -> b
fnToExpr f tps g fn arg = case splitTyConApp $ g fn of
  (_,[targs,res]) -> withUndef res $ \res' -> case splitTyConApp targs of
    (_,rargs) -> case rargs of
      [] -> let [a0] = arg 
            in withUndef targs $ 
               \t0' -> f $ asType res' $ App (Fun fn undefined undefined) (asType t0' $ lispToExprT tps () g a0)
      [t0,t1] -> let [a0,a1] = arg 
                 in withUndef t0 $ 
                    \t0' -> withUndef t1 $ 
                            \t1' -> let p0 = lispToExprT tps () g a0
                                        p1 = lispToExprT tps () g a1
                                    in f $ asType res' $ App (Fun fn undefined undefined) (asType t0' p0,asType t1' p1)
      [t0,t1,t2] -> let [a0,a1,a2] = arg 
                    in withUndef t0 $ 
                       \t0' -> withUndef t1 $ 
                               \t1' -> withUndef t2 $ 
                                       \t2' -> let p0 = lispToExprT tps () g a0
                                                   p1 = lispToExprT tps () g a1
                                                   p2 = lispToExprT tps () g a2
                                               in f $ asType res' $ App (Fun fn undefined undefined) (asType t0' p0,asType t1' p1,asType t2' p2)
      _ -> error "Language.SMTLib2.Internals.Translation.fnToExpr: Invalid number of function arguments given (more than 3)."
  _ -> error $ "Language.SMTLib2.Internals.Translation.fnToExpr: Invalid function type "++(show $ g fn)++" given to function "++show fn++"."

fgcast :: (Typeable a,Typeable b) => L.Lisp -> c a -> c b
fgcast l x = case gcast x of
  Just r -> r
  Nothing -> error $ "Type error in expression "++show l

binBV :: (forall a. (SMTBV a,Typeable a) => SMTExpr a -> SMTExpr a -> SMTExpr b) 
         -> Map.Map TyCon DeclaredType -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> SMTExpr b
binBV f tps g lhs rhs
  = let r0 = lispToExprU (asBV (\lhs0 -> let rhs0 = lispToExprT tps (extractAnnotation lhs0) g rhs
                                         in f lhs0 rhs0
                               )) tps g lhs
    in case r0 of
      Just r -> r
      Nothing -> let r1 = lispToExprU (asBV (\rhs1 -> let lhs1 = lispToExprT tps (extractAnnotation rhs1) g lhs
                                                      in f lhs1 rhs1
                                            )) tps g rhs
                 in case r1 of
                   Just r -> r
                   Nothing -> error $ "Parsing bitvector expression failed"

lispToExprT :: (SMTValue a,Typeable a) => Map.Map TyCon DeclaredType -> SMTAnnotation a -> (T.Text -> TypeRep) -> L.Lisp -> SMTExpr a
lispToExprT tps ann g l = case unmangle l ann of
    Just v -> Const v ann
    Nothing -> case l of
      L.Symbol name -> Var name ann
      L.List [L.Symbol "=",lhs,rhs] 
        -> let lhs' = lispToExprU (\lhs' -> let rhs' = lispToExprT tps (extractAnnotation lhs') g rhs
                                            in fgcast l $ Eq lhs' rhs'
                                  ) tps g lhs
           in case lhs' of
             Just r -> r
             Nothing -> let rhs' = lispToExprU (\rhs' -> let lhs'' = lispToExprT tps (extractAnnotation rhs') g lhs
                                                         in fgcast l $ Eq lhs'' rhs'
                                               ) tps g rhs
                        in case rhs' of
                          Just r -> r
                          Nothing -> error $ "Failed to parse expression "++show l
      L.List [L.Symbol ">",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                           r' = lispToExprT tps () g rhs
                                       in fgcast l $ Gt (l' :: SMTExpr Integer) r'
      L.List [L.Symbol ">=",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                            r' = lispToExprT tps () g rhs
                                        in fgcast l $ Ge (l' :: SMTExpr Integer) r'
      L.List [L.Symbol "<",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                           r' = lispToExprT tps () g rhs
                                       in fgcast l $ Lt (l' :: SMTExpr Integer) r'
      L.List [L.Symbol "<=",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                            r' = lispToExprT tps () g rhs
                                        in fgcast l $ Le (l' :: SMTExpr Integer) r'
      L.List (L.Symbol "+":arg) -> let arg' = fmap (lispToExprT tps () g) arg
                                   in  fgcast l $ Plus (arg' :: [SMTExpr Integer])
      L.List [L.Symbol "-",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                           r' = lispToExprT tps () g rhs
                                       in fgcast l $ Minus (l' :: SMTExpr Integer) r'
      L.List (L.Symbol "*":arg) -> let arg' = fmap (lispToExprT tps () g) arg
                                   in fgcast l $ Mult (arg' :: [SMTExpr Integer])
      L.List [L.Symbol "/",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                           r' = lispToExprT tps () g rhs
                                       in fgcast l $ Div l' r'
      L.List [L.Symbol "div",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                             r' = lispToExprT tps () g rhs
                                         in fgcast l $ Div l' r'
      L.List [L.Symbol "mod",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                             r' = lispToExprT tps () g rhs
                                         in fgcast l $ Mod l' r'
      L.List [L.Symbol "rem",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                             r' = lispToExprT tps () g rhs
                                         in fgcast l $ Rem l' r'
      L.List [L.Symbol "to_real",arg] -> let arg' = lispToExprT tps () g arg
                                         in fgcast l $ ToReal arg'
      L.List [L.Symbol "to_int",arg] -> let arg' = lispToExprT tps () g arg
                                        in fgcast l $ ToInt arg'
      L.List (L.Symbol "and":arg) -> let arg' = fmap (lispToExprT tps () g) arg
                                     in fgcast l $ And arg'
      L.List (L.Symbol "or":arg) -> let arg' = fmap (lispToExprT tps () g) arg
                                    in fgcast l $ Or arg'
      L.List [L.Symbol "xor",lhs,rhs] -> let l' = lispToExprT tps () g lhs
                                             r' = lispToExprT tps () g rhs
                                         in fgcast l $ XOr l' r'
      L.List [L.Symbol "ite",cond,lhs,rhs]
        -> let c' = lispToExprT tps () g cond
               lhs' = lispToExprU (\lhs' -> let rhs' = lispToExprT tps (extractAnnotation lhs') g rhs
                                            in fgcast l $ ITE c' lhs' rhs'
                                  ) tps g lhs
               rhs' = lispToExprU (\rhs' -> let lhs'' = lispToExprT tps (extractAnnotation rhs') g lhs
                                            in fgcast l $ ITE c' lhs'' rhs'
                                  ) tps g rhs
           in case lhs' of
             Just r -> r
             Nothing -> case rhs' of
               Just r -> r
               Nothing -> error $ "Failed to parse expression "++show l
      L.List [L.Symbol "not",arg] -> fgcast l $ Not $ lispToExprT tps () g arg
      L.List [L.Symbol "let",L.List syms,arg] -> letToExpr tps g syms arg
      L.List [L.Symbol "bvule",lhs,rhs] -> fgcast l $ binBV BVULE tps g lhs rhs
      L.List [L.Symbol "bvult",lhs,rhs] -> fgcast l $ binBV BVULT tps g lhs rhs
      L.List [L.Symbol "bvuge",lhs,rhs] -> fgcast l $ binBV BVUGE tps g lhs rhs
      L.List [L.Symbol "bvugt",lhs,rhs] -> fgcast l $ binBV BVUGT tps g lhs rhs
      L.List [L.Symbol "bvsle",lhs,rhs] -> fgcast l $ binBV BVSLE tps g lhs rhs
      L.List [L.Symbol "bvslt",lhs,rhs] -> fgcast l $ binBV BVSLT tps g lhs rhs
      L.List [L.Symbol "bvsge",lhs,rhs] -> fgcast l $ binBV BVSGE tps g lhs rhs
      L.List [L.Symbol "bvsgt",lhs,rhs] -> fgcast l $ binBV BVSGT tps g lhs rhs
      L.List [L.Symbol "forall",L.List vars,body] -> fgcast l $ quantToExpr Forall tps g vars body
      L.List [L.Symbol "exists",L.List vars,body] -> fgcast l $ quantToExpr Exists tps g vars body
      L.List (L.Symbol fn:arg) -> fnToExpr (fgcast l) tps g fn arg
      L.List [L.List (L.Symbol "_":arg),expr] 
        -> fgcast l $ App (InternalFun arg) $
           lispToExprT tps () g expr
      _ -> error $ "Cannot parse "++show l
      where
        letToExpr tps' g' (L.List [L.Symbol name,expr]:rest) arg
          = let res = lispToExprU 
                      (\expr' -> let rest' = letToExpr tps' (\txt -> if txt==name
                                                                     then typeOf $ getUndef expr'
                                                                     else g' txt) rest arg
                                     ann' = extractAnnotation expr'
                                 in Let ann' expr' (\sym -> replaceName (\n -> if n==name 
                                                                               then gcast sym
                                                                               else Nothing) rest')
                      ) tps' g' expr
            in case res of
              Just r -> r
              Nothing -> error $ "Unparseable expression "++show expr++" in let expression"
        letToExpr tps' g' [] arg = lispToExprT tps' ann g' arg
        letToExpr _ _ (x:_) _ = error $ "Unparseable entry "++show x++" in let expression"

quantToExpr :: (forall a. Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool)
               -> Map.Map TyCon DeclaredType -> (T.Text -> TypeRep) -> [L.Lisp] -> L.Lisp -> SMTExpr Bool
quantToExpr q tps' g' (L.List [L.Symbol var,tp]:rest) body
  = let decl = declForSMTType tp tps'
        expr = quantToExpr q tps' (\txt -> if txt==var
                                           then declaredTypeRep decl
                                           else g' txt) rest body
        getForall :: Typeable a => a -> SMTExpr a -> SMTExpr Bool
        getForall u sym = replaceName (\n -> if n==var
                                             then gcast sym
                                             else Nothing) expr
    in withDeclaredType (\u ann -> q ann $ getForall u) decl
quantToExpr q tps' g' [] body = lispToExprT tps' () g' body

-- | Reconstruct the type annotation for a given SMT expression.
extractAnnotation :: SMTExpr a -> SMTAnnotation a
extractAnnotation (Var _ ann) = ann
extractAnnotation (Const _ ann) = ann
extractAnnotation (Eq _ _) = ()
extractAnnotation (Ge _ _) = ()
extractAnnotation (Gt _ _) = ()
extractAnnotation (Le _ _) = ()
extractAnnotation (Lt _ _) = ()
extractAnnotation (Distinct _) = ()
extractAnnotation (Plus (x:_)) = extractAnnotation x
extractAnnotation (Plus []) = error "Internal smtlib2 error: Can't extract annotation from empty Plus."
extractAnnotation (Minus x _) = extractAnnotation x
extractAnnotation (Mult (x:_)) = extractAnnotation x
extractAnnotation (Mult []) = error "Internal smtlib2 error: Can't extract annotation from empty Mult."
extractAnnotation (Div _ _) = ()
extractAnnotation (Mod _ _) = ()
extractAnnotation (Rem _ _) = ()
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
extractAnnotation (AsArray (Fun _ iann eann)) = (iann,eann)
extractAnnotation (AsArray _) = error "Internal smtlib2 error: Argument to AsArray isn't a function."
extractAnnotation (ConstArray e ann) = (ann,extractAnnotation e)
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
extractAnnotation (BVLSHR x _) = extractAnnotation x
extractAnnotation (BVASHR x _) = extractAnnotation x
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
extractAnnotation (Fun _ _ _) = error "Internal smtlib2 error: extractAnnotation called on Fun, which isn't a SMTType instance."
extractAnnotation (InternalFun _) = error "Internal smtlib2 error: extractAnnotation called on Fun, which isn't a SMTType instance."
extractAnnotation (App (Fun _ _ ann) _) = ann
extractAnnotation (App _ _) = error "Internal smtlib2 error: First argument to App isn't a function."
extractAnnotation Undefined = error "Internal smtlib2 error: extractAnnotation called on Undefined."
extractAnnotation (FieldSel field expr) = getFieldAnn field (extractAnnotation expr)

instance (SMTValue a) => LiftArgs (SMTExpr a) where
  type Unpacked (SMTExpr a) = a
  liftArgs = Const
  unliftArgs = getValue
