{-# LANGUAGE RankNTypes,TypeFamilies,OverloadedStrings,GADTs,FlexibleContexts,ScopedTypeVariables,CPP #-}
module Language.SMTLib2.Internals.Translation where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances (extractAnnotation)
import Language.SMTLib2.Functions

import qualified Data.AttoLisp as L
import Data.Typeable
import Data.Text as T hiding (foldl1,head)
import Data.Word
import Data.Array
import qualified Data.Map as Map (Map,lookup,elems)
import Data.Monoid

import Data.Unit

#ifdef SMTLIB2_WITH_CONSTRAINTS
import Data.Constraint
import Data.Proxy
#endif

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
defFun :: (Liftable a,SMTType r,Unit (ArgAnnotation a),Unit (SMTAnnotation r)) => (a -> SMTExpr r) -> SMT (SMTFun a r)
defFun = defFunAnn unit unit

-- | Define a new constant
defConst :: (SMTType r,Unit (SMTAnnotation r)) => SMTExpr r -> SMT (SMTExpr r)
defConst = defConstAnn unit

-- | Define a new constant with a type annotation.
defConstAnn :: (SMTType r) => SMTAnnotation r -> SMTExpr r -> SMT (SMTExpr r)
defConstAnn ann e = do
  fname <- freeName "constvar"
  let (expr',_) = exprToLisp e 0
  defineFun fname [] (getSort (getUndef e) ann) expr'
  return $ Var fname ann

-- | Define a new function with a body and custom type annotations for arguments and result.
defFunAnnNamed :: (Liftable a,SMTType r) => String -> ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT (SMTFun a r)
defFunAnnNamed name ann_arg ann_res f = do
  fname <- freeName name
  (names,_,_) <- getSMT
  let c_args = case Map.lookup "arg" names of
        Nothing -> 0
        Just n -> n

      res = SMTFun fname ann_res
      
      (_,rtp) = getFunUndef res
      
      (au,tps,c_args') = createArgs ann_arg (c_args+1)
      
      (expr',_) = exprToLisp (f au) c_args'
  defineFun fname tps (getSort rtp ann_res) expr'
  return res

-- | Like `defFunAnnNamed`, but defaults the function name to "fun".
defFunAnn :: (Liftable a,SMTType r) => ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT (SMTFun a r)
defFunAnn = defFunAnnNamed "fun"

-- | Extract all values of an array by giving the range of indices.
unmangleArray :: (Liftable i,LiftArgs i,Ix (Unpacked i),SMTValue v,
                  --Unit (SMTAnnotation (Unpacked i)),
                  Unit (ArgAnnotation i)) 
                 => (Unpacked i,Unpacked i) 
                 -> SMTExpr (SMTArray i v) 
                 -> SMT (Array (Unpacked i) v)
unmangleArray b expr = mapM (\i -> do
                                v <- getValue (App Select (expr,liftArgs i unit))
                                return (i,v)
                            ) (range b) >>= return.array b

withSort :: Sort -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withSort (Sort u ann) f = f u ann
withSort (ArraySort i v) f = withArraySort i v f

withArraySort :: [Sort] -> Sort -> (forall i v. (Args i,SMTType v) => SMTArray i v -> (ArgAnnotation i,SMTAnnotation v) -> a) -> a
withArraySort idx v f
  = withArgSort idx $
    \(_::i) anni 
    -> withSort v $
       \(_::vt) annv -> f (undefined::SMTArray i vt) (anni,annv)

withArgSort :: [Sort] -> (forall i. Args i => i -> ArgAnnotation i -> a) -> a
withArgSort [] f = f () ()
withArgSort [i] f = withSort i $
                    \(_::ti) anni -> f (undefined::SMTExpr ti) anni
withArgSort [i1,i2] f
  = withSort i1 $
    \(_::t1) ann1
     -> withSort i2 $
        \(_::t2) ann2 -> f (undefined::(SMTExpr t1,SMTExpr t2)) (ann1,ann2)
withArgSort [i1,i2,i3] f
  = withSort i1 $
    \(_::t1) ann1
     -> withSort i2 $
        \(_::t2) ann2 
        -> withSort i3 $
           \(_::t3) ann3 -> f (undefined::(SMTExpr t1,SMTExpr t2,SMTExpr t3)) (ann1,ann2,ann3)
withArgSort _ _ = error $ "smtlib2: Please provide more cases for withArgSort."

exprsToLisp :: [SMTExpr t] -> Integer -> ([L.Lisp],Integer)
exprsToLisp [] c = ([],c)
exprsToLisp (e:es) c = let (e',c') = exprToLisp e c
                           (es',c'') = exprsToLisp es c'
                       in (e':es',c'')

exprToLisp :: SMTExpr t -> Integer -> (L.Lisp,Integer)
exprToLisp (Var name _) c = (L.Symbol name,c)
exprToLisp (Const x ann) c = (mangle x ann,c)
exprToLisp (AsArray f arg) c 
  = let f' = getFunctionSymbol f arg
    in (L.List [L.Symbol "_",L.Symbol "as-array",f'],c)
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
exprToLisp (App fun x) c = let arg_ann = extractArgAnnotation x
                               l = getFunctionSymbol fun arg_ann
                               ~(x',c1) = unpackArgs (\e _ i -> exprToLisp e i) x
                                          arg_ann c
                           in if Prelude.null x'
                              then (l,c1)
                              else (L.List $ l:x',c1)
exprToLisp (Named expr name) c = let (expr',c') = exprToLisp expr c
                                 in (L.List [L.Symbol "!",expr',L.Symbol ":named",L.Symbol name],c')

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

createVarDeclared :: ((forall a. SMTType a => SMTExpr a -> b)) -> DeclaredType -> Text -> b
createVarDeclared f d name
  = withDeclaredType (\u ann -> f (eq u (Var name ann))) d
  where
    eq :: a -> SMTExpr a -> SMTExpr a
    eq = const id

newtype FunctionParser 
  = FunctionParser { parseFun :: forall a. L.Lisp -> Maybe [Sort] -> Maybe Sort
                                 -> FunctionParser
                                 -> (forall f. SMTFunction f => f -> a)
                                 -> Maybe a }

instance Monoid FunctionParser where
  mempty = FunctionParser $ \_ _ _ _ _ -> Nothing
  mappend p1 p2 = FunctionParser $
                  \sym sort_arg sort_ret rec f 
                  -> case parseFun p1 sym sort_arg sort_ret rec f of
                    Nothing -> parseFun p2 sym sort_arg sort_ret rec f
                    Just r -> Just r

lispToExpr :: FunctionParser -> SortParser 
              -> (T.Text -> Maybe UntypedExpr) 
              -> Map.Map TyCon DeclaredType
              -> (forall a. SMTType a => SMTExpr a -> b) -> Maybe Sort -> L.Lisp -> Maybe b
lispToExpr fun sort bound tps f expected l
  = firstJust $
    [ unmangleDeclared f tp l | tp <- Map.elems tps ] ++
    [case l of
        L.Symbol name -> case bound name of
          Nothing -> Nothing
          Just subst -> entype (\subst' -> Just $ f subst') subst
        L.List [L.Symbol "forall",L.List args',body]
          -> fmap f $ quantToExpr Forall fun sort bound tps args' body
        L.List [L.Symbol "exists",L.List args',body]
          -> fmap f $ quantToExpr Exists fun sort bound tps args' body
        L.List [L.Symbol "let",L.List args',body]
          -> let struct = parseLetStruct fun sort bound tps expected args' body
             in Just $ convertLetStruct f struct
        --L.List [L.Symbol "_",L.Symbol "as-array",fsym]
        --  -> parseFun fun fsym (
        L.List (fsym:args') -> do
          nargs <- lispToExprs args'
          let arg_tps = fmap (entype $ \(expr::SMTExpr t) 
                                       -> toSort (undefined::t) (extractAnnotation expr)
                             ) nargs
          parseFun fun fsym (Just arg_tps) expected fun $
            \rfun -> case (do
                              (rargs,rest) <- toArgs nargs
                              case rest of
                                [] -> Just $ App rfun rargs
                                _ -> Nothing) of
                       Just e -> f e
                       Nothing -> error $ "smtlib2: Wrong arguments for function"
        _ -> Nothing
    ]
  where
    lispToExprs = mapM $ \arg -> lispToExpr fun sort bound tps (UntypedExpr) Nothing arg

quantToExpr :: (forall a. Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool)
               -> FunctionParser -> SortParser
               -> (T.Text -> Maybe UntypedExpr)
               -> Map.Map TyCon DeclaredType -> [L.Lisp] -> L.Lisp -> Maybe (SMTExpr Bool)
quantToExpr q fun sort bound tps' (L.List [L.Symbol var,tp]:rest) body
  = let decl = declForSMTType tp tps'
        getForall :: Typeable a => a -> SMTExpr a -> SMTExpr a
        getForall = const id
    in Just $ withDeclaredType 
       (\u ann ->
         q ann $ \subst -> case quantToExpr q fun sort 
                                (\txt -> if txt==var
                                         then Just $ UntypedExpr $ getForall u subst
                                         else bound txt)
                                tps' rest body of
                             Just r -> r
                             Nothing -> error $ "smtlib2: Failed to parse quantifier construct "++show rest
                             ) decl
quantToExpr _ fun sort bound tps' [] body
  = lispToExpr fun sort bound tps' (\expr -> case gcast expr of 
                                       Nothing -> error "smtlib2: Body of existential quantification isn't bool."
                                       Just r -> r
                                   ) (Just $ toSort (undefined::Bool) ()) body
quantToExpr _ _ _ _ _ (el:_) _ = error $ "smtlib2: Invalid element "++show el++" in quantifier construct."

data LetStruct where
  LetStruct :: SMTType a => SMTAnnotation a -> SMTExpr a -> (SMTExpr a -> LetStruct) -> LetStruct
  EndLet :: SMTType a => SMTExpr a -> LetStruct

parseLetStruct :: FunctionParser -> SortParser
                  -> (T.Text -> Maybe UntypedExpr)
                  -> Map.Map TyCon DeclaredType
                  -> Maybe Sort
                  -> [L.Lisp] -> L.Lisp -> LetStruct
parseLetStruct fun sort bound tps expected (L.List [L.Symbol name,expr]:rest) arg
  = case lispToExpr fun sort bound tps
         (\expr' -> LetStruct (extractAnnotation expr') expr' $
                    \sym -> parseLetStruct fun sort
                            (\txt -> if txt==name
                                     then Just $ UntypedExpr expr'
                                     else bound txt) tps expected rest arg
                     ) Nothing expr of
      Nothing -> error $ "smtlib2: Failed to parse argument in let-expression "++show expr
      Just x -> x
parseLetStruct fun sort bound tps expected [] arg 
  = case lispToExpr fun sort bound tps EndLet expected arg of
    Nothing -> error $ "smtlib2: Failed to parse body of let-expression: "++show arg
    Just x -> x
parseLetStruct _ _ _ _ _ (el:_) _ = error $ "smtlib2: Invalid entry "++show el++" in let construct."

extractType :: (forall a. SMTType a => a -> b) -> LetStruct -> b
extractType f (EndLet x) = f (getUndef x)
extractType f (LetStruct ann x g) = extractType f (g $ error "smtlib2: Don't evaluate the argument to the let-function.")

convertLetStructT :: SMTType a => LetStruct -> SMTExpr a
convertLetStructT (EndLet x) = case gcast x of
  Just x' -> x'
convertLetStructT (LetStruct ann x g) = Let ann x (\sym -> convertLetStructT (g sym))

convertLetStruct :: (forall a. SMTType a => SMTExpr a -> b) -> LetStruct -> b
convertLetStruct f x 
  = extractType 
    (\(u::t) -> f (convertLetStructT x :: SMTExpr t)) x

withFirstArgSort :: L.Lisp -> Maybe [Sort] -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withFirstArgSort sym (Just (s:_)) f = withSort s f
withFirstArgSort sym (Just []) f = error $ "smtlib2: Function "++show sym++" needs at least one argument."
withFirstArgSort sym Nothing f = error $ "smtlib2: Must provide signature for overloaded symbol "++show sym

withAnySort :: L.Lisp -> Maybe [Sort] -> Maybe Sort -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withAnySort sym (Just (s:_)) _ f = withSort s f
withAnySort sym _ (Just s) f = withSort s f
withAnySort sym (Just []) _ f = error $ "smtlib2: Function "++show sym++" needs at least one argument."
withAnySort sym Nothing Nothing f = error $ "smtlib2: Must provide signature for overloaded symbol "++show sym

commonFunctions :: FunctionParser
commonFunctions = mconcat [eqParser
                          ,mapParser
                          ,ordOpParser
                          ,arithOpParser
                          ,minusParser
                          ,intArithParser
                          ,divideParser
                          ,absParser
                          ,logicParser
                          ,iteParser]

eqParser :: FunctionParser
eqParser = FunctionParser $ 
           \sym sort_arg _ rec f -> case sym of
             L.Symbol "=" -> withFirstArgSort sym sort_arg $
                             \(u::t) _ -> Just $ f (Eq :: SMTEq t)
             _ -> Nothing

mapParser :: FunctionParser
#ifdef SMTLIB2_WITH_CONSTRAINTS
mapParser = FunctionParser $
            \sym sort_arg sort_ret rec f -> case sym of
              L.List [L.Symbol "_"
                     ,L.Symbol "map"
                     ,fun] -> let idx_sort = case sort_arg of
                                    Nothing -> case sort_ret of
                                      Nothing -> [toSort (undefined::Integer) ()]
                                      Just (ArraySort i _) -> i
                                      Just _ -> error $ "smtlib2: map return value must be array."
                                    Just (ArraySort i _:_) -> i
                                    Just _ -> error $ "smtlib2: all map arguments must be arrays."
                                  arg_sorts = fmap 
                                              (fmap (\s -> case s of
                                                        ArraySort _ v -> v
                                                        _ -> error $ "smtlib2: all map arguments must be arrays."
                                                    )) sort_arg
                                  ret_sort = case sort_ret of
                                    Nothing -> Nothing
                                    Just (ArraySort _ v) -> Just v
                                    Just _ -> error $ "smtlib2: map return value must be array."
                              in parseFun rec fun arg_sorts ret_sort rec
                                 (\(fun' :: g) -> withArgSort idx_sort $
                                                  \(_::i) _
                                                  -> let res = SMTMap fun' :: SMTMap g i r
                                                     in case getConstraint (Proxy :: Proxy (SMTFunArg g,i)) of
                                                       Dict -> f res
                                 )
              _ -> Nothing
#else
mapParser = FunctionParser 
            $ \sym _ _ _ 
              -> case sym of
                L.List [L.Symbol "_"
                       ,L.Symbol "map"
                       ,_] -> error "smtlib2: Compile smtlib2 with -fWithConstraints to enable parsing of map functions"
#endif

ordOpParser :: FunctionParser
ordOpParser 
  = FunctionParser $
    \sym sort_arg _ rec f 
    -> case sym of
      L.Symbol ">=" -> withFirstArgSort sym sort_arg $ \(_::t) _ -> Just $ f (Ge::SMTOrdOp t)
      L.Symbol ">" -> withFirstArgSort sym sort_arg $ \(_::t) _ -> Just $ f (Gt::SMTOrdOp t)
      L.Symbol "<=" -> withFirstArgSort sym sort_arg $ \(_::t) _ -> Just $ f (Le::SMTOrdOp t)
      L.Symbol "<" -> withFirstArgSort sym sort_arg $ \(_::t) _ -> Just $ f (Lt::SMTOrdOp t)
      _ -> Nothing

arithOpParser :: FunctionParser
arithOpParser
  = FunctionParser $
    \sym sort_arg sort_ret rec f -> case sym of
      L.Symbol "+" -> withAnySort sym sort_arg sort_ret $ \(_::t) _ -> Just $ f (Plus::SMTArithOp t)
      L.Symbol "*" -> withAnySort sym sort_arg sort_ret $ \(_::t) _ -> Just $ f (Mult::SMTArithOp t)
      _ -> Nothing

minusParser :: FunctionParser
minusParser
  = FunctionParser $
    \sym sort_arg sort_ret rec f -> case sym of
      L.Symbol "-" -> case sort_arg of
        Just [s] -> withSort s $ \(_::t) _ -> Just $ f (Neg::SMTNeg t)
        Just (s:_) -> withSort s $ \(_::t) _ -> Just $ f (Minus::SMTMinus t)
        Nothing -> error $ "smtlib2: Must provide signature for overloaded symbol "++show sym
      _ -> Nothing

intArithParser :: FunctionParser
intArithParser
  = FunctionParser $
    \sym _ _ rec f -> case sym of
      L.Symbol "div" -> Just $ f Div
      L.Symbol "mod" -> Just $ f Mod
      L.Symbol "rem" -> Just $ f Rem
      _ -> Nothing

divideParser :: FunctionParser
divideParser
  = FunctionParser $
    \sym _ _ rec f -> case sym of
      L.Symbol "/" -> Just $ f Divide
      _ -> Nothing

absParser :: FunctionParser
absParser
  = FunctionParser $
    \sym sort_arg sort_ret rec f -> case sym of
      L.Symbol "abs" -> withAnySort sym sort_arg sort_ret $ \(_::t) _ -> Just $ f (Abs::SMTAbs t)
      _ -> Nothing

logicParser :: FunctionParser
logicParser
  = FunctionParser $
    \sym _ _ rec f -> case sym of
      L.Symbol "not" -> Just $ f Not
      L.Symbol "and" -> Just $ f And
      L.Symbol "or" -> Just $ f Or
      L.Symbol "xor" -> Just $ f XOr
      L.Symbol "=>" -> Just $ f Implies
      _ -> Nothing
                                     
iteParser :: FunctionParser
iteParser
  = FunctionParser $
    \sym sort_arg sort_ret _ f -> case sym of
      L.Symbol "ite" -> case sort_arg of
        Just [_,s,_] -> withSort s $ \(_::t) _ -> Just $ f (ITE :: SMTITE t)
        Just _ -> error "smtlib2: Wrong number of arguments to ite."
        Nothing -> case sort_ret of
          Just s -> withSort s $ \(_::t) _ -> Just $ f (ITE :: SMTITE t)
          Nothing -> error "smtlib2: Must provide signature for overloaded symbol ite."
      _ -> Nothing

instance (SMTValue a) => LiftArgs (SMTExpr a) where
  type Unpacked (SMTExpr a) = a
  liftArgs = Const
  unliftArgs = getValue
