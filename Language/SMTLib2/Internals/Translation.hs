{-# LANGUAGE RankNTypes,TypeFamilies,OverloadedStrings,GADTs,FlexibleContexts,ScopedTypeVariables,CPP,IncoherentInstances #-}
module Language.SMTLib2.Internals.Translation where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances
import Language.SMTLib2.Functions

import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Typeable
import Data.Text as T hiding (foldl1,head,zip)
import Data.Array
import qualified Data.Map as Map (Map,lookup,elems)
import Data.Monoid
import Data.Ratio

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
        (sargs,sres) = functionGetSignature f arg (inferResAnnotation f arg)
    in (L.List [L.Symbol "_",L.Symbol "as-array",if isOverloaded f
                                                 then L.List [f',L.List sargs,sres]
                                                 else f'],c)
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
exprToLisp (App fun x) c 
  = case optimizeCall fun x of
    Nothing -> let arg_ann = extractArgAnnotation x
                   l = getFunctionSymbol fun arg_ann
                   ~(x',c1) = unpackArgs (\e _ i -> exprToLisp e i) x
                              arg_ann c
               in if Prelude.null x'
                  then (l,c1)
                  else (L.List $ l:x',c1)
    Just res -> exprToLisp res c
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

newtype FunctionParser = FunctionParser { parseFun :: L.Lisp
                                                      -> FunctionParser
                                                      -> SortParser
                                                      -> Maybe FunctionParser' }

instance Monoid FunctionParser where
  mempty = FunctionParser $ \_ _ _ -> Nothing
  mappend p1 p2 = FunctionParser $ \l fun sort -> case parseFun p1 l fun sort of
    Nothing -> parseFun p2 l fun sort
    Just r -> Just r

data FunctionParser'
  = OverloadedParser { deriveRetSort :: [Sort] -> Maybe Sort
                     , parseOverloaded :: forall a. [Sort] -> Sort
                                          -> (forall f. SMTFunction f => f -> a)
                                          -> Maybe a }
  | DefinedParser { definedArgSig :: [Sort]
                  , definedRetSig :: Sort
                  , parseDefined :: forall a. (forall f. SMTFunction f => f -> a)
                                     -> Maybe a }

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
        L.List [L.Symbol "_",L.Symbol "as-array",fsym]
          -> case parseFun fun fsym fun sort of
          Nothing -> Nothing
          Just (DefinedParser arg_sort _ parse)
            -> parse $ \(rfun :: g) -> case getArgAnnotation (undefined::SMTFunArg g) arg_sort of
            (ann,[]) -> f (AsArray rfun ann)
            (_,_) -> error "smtlib2: Arguments not wholy parsed."
          Just _ -> error "smtlib2: as-array can't handle overloaded functions."
        L.List (fsym:args') -> case parseFun fun fsym fun sort of
          Nothing -> Nothing
          Just (OverloadedParser derive parse) 
            -> do
            nargs <- lispToExprs args'
            let arg_tps = fmap (entype $ \(expr::SMTExpr t) 
                                         -> toSort (undefined::t) (extractAnnotation expr)
                               ) nargs
            parse arg_tps
              (case derive arg_tps of
                  Nothing -> case expected of
                    Nothing -> error $ "smtlib2: Couldn't infer return type of "++show l
                    Just s -> s
                  Just s -> s) $
              \rfun -> case (do
                                (rargs,rest) <- toArgs nargs
                                case rest of
                                  [] -> Just $ App rfun rargs
                                  _ -> Nothing) of
                         Just e -> f e
                         Nothing -> error $ "smtlib2: Wrong arguments for function "++show fsym
          Just (DefinedParser arg_tps _ parse) -> do
            nargs <- mapM (\(el,tp) -> lispToExpr fun sort bound tps UntypedExpr (Just tp) el)
                     (zip args' arg_tps)
            parse $ \rfun -> case (do
                                      (rargs,rest) <- toArgs nargs
                                      case rest of
                                        [] -> Just $ App rfun rargs
                                        _ -> Nothing) of
                               Just e -> f e
                               Nothing -> error $ "smtlib2: Wrong arguments for function "++show fsym
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
                                     then Just $ UntypedExpr sym
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
extractType f (LetStruct _ _ g) = extractType f (g $ error "smtlib2: Don't evaluate the argument to the let-function.")

convertLetStructT :: SMTType a => LetStruct -> SMTExpr a
convertLetStructT (EndLet x) = case gcast x of
  Just x' -> x'
  Nothing -> error "smtlib2: Type error while converting let structure."
convertLetStructT (LetStruct ann x g) = Let ann x (\sym -> convertLetStructT (g sym))

convertLetStruct :: (forall a. SMTType a => SMTExpr a -> b) -> LetStruct -> b
convertLetStruct f x 
  = extractType 
    (\(_::t) -> f (convertLetStructT x :: SMTExpr t)) x

withFirstArgSort :: L.Lisp -> [Sort] -> (forall t. SMTType t => t -> SMTAnnotation t -> a) -> a
withFirstArgSort _ (s:_) f = withSort s f
withFirstArgSort sym [] _ = error $ "smtlib2: Function "++show sym++" needs at least one argument."

commonFunctions :: FunctionParser
commonFunctions = mconcat $ fmap FunctionParser 
                  [eqParser
                  ,mapParser
                  ,ordOpParser
                  ,arithOpParser
                  ,minusParser
                  ,intArithParser
                  ,divideParser
                  ,absParser
                  ,logicParser
                  ,iteParser
                  ,distinctParser
                  ,toRealParser
                  ,toIntParser
                  ,bvCompParser
                  ,bvBinOpParser
                  ,bvUnOpParser
                  ,selectParser
                  ,storeParser
                  ,constArrayParser
                  ,concatParser
                  ,extractParser
                  ,sigParser]

eqParser,
  mapParser,
  ordOpParser,
  arithOpParser,
  minusParser,
  intArithParser,
  divideParser,
  absParser,
  logicParser,
  iteParser,
  distinctParser,
  toRealParser,
  toIntParser,
  bvCompParser,
  bvBinOpParser,
  bvUnOpParser,
  selectParser,
  storeParser,
  constArrayParser,
  concatParser,
  extractParser,
  sigParser :: L.Lisp -> FunctionParser -> SortParser -> Maybe FunctionParser'
eqParser sym@(L.Symbol "=") _ _
  = Just $ OverloadedParser (const $ Just $ toSort (undefined::Bool) ()) $
    \sort_arg _ f -> withFirstArgSort sym sort_arg $
                     \(_::t) _ -> Just $ f (Eq :: SMTEq t)
eqParser _ _ _ = Nothing

mapParser (L.List [L.Symbol "_"
                  ,L.Symbol "map"
                  ,fun]) rec sort
#ifdef SMTLIB2_WITH_CONSTRAINTS
  = case parseFun rec fun rec sort of
    Nothing -> Nothing
    Just (DefinedParser _ ret_sig parse)
      -> Just $ OverloadedParser 
        { deriveRetSort = \arg -> case arg of
             ArraySort i _:_ -> Just (ArraySort i ret_sig)
             _ -> error "smtlib2: map function must have arrays as arguments."
        , parseOverloaded = \_ ret f
                             -> let idx_sort = case ret of
                                      ArraySort i _ -> i
                                      _ -> error "smtlib2: map function must have arrays as return type."
                                in parse $ \(fun' :: g) 
                                           -> withArgSort idx_sort $
                                              \(_::i) _ -> let res = SMTMap fun' :: SMTMap g i r
                                                           in case getConstraint (Proxy :: Proxy (SMTFunArg g,i)) of
                                                             Dict -> f res
        }
    Just _ -> error "smtlib2: map function can't handle overloaded functions."
#else
  = Just $ error "smtlib2: Compile smtlib2 with -fWithConstraints to enable parsing of map functions"
#endif
mapParser _ _ _ = Nothing

ordOpParser sym _ _
  = case sym of
      L.Symbol ">=" -> p Ge
      L.Symbol ">" -> p Gt
      L.Symbol "<=" -> p Le
      L.Symbol "<" -> p Lt
      _ -> Nothing
  where
    p :: (forall g. SMTOrdOp g) -> Maybe FunctionParser'
    p op = Just $ OverloadedParser (const $ Just $ toSort (undefined::Bool) ()) $
           \sort_arg _ f -> withFirstArgSort sym sort_arg $ \(_::t) _ -> Just $ f (op::SMTOrdOp t)

arithOpParser sym _ _
  = case sym of
    L.Symbol "+" -> Just $ OverloadedParser (\sorts -> Just (head sorts)) $
                    \_ sort_ret f
                    -> withSort sort_ret $ \(_::t) _ -> Just $ f (Plus::SMTArithOp t)
    L.Symbol "*" -> Just $ OverloadedParser (\sorts -> Just (head sorts)) $
                    \_ sort_ret f
                    -> withSort sort_ret $ \(_::t) _ -> Just $ f (Mult::SMTArithOp t)
    _ -> Nothing

minusParser (L.Symbol "-") _ _
  = Just $ OverloadedParser  (\sorts -> Just (head sorts)) $
    \sort_arg _ f -> case sort_arg of
      [] -> error "smtlib2: minus function needs at least one argument"
      [s] -> withSort s $ \(_::t) _ -> Just $ f (Neg::SMTNeg t)
      (s:_) -> withSort s $ \(_::t) _ -> Just $ f (Minus::SMTMinus t)
minusParser _ _ _ = Nothing

intArithParser (L.Symbol "div") _ _
  = Just $ DefinedParser 
    [toSort (undefined::Integer) ()
    ,toSort (undefined::Integer) ()]
    (toSort (undefined::Integer) ()) $ \f -> Just $ f Div
intArithParser (L.Symbol "mod") _ _
  = Just $ DefinedParser 
    [toSort (undefined::Integer) ()
    ,toSort (undefined::Integer) ()]
    (toSort (undefined::Integer) ()) $ \f -> Just $ f Mod
intArithParser (L.Symbol "rem") _ _
  = Just $ DefinedParser
    [toSort (undefined::Integer) ()
    ,toSort (undefined::Integer) ()]
    (toSort (undefined::Integer) ()) $ \f -> Just $ f Rem
intArithParser _ _ _ = Nothing

divideParser (L.Symbol "/") _ _
  = Just $ DefinedParser [toSort (undefined::Ratio Integer) ()
                         ,toSort (undefined::Ratio Integer) ()]
    (toSort (undefined::Ratio Integer) ()) $ \f -> Just $ f Divide
divideParser _ _ _ = Nothing

absParser (L.Symbol "abs") _ _
  = Just $ OverloadedParser (\sorts -> Just $ head sorts) $
    \_ sort_ret f 
    -> withSort sort_ret $ \(_::t) _ -> Just $ f (Abs::SMTAbs t)
absParser _ _ _ = Nothing

logicParser (L.Symbol "not") _ _ = Just $ DefinedParser [toSort (undefined::Bool) ()] (toSort (undefined::Bool) ()) 
                                   $ \f -> Just $ f Not
logicParser (L.Symbol "and") _ _ = Just $ OverloadedParser 
                                   (const $ Just $ toSort (undefined::Bool) ())
                                 $ \_ _ f -> Just $ f And
logicParser (L.Symbol "or") _ _ = Just $ OverloadedParser 
                                  (const $ Just $ toSort (undefined::Bool) ())
                                 $ \_ _ f -> Just $ f Or
logicParser (L.Symbol "xor") _ _ = Just $ OverloadedParser 
                                   (const $ Just $ toSort (undefined::Bool) ())
                                   $ \_ _ f -> Just $ f XOr
logicParser (L.Symbol "=>") _ _ = Just $ OverloadedParser 
                                  (const $ Just $ toSort (undefined::Bool) ())
                                  $ \_ _ f -> Just $ f Implies
logicParser _ _ _ = Nothing

distinctParser sym@(L.Symbol "distinct") _ _
  = Just $ OverloadedParser
    (const $ Just $ toSort (undefined::Bool) ()) $
    \sort_arg _ f -> withFirstArgSort sym sort_arg $ \(_::t) _ -> Just $ f (Distinct::SMTDistinct t)
distinctParser _ _ _ = Nothing

toRealParser (L.Symbol "to_real") _ _
  = Just $ DefinedParser [toSort (undefined::Integer) ()] (toSort (undefined::Ratio Integer) ()) $
    \f -> Just $ f ToReal
toRealParser _ _ _ = Nothing

toIntParser (L.Symbol "to_int") _ _
  = Just $ DefinedParser [toSort (undefined::Ratio Integer) ()] (toSort (undefined::Integer) ()) $
    \f -> Just $ f ToInt
toIntParser _ _ _ = Nothing

iteParser (L.Symbol "ite") _ _
  = Just $ OverloadedParser
    (\sorts -> case sorts of
        [_,s,_] -> Just s
        _ -> error "smtlib2: Wrong number of arguments to ite.") $
    \_ sort_ret f -> withSort sort_ret $ \(_::t) _ -> Just $ f (ITE :: SMTITE t)
iteParser _ _ _ = Nothing

bvCompParser sym _ _ = case sym of
  L.Symbol "bvule" -> p BVULE
  L.Symbol "bvult" -> p BVULT
  L.Symbol "bvuge" -> p BVUGE
  L.Symbol "bvugt" -> p BVSLE
  L.Symbol "bvsle" -> p BVSLE
  L.Symbol "bvslt" -> p BVSLT
  L.Symbol "bvsge" -> p BVSGE
  L.Symbol "bvsgt" -> p BVSGT
  _ -> Nothing
  where
    p :: (forall g. SMTBVComp g) -> Maybe FunctionParser'
    p op = Just $ OverloadedParser (const $ Just $ toSort (undefined::Bool) ()) $
           \sort_arg _ f -> case sort_arg of
#ifdef SMTLIB2_WITH_DATAKINDS
             (BVSort i:_) -> reifyNat i $ \(_::Proxy n) -> Just $ f (op::SMTBVComp (BVTyped n))
#else
             (BVSort i:_) -> reifyNat i $ \(_::n) -> Just $ f (op::SMTBVComp (BVTyped n))
#endif
             _ -> error "smtlib2: Bitvector comparision needs bitvector arguments."

bvBinOpParser sym _ _ = case sym of
  L.Symbol "bvadd" -> p BVAdd
  L.Symbol "bvsub" -> p BVSub
  L.Symbol "bvmul" -> p BVMul
  L.Symbol "bvurem" -> p BVURem
  L.Symbol "bvsrem" -> p BVSRem
  L.Symbol "bvudiv" -> p BVUDiv
  L.Symbol "bvsdiv" -> p BVSDiv
  L.Symbol "bvshl" -> p BVSHL
  L.Symbol "bvlshr" -> p BVLSHR
  L.Symbol "bvashr" -> p BVASHR
  L.Symbol "bvxor" -> p BVXor
  L.Symbol "bvand" -> p BVAnd
  L.Symbol "bvor" -> p BVOr
  _ -> Nothing
  where
    p :: (forall g. SMTBVBinOp g) -> Maybe FunctionParser'
    p op = Just $ OverloadedParser (Just . head) $
           \_ sort_ret f -> case sort_ret of 
#ifdef SMTLIB2_WITH_DATAKINDS
              BVSort i -> reifyNat i (\(_::Proxy n) -> Just $ f (op::SMTBVBinOp (BVTyped n)))
#else
              BVSort i -> reifyNat i (\(_::n) -> Just $ f (op::SMTBVBinOp (BVTyped n)))
#endif
              _ -> Nothing

bvUnOpParser (L.Symbol "bvnot") _ _
  = Just $ OverloadedParser (Just . head) $
    \_ sort_ret f -> case sort_ret of
#ifdef SMTLIB2_WITH_DATAKINDS
      BVSort i -> reifyNat i $ \(_::Proxy n) -> Just $ f (BVNot::SMTBVUnOp (BVTyped n))
#else
      BVSort i -> reifyNat i $ \(_::n) -> Just $ f (BVNot::SMTBVUnOp (BVTyped n))
#endif
      _ -> Nothing
bvUnOpParser (L.Symbol "bvneg") _ _
  = Just $ OverloadedParser (Just . head) $
    \_ sort_ret f -> case sort_ret of
#ifdef SMTLIB2_WITH_DATAKINDS
      BVSort i -> reifyNat i $ \(_::Proxy n) -> Just $ f (BVNeg::SMTBVUnOp (BVTyped n))
#else
      BVSort i -> reifyNat i $ \(_::n) -> Just $ f (BVNeg::SMTBVUnOp (BVTyped n))
#endif
      _ -> Nothing
bvUnOpParser _ _ _ = Nothing

selectParser (L.Symbol "select") _ _
  = Just $ OverloadedParser (\sort_arg -> case sort_arg of
                                (ArraySort _ vsort:_) -> Just vsort
                                _ -> error "smtlib2: Wrong arguments for select function.") $
    \sort_arg sort_ret f -> case sort_arg of
      (ArraySort isort1 _:_) -> withArgSort isort1 $ 
                                \(_::i) _ -> withSort sort_ret $ 
                                             \(_::v) _ -> Just $ f (Select::SMTSelect i v)
      _ -> error "smtlib2: Wrong arguments for select function."
selectParser _ _ _ = Nothing

storeParser (L.Symbol "store") _ _
  = Just $ OverloadedParser (\sort_arg -> case sort_arg of
                                s:_ -> Just s
                                _ -> error "smtlib2: Wrong arguments for store function.") $
    \_ sort_ret f -> case sort_ret of
      ArraySort idx val -> withArraySort idx val $ \(_::SMTArray i v) _ -> Just $ f (Store::SMTStore i v)
      _ -> error "smtlib2: Wrong arguments for store function."
storeParser _ _ _ = Nothing

constArrayParser (L.List [L.Symbol "as"
                         ,L.Symbol "const"
                         ,s]) _ sort
  = case parseSort sort s sort of
    Just rsort@(ArraySort idx val)
      -> Just $ DefinedParser [val] rsort $
         \f -> withArraySort idx val $
               \(_::SMTArray i v) (i_ann,_) 
               -> Just $ f (ConstArray i_ann::SMTConstArray i v)
    _ -> Nothing
constArrayParser _ _ _ = Nothing

concatParser (L.Symbol "concat") _ _
  = Just $ OverloadedParser 
    (\args' -> Just $ BVSort (sum $ fmap (\(BVSort i) -> i) args'))
    (\sort_arg _ f -> case sort_arg of
        [BVSort i1,BVSort i2]
          -> reifySum i1 i2 $
#ifdef SMTLIB2_WITH_DATAKINDS
             \(_::Proxy n1) (_::Proxy n2) _ 
#else
             \(_::n1) (_::n2) _
#endif
             -> Just $ f (BVConcat::SMTConcat (BVTyped n1) (BVTyped n2))
        _ -> Nothing)
concatParser _ _ _ = Nothing

extractParser (L.List [L.Symbol "_"
                      ,L.Symbol "extract"
                      ,L.Number (L.I u)
                      ,L.Number (L.I l)]) _ _
  = Just $ OverloadedParser
    (\args' -> case args' of
        [BVSort t] -> if u < t && l >= 0 && l <= u
                      then Just $ BVSort (u-l+1)
                      else error "smtlib2: Invalid parameters for extract."
        _ -> error "smtlib2: Invalid parameters for extract.")
    (\sort_arg sort_ret f -> case sort_arg of
        [BVSort t] -> case sort_ret of
          BVSort r -> if r+l == u+1
                      then reifyNat l $
#ifdef SMTLIB2_WITH_DATAKINDS
                           \(_::Proxy start)
                            -> reifyNat (u-l+1) $
                               \(_::Proxy len)
                                -> reifyNat t $
                                   \(_::Proxy tp)
#else
                           \(_::start)
                            -> reifyNat (u-l+1) $
                               \(_::len)
                                -> reifyNat t $
                                   \(_::tp)
#endif
                                    -> Just $ f (BVExtract::SMTExtract (BVTyped tp) start len)
                      else error "smtlib2: Invalid parameters for extract."
          _ -> error "smtlib2: Wrong return type for extract."
        _ -> error "smtlib2: Wrong argument type for extract.")
extractParser _ _ _ = Nothing

sigParser (L.List [fsym,L.List sig,ret]) rec sort = do
  rsig <- mapM (\l -> parseSort sort l sort) sig
  rret <- parseSort sort ret sort
  parser <- parseFun rec fsym rec sort
  return $ DefinedParser rsig rret $
    \f -> case parser of
      OverloadedParser _ parse -> parse rsig rret f
      DefinedParser _ _ parse -> parse f
sigParser _ _ _ = Nothing

instance (SMTValue a) => LiftArgs (SMTExpr a) where
  type Unpacked (SMTExpr a) = a
  liftArgs = Const
  unliftArgs = getValue
