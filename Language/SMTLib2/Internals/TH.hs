module Language.SMTLib2.Internals.TH where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Internals.Embed

import Data.Char
import Numeric
import Data.List (genericLength)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import qualified Language.Haskell.Meta as TH
import Data.Proxy
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (liftM2)
import Data.Maybe (catMaybes)

data BasicExpr = Atom String
               | List [BasicExpr]
               | HsExpr String
               deriving Show

data THType = DeterminedType Type
            | QueryType TH.ExpQ

liftNat :: Nat -> TH.ExpQ
liftNat Z = [| Zero |]
liftNat (S n) = [| Succ $(liftNat n) |]

liftNatType :: Nat -> TH.TypeQ
liftNatType Z = [t| 'Z |]
liftNatType (S n) = [t| 'S $(liftNatType n) |]

liftTypeRepr :: Type -> TH.ExpQ
liftTypeRepr BoolType = [| BoolRepr |]
liftTypeRepr IntType = [| IntRepr |]
liftTypeRepr RealType = [| RealRepr |]
liftTypeRepr (BitVecType bw) = [| BitVecRepr $(liftNat bw) |]
liftTypeRepr (ArrayType idx el)
  = [| ArrayRepr $(liftList $ fmap liftTypeRepr idx) $(liftTypeRepr el) |]

liftType' :: Type -> TH.TypeQ
liftType' BoolType = [t| 'BoolType |]
liftType' IntType = [t| 'IntType |]
liftType' RealType = [t| 'RealType |]
liftType' (BitVecType bw) = [t| 'BitVecType $(liftNatType bw) |]
liftType' (ArrayType idx el)
  = [t| ArrayType $(toArgs $ fmap liftType' idx) $(liftType' el) |]
  where
    toArgs :: [TH.TypeQ] -> TH.TypeQ
    toArgs [] = [t| '[] |]
    toArgs (x:xs) = [t| ( '(:) ) $(x) $(toArgs xs) |]

liftList :: [TH.ExpQ] -> TH.ExpQ
liftList [] = [| Nil |]
liftList (x:xs) = [| Cons $(x) $(liftList xs) |]

liftTHType :: THType -> TH.ExpQ
liftTHType (DeterminedType tp) = [| return $(liftTypeRepr tp) |]
liftTHType (QueryType q) = q

liftTHTypes :: [THType] -> TH.ExpQ
liftTHTypes [] = [| return Nil |]
liftTHTypes (tp:tps) = [| liftM2 Cons $(liftTHType tp) $(liftTHTypes tps) |]

liftNumType :: Type -> TH.ExpQ
liftNumType IntType = [| NumInt |]
liftNumType RealType = [| NumReal |]

natLength :: [a] -> Nat
natLength [] = Z
natLength (_:xs) = S (natLength xs)

natInt :: Integer -> Nat
natInt 0 = Z
natInt n = S (natInt (n-1))

data THFunction = THFun { deriveFunctionType :: (Maybe [Maybe THType],Maybe THType)
                                             -> (Maybe [Maybe THType],Maybe THType)
                        , getSymbol :: (Maybe [Maybe THType],Maybe THType) -> TH.ExpQ
                        , allEqSymbol :: TH.ExpQ
                        , match :: TH.PatQ }

data THExpression = THExpr { deriveType :: THType
                           , getExpr' :: TH.ExpQ }

type THBind = Map String THExpression

deriveAllEqType :: [THExpression] -> THType
deriveAllEqType args = case [ tp | THExpr { deriveType = DeterminedType tp } <- args
                                 ] of
  x:xs -> DeterminedType x
  [] -> case args of
    e:_ -> deriveType e
    [] -> error $ "Cannot use function with zero arguments."

toFunction :: BasicExpr -> THFunction
toFunction (Atom "=")
  = THFun { deriveFunctionType = \(args,_)
                                 -> (case args of
                                      Nothing -> Nothing
                                      Just tps -> Just $ case [ tp | Just tp <- tps ] of
                                        [] -> tps
                                        tps' -> case [ tp | DeterminedType tp <- tps' ] of
                                          [] -> fmap (const (Just (head tps'))) tps
                                          tp:_ -> fmap (const (Just (DeterminedType tp))) tps,
                                     Just (DeterminedType BoolType))
          , getSymbol = \(args,_) -> case args of
            Just xs@((Just tp):_)
              -> [| $(liftTHType tp) >>= \rtp -> return $ Eq rtp $(liftNat $ natLength xs) |]
          , allEqSymbol = [| eq' |]
          , match = [p| Eq _ _ |] }
toFunction (Atom "distinct")
  = THFun { deriveFunctionType = \(args,_)
                                 -> (case args of
                                      Nothing -> Nothing
                                      Just tps -> Just $ case [ tp | Just tp <- tps ] of
                                        [] -> tps
                                        tps' -> case [ tp | DeterminedType tp <- tps' ] of
                                          [] -> fmap (const (Just (head tps'))) tps
                                          tp:_ -> fmap (const (Just (DeterminedType tp))) tps,
                                     Just (DeterminedType BoolType))
          , getSymbol = \(args,_) -> case args of
            Just xs@((Just tp):_)
              -> [| $(liftTHType tp) >>= \rtp -> return $ Distinct rtp $(liftNat $ natLength xs) |]
          , allEqSymbol = [| distinct' |]
          , match = [p| Distinct _ _ |] }
toFunction (List [Atom "map",fun])
  = THFun { deriveFunctionType = deriv
          , getSymbol = sym
          , allEqSymbol = error "map function cannot be applied to list."
          , match = [p| Map _ $(match rfun) |]
          }
  where
    rfun = toFunction fun
    deriv (args,tp) = let nargs = case args of
                            Nothing -> Nothing
                            Just tps -> Just $ fmap (fmap thElementType) tps
                          ntp = fmap thElementType tp
                          all_tps = (case args of
                                      Nothing -> []
                                      Just tps -> catMaybes tps)++
                                    (case tp of
                                      Nothing -> []
                                      Just rtp -> [rtp])
                          all_idx = fmap thIndexType all_tps
                          idx = case [ tps | Left tps <- all_idx ] of
                            idx':_ -> Left idx'
                            [] -> case [ q | Right q <- all_idx ] of
                              idx':_ -> Right idx'
                              [] -> error "Cannot infer index type for map function."
                          (fargs,ftp) = deriveFunctionType rfun (nargs,ntp)
                      in (case fargs of
                           Nothing -> Nothing
                           Just tps -> Just $ fmap (fmap (thMakeArray idx)) tps,
                          case ftp of
                          Nothing -> Nothing
                          Just tp -> Just $ thMakeArray idx tp)
    sym :: (Maybe [Maybe THType],Maybe THType) -> TH.ExpQ
    sym (args,tp) = let all_tps = (case args of
                                    Nothing -> []
                                    Just tps -> catMaybes tps)++
                                  (case tp of
                                    Nothing -> []
                                    Just tp -> [tp])
                        all_idx = fmap thIndexType all_tps
                        idx = case [ tps | Left tps <- all_idx ] of
                            idx':_ -> Left idx'
                            [] -> case [ q | Right q <- all_idx ] of
                              idx':_ -> Right idx'
                              [] -> error "Cannot infer index type for map function."
                        fargs = case args of
                          Nothing -> Nothing
                          Just args' -> Just $ fmap (fmap thElementType) args'
                        ftp = case tp of
                          Nothing -> Nothing
                          Just tp' -> Just $ thElementType tp'
                    in [| liftM2 Map
                          $(case idx of
                             Left idx' -> liftTHTypes (fmap DeterminedType idx')
                             Right q -> q)
                          $(getSymbol rfun (fargs,ftp)) |]
toFunction (Atom "<=") = toOrd 'Le
toFunction (Atom "<") = toOrd 'Lt
toFunction (Atom ">=") = toOrd 'Ge
toFunction (Atom ">") = toOrd 'Gt
toFunction (Atom "+") = toArith 'Plus
toFunction (Atom "-") = toArith 'Minus
toFunction (Atom "*") = toArith 'Mult
toFunction (Atom "div") = toArithBin 'Div
toFunction (Atom "mod") = toArithBin 'Mod
toFunction (Atom "rem") = toArithBin 'Rem
toFunction (Atom "/") = THFun { deriveFunctionType = const (Just [Just (DeterminedType RealType)
                                                                 ,Just (DeterminedType RealType)],
                                                            Just (DeterminedType RealType))
                              , getSymbol = const [| return Divide |]
                              , allEqSymbol = error "Cannot apply / function to list."
                              , match = [p| Divide |] }
toFunction (Atom "abs")
  = THFun { deriveFunctionType = \(args,rtp) -> case args of
            Just [Just tp] -> case tp of
              DeterminedType _ -> (Just [Just tp],Just tp)
              _ -> case rtp of
                Just (DeterminedType tp) -> (Just [rtp],rtp)
                _ -> (Just [Just tp],Just tp)
            _ -> case rtp of
              Just tp -> (Just [Just tp],Just tp)
              Nothing -> (Just [Nothing],Nothing)
          , getSymbol = \(_,rtp) -> case rtp of
            Just (DeterminedType IntType) -> [| return $ Abs NumInt |]
            Just (DeterminedType RealType) -> [| return $ Abs NumReal |]
            Just (QueryType q) -> [| $(q) >>= \repr -> return $ Abs (case asNumRepr repr of
                                                                      Just r -> r) |]
          , allEqSymbol = error "Cannot apply abs function to list."
          , match = [p| Abs _ |] }
toFunction (Atom "not")
  = THFun { deriveFunctionType = \_ -> (Just [Just $ DeterminedType BoolType],
                                        Just (DeterminedType BoolType))
          , getSymbol = const [| return Not |]
          , allEqSymbol = error "Cannot apply not function to list."
          , match = [p| Not |] }
toFunction (Atom "and") = toLogic 'And
toFunction (Atom "or") = toLogic 'Or
toFunction (Atom "xor") = toLogic 'XOr
toFunction (Atom "=>") = toLogic 'Implies
toFunction (Atom "to_real")
  = THFun { deriveFunctionType = \_ -> (Just [Just $ DeterminedType IntType],
                                        Just (DeterminedType RealType))
          , getSymbol = const [| return ToReal |]
          , allEqSymbol = error "Cannot apply to-real function to list."
          , match = [p| ToReal |] }
toFunction (Atom "to_int")
  = THFun { deriveFunctionType = \_ -> (Just [Just $ DeterminedType RealType],
                                        Just (DeterminedType IntType))
          , getSymbol = const [| return ToInt |]
          , allEqSymbol = error "Cannot apply to-int function to list."
          , match = [p| ToInt |] }
toFunction (Atom "ite")
  = THFun { deriveFunctionType = deriv
          , getSymbol = sym
          , allEqSymbol = error "Cannot apply ite function to list."
          , match = [p| ITE _ |] }
  where
    deriv (args,rtp) = let all_tps = (case args of
                                       Just [_,tp1,tp2] -> catMaybes [tp1,tp2]
                                       Nothing -> [])++
                                     (case rtp of
                                       Just tp -> [tp]
                                       Nothing -> [])
                           res = case [ tp | DeterminedType tp <- all_tps ] of
                             tp:_ -> Just (DeterminedType tp)
                             [] -> case [ tp | QueryType tp <- all_tps ] of
                               tp:_ -> Just (QueryType tp)
                               [] -> rtp
                       in (Just [Just $ DeterminedType BoolType
                                ,res,res],res)
    sym (_,Just rtp) = [| fmap ITE $(liftTHType rtp) |]
toFunction (Atom "select")
  = THFun { deriveFunctionType = deriv
          , getSymbol = sym
          , allEqSymbol = error "Cannot apply select function to list."
          , match = [p| Select _ _ |] }
  where
    deriv (args,rtp) = case args of
      Just (arr:idx) -> case arr of
        Just (DeterminedType (ArrayType idx' el))
          -> (Just (arr:fmap (Just . DeterminedType) idx'),
              Just (DeterminedType el))
        _ -> (args,rtp)
      _ -> (args,rtp)
    sym (Just (Just arr:_),_)
      = [| liftM2 Select $(case thIndexType arr of
                            Left tps -> liftTHTypes (fmap DeterminedType tps)
                            Right q -> q)
           $(liftTHType $ thElementType arr) |]
toFunction (Atom "store")
  = THFun { deriveFunctionType = deriv
          , getSymbol = sym
          , allEqSymbol = error "Cannot apply store function to list."
          , match = [p| Store _ _ |] }
  where
    deriv (args,rtp) = case args of
      Just (arr:idx) -> case arr of
        Just (DeterminedType (ArrayType idx' el))
          -> (Just (arr:(fmap (Just . DeterminedType) idx')++[Just $ DeterminedType el]),
              Just (DeterminedType el))
        _ -> (args,rtp)
      _ -> (args,rtp)
    sym (Just (Just arr:_),_)
      = [| liftM2 Store
           $(case thIndexType arr of
              Left tps -> liftTHTypes (fmap DeterminedType tps)
              Right q -> q)
           $(liftTHType $ thElementType arr) |]
toFunction (List [Atom "as",Atom "const",List [Atom "Array",List idx,el]])
  = THFun { deriveFunctionType = \_ -> (Just [Just elTp],Just arrTp)
          , getSymbol = \_ -> [| liftM2 ConstArray
                                 $(liftTHTypes idxTps)
                                 $(liftTHType elTp) |]
          , allEqSymbol = error "Cannot apply constant array function to list."
          , match = [p| ConstArray _ _ |] }
  where
    idxTps = fmap toType idx
    elTp = toType el
    qarrTp = [| ArrayRepr $(liftList $ fmap liftTHType idxTps)
                $(liftTHType elTp) |]
                
    arrTp = case mapM (\tp -> case tp of
                        DeterminedType tp' -> Just tp'
                        _ -> Nothing) idxTps of
            Just idx' -> case elTp of
              DeterminedType el' -> DeterminedType (ArrayType idx' el')
              _ -> QueryType qarrTp
            Nothing -> QueryType qarrTp

toOrd :: TH.Name -> THFunction
toOrd name = THFun { deriveFunctionType = \(args,_)
                                          -> (case args of
                                               Nothing -> Nothing
                                               Just [t1,t2] -> Just $ case t1 of
                                                 Just (DeterminedType tp)
                                                   -> [Just (DeterminedType tp)
                                                      ,Just (DeterminedType tp)]
                                                 Just (QueryType q)
                                                   -> case t2 of
                                                   Just (DeterminedType tp)
                                                     -> [Just (DeterminedType tp)
                                                        ,Just (DeterminedType tp)]
                                                   _ -> [Just (QueryType q)
                                                        ,Just (QueryType q)]
                                                 Nothing -> [t2,t2],
                                              Just (DeterminedType BoolType))
                   , getSymbol = getSym
                   , allEqSymbol = error $ "Cannot dynamically apply comparison function."
                   , match = [p| Ord _ $(TH.conP name []) |] }
  where
    getSym (Just [Just tp,_],_)
      = case tp of
      DeterminedType tp' -> [| return $ Ord $(liftNumType tp') $(TH.conE name) |]
      QueryType q -> [| $(q) >>= \repr -> return $ Ord (case asNumRepr repr of
                                                         Just rtp -> rtp) $(TH.conE name) |]

toArith :: TH.Name -> THFunction
toArith name = THFun { deriveFunctionType = deriv
                     , getSymbol = sym
                     , allEqSymbol = [| arith' $(TH.conE name) |]
                     , match = [p| Arith _ $(TH.conP name []) _ |]
                     }
  where
    deriv :: (Maybe [Maybe THType],Maybe THType) -> (Maybe [Maybe THType],Maybe THType)
    deriv (args,rtp) = let all_tps = (case args of
                                       Just tps -> catMaybes tps
                                       Nothing -> [])++
                                     (case rtp of
                                       Just tp -> [tp]
                                       Nothing -> [])
                       in case [ tp | DeterminedType tp <- all_tps ] of
                       tp:_ -> (case args of
                                 Just args' -> Just $ fmap (const $ Just (DeterminedType tp)) args'
                                 Nothing -> Nothing,
                                Just $ DeterminedType tp)
                       [] -> case [ tp | QueryType tp <- all_tps ] of
                         tp:_ -> (case args of
                                   Just args' -> Just $ fmap (const $ Just (QueryType tp)) args'
                                   Nothing -> Nothing,
                                  Just $ QueryType tp)
                         [] -> (args,rtp)
    sym (Just args,Just (DeterminedType tp)) = [| return $ Arith $(case tp of
                                                                    IntType -> [| NumInt |]
                                                                    RealType -> [| NumReal |])
                                                  $(TH.conE name)
                                                  $(liftNat $ natLength args)
                                                |]
    sym (Just args,Just (QueryType q)) = [| $(q) >>= \repr -> return $
                                                              Arith (case asNumRepr repr of
                                                                      Just r -> r) $(TH.conE name)
                                                              $(liftNat $ natLength args) |]

toArithBin :: TH.Name -> THFunction
toArithBin name = THFun { deriveFunctionType = \_ -> (Just [Just (DeterminedType IntType)
                                                           ,Just (DeterminedType IntType)],
                                                      Just (DeterminedType IntType))
                        , getSymbol = \_ -> [| return $ ArithIntBin $(TH.conE name) |]
                        , allEqSymbol = error $ "Cannot apply binary function to list."
                        , match = [p| ArithIntBin $(TH.conP name []) |] }

toLogic :: TH.Name -> THFunction
toLogic name = THFun { deriveFunctionType = \(args,_)
                                            -> (fmap (fmap (const
                                                            (Just $ DeterminedType BoolType))) args,
                                                Just (DeterminedType BoolType))
                     , getSymbol = \(args,_) -> case args of
                       Just args' -> [| return $ Logic $(TH.conE name)
                                        $(liftNat $ natLength args') |]
                     , allEqSymbol = [| logic' $(TH.conE name) |]
                     , match = [p| Logic $(TH.conP name []) _ |] }

toExpression :: THBind -> BasicExpr -> THExpression
toExpression _ (Atom "false")
  = THExpr { deriveType = DeterminedType BoolType
           , getExpr' = [| embed (Const (BoolValue False)) |] }
toExpression _ (Atom "true")
  = THExpr { deriveType = DeterminedType BoolType
           , getExpr' = [| embed (Const (BoolValue True)) |] }
toExpression _ (Atom ('#':'x':rest)) = case [ num | (num,"") <- readHex rest ] of
  [n] -> let bw = genericLength rest*4
             natBW = natInt bw
         in THExpr { deriveType = DeterminedType (BitVecType natBW)
                   , getExpr' = [| embed (Const (BitVecValue $(TH.litE $ TH.integerL n)
                                                 $(liftNat natBW)
                                                )) |] }
toExpression _ (List [Atom "_",Atom ('b':'v':val),Atom bw])
  = let num = read val
        rbw = read bw
        natBW = natInt rbw
    in THExpr { deriveType = DeterminedType (BitVecType natBW)
              , getExpr' = [| embed (Const (BitVecValue $(TH.litE $ TH.integerL num)
                                            $(liftNat natBW))) |] }
toExpression _ (List [Atom "_",Atom "as-array",fun])
  = THExpr { deriveType = case funType of
             (Just (sequence -> Just tps),Just tp)
               -> case mapM (\tp -> case tp of
                              DeterminedType t -> Just t
                              _ -> Nothing
                            ) tps of
                  Just det -> case tp of
                    DeterminedType rdet -> DeterminedType (ArrayType det rdet)
           , getExpr' = [| $(getSymbol rfun funType) >>=
                           \sym -> embedSMT $ B.toBackend (AsArray sym) |] }
  where
    rfun = toFunction fun
    funType = deriveFunctionType rfun (Nothing,Nothing)
toExpression bind (List [Atom "forall",List vars,body])
  = toQuantifier Forall bind vars body
toExpression bind (List [Atom "exists",List vars,body])
  = toQuantifier Exists bind vars body
toExpression bind (Atom name)
  | isDigit (head name)
    = if '.' `elem` name
      then case [ res | (res,"") <- readFloat name ] of
        [r] -> THExpr { deriveType = DeterminedType RealType
                      , getExpr' = [| embed (Const (RealValue $(TH.litE $ TH.rationalL r))) |] }
      else let num = read name
           in THExpr { deriveType = DeterminedType IntType
                     , getExpr' = [| embed (Const (IntValue $(TH.litE $ TH.integerL num))) |] }
  | otherwise = case Map.lookup name bind of
      Just res -> res
      Nothing -> THExpr { deriveType = QueryType [| embedTypeOf $(TH.varE (TH.mkName name)) |]
                        , getExpr' = [| return $(TH.varE (TH.mkName name)) |] }
toExpression bind (List [List [Atom "is",Atom dt,Atom con],expr])
  = THExpr { deriveType = DeterminedType BoolType
           , getExpr' = TH.appsE [[| (>>=) |]
                                 , toExpr bind expr
                                 , [| embedConstrTest $(TH.litE $ TH.stringL con)
                                      (Proxy:: Proxy $(TH.conT $ TH.mkName dt)) |] ] }
toExpression bind (List [List [Atom "get",Atom dt,Atom con,Atom field,tp],expr])
  = THExpr { deriveType = toType tp
           , getExpr' = TH.appsE [[| (>>=) |]
                                 ,getExpr' $ toExpression bind expr
                                 ,[| embedGetField $(TH.litE $ TH.stringL field)
                                     $(TH.litE $ TH.stringL con)
                                     (Proxy:: Proxy $(TH.conT $ TH.mkName dt))
                                     $(liftTHType $ toType tp) |]] }
toExpression bind (List [Atom "const",HsExpr c])
  = THExpr { deriveType = QueryType [| return (valueTypeC $(e)) |]
           , getExpr' = TH.appE [| embedConst |] e }
  where
    e = case TH.parseExp c of
      Left err -> error $ "Failed to parse haskell expression: "++show c
      Right e' -> return e'
toExpression bind (List [fun,Atom "#",HsExpr e])
  = THExpr { deriveType = case deriveFunctionType rfun (Nothing,Nothing) of
             (_,Just rtp) -> rtp
           , getExpr' = case TH.parseExp e of
             Left err -> error $ "Failed to parse haskell expression: "++show e
             Right e' -> TH.appE (allEqSymbol rfun) (return e') }
  where
    rfun = toFunction fun
toExpression bind (List (fun:args))
  = THExpr { deriveType = case funType of
             (_,Just rtp) -> rtp
           , getExpr' = [| $(getSymbol rfun funType) >>=
                           \sym -> $(toArgs rargs) >>=
                                   embed . (App sym) |] }
  where
    rfun = toFunction fun
    rargs = fmap (toExpression bind) args
    funType = deriveFunctionType rfun (Just (fmap (Just . deriveType) rargs),Nothing)
    toArgs :: [THExpression] -> TH.ExpQ
    toArgs [] = [| return Nil |]
    toArgs (e:es) = [| liftM2 Cons $(getExpr' e) $(toArgs es) |]
toExpression bind (HsExpr expr) = case TH.parseExp expr of
  Left err -> error $ "Failed to parse haskell expression: "++show expr
  Right expr' -> THExpr { deriveType = QueryType [| embedTypeOf $(return expr') |]
                        , getExpr' = [| return $(return expr') |] }
  
toQuantifier :: Quantifier -> THBind -> [BasicExpr] -> BasicExpr -> THExpression
toQuantifier q bind vars body
  = THExpr { deriveType = DeterminedType BoolType
           , getExpr' = do
               let sig = toVarSig vars
               (pat,nbind) <- mkPat bind sig
               argTps <- mkTps sig
               TH.appsE [ [| embedQuantifier |]
                        , case q of
                          Forall -> [| Forall |]
                          Exists -> [| Exists |]
                        , mkTps sig
                        , TH.lamE [pat] (getExpr' $ toExpression nbind body)
                        ] }
  where
    mkPat bind [] = return ([p| Nil |],bind)
    mkPat bind ((var,tp):vars) = do
      qvar <- TH.newName "q"
      (pat,nbind) <- mkPat bind vars
      return (TH.conP 'Cons [TH.varP qvar,pat],
              Map.insert var (THExpr { deriveType = tp
                                     , getExpr' = [| embed (QVar $(TH.varE qvar)) |]
                                     }) nbind)
    mkTps [] = [| Nil |]
    mkTps ((_,tp):tps) = [| Cons $(case tp of
                                    DeterminedType t -> liftTypeRepr t
                                    QueryType q -> q)
                            $(mkTps tps) |]

parseList :: String -> Maybe ([BasicExpr],String)
parseList ((isSpace -> True):rest) = parseList rest
parseList (')':rest) = return ([],rest)
parseList rest = do
  (x,rest1) <- parseExpr rest
  (xs,rest2) <- parseList rest1
  return (x:xs,rest2)

parseExpr :: String -> Maybe (BasicExpr,String)
parseExpr ((isSpace -> True):rest) = parseExpr rest
parseExpr ('(':rest) = do
  (exprs,rest1) <- parseList rest
  return (List exprs,rest1)
parseExpr ('$':rest) = do
  (str,rest1) <- parseHs rest
  return (HsExpr str,rest1)
parseExpr rest = do
  (name,rest1) <- parseName rest
  if name==""
     then Nothing
     else return (Atom name,rest1)
parseExpr "" = Nothing

parseName :: String -> Maybe (String,String)
parseName (')':rest) = return ("",')':rest)
parseName ((isSpace -> True):rest) = return ("",rest)
parseName (x:xs) = do
  (name,xs') <- parseName xs
  return (x:name,xs')
parseName "" = return ("","")

parseHs :: String -> Maybe (String,String)
parseHs ('{':rest) = case break (=='}') rest of
  (expr,'}':rest1) -> return (expr,rest1)
  _ -> Nothing
parseHs rest = parseName rest

parseArgs :: String -> Maybe [BasicExpr]
parseArgs ((isSpace -> True):xs) = parseArgs xs
parseArgs "" = return []
parseArgs xs = do
  (expr,xs1) <- parseExpr xs
  exprs <- parseArgs xs1
  return $ expr:exprs

parseSingleExpr :: String -> Maybe BasicExpr
parseSingleExpr str = do
  (expr,rest) <- parseExpr str
  if all isSpace rest
    then return expr
    else Nothing

{-args :: QuasiQuoter
args = QuasiQuoter { quoteExp = quoteExpr
                   , quotePat = quotePattern
                   , quoteType = quoteTp
                   , quoteDec = \_ -> error "smtlb2: No support for argument declarations." }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = case parseArgs s of
      Nothing -> fail $ "Failed to parse arguments: "++s
      Just exprs -> toArgs exprs
    quotePattern :: String -> TH.PatQ
    quotePattern s = case parseArgs s of
      Nothing -> fail $ "Failed to parse argument pattern: "++s
      Just exprs -> mkArgsPat exprs
    quoteTp :: String -> TH.TypeQ
    quoteTp s = case parseArgs s of
      Nothing -> fail $ "Failed to parse argument type: "++s
      Just tps -> toTypes tps-}

-- | This quasiquoter can be used to generate SMTLib2 expressions or pattern matches.
--   For example, to assert the fact that variable @x@ is equal to variable @y@ we can use
--
--   > [expr| (= x y) |] >>= assert
--
--   To perform pattern matching against an expression @e@, we can use:
--
--   > analyze e >>= \re -> case re of
--   >   [expr| (+ x y) |] -> ...
--
--   Types can also be generated using for example:
--
--   > myExpr :: Backend b => SMT b (Expr b [expr| (Array Int Bool) |])
--   > myExpr = [expr| ((as const (Array Int Bool)) False) |]
expr :: QuasiQuoter
expr = QuasiQuoter { quoteExp = quoteExpr
                   , quotePat = quotePattern
                   , quoteType = quoteTp }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = case parseSingleExpr s of
      Nothing -> fail $ "Failed to parse expression: "++s
      Just expr -> toExpr Map.empty expr

    quotePattern :: String -> TH.PatQ
    quotePattern s = case parseSingleExpr s of
      Nothing -> fail $ "Failed to parse pattern: "++s
      Just expr -> toPat expr

    quoteTp :: String -> TH.TypeQ
    quoteTp s = case parseSingleExpr s of
      Nothing -> fail $ "Failed to parse type: "++s
      Just expr -> case toType expr of
        DeterminedType tp -> liftType' tp
        QueryType _ -> fail $ "Failed to parse type: "++s

declare :: QuasiQuoter
declare = QuasiQuoter { quoteExp = quoteExpr }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = case parseArgs s of
      Nothing -> fail $ "Failed to parse type: "++s
      Just [tp] -> [| $(liftTHType $ toType tp) >>=
                      \rtp -> embedSMT (B.declareVar rtp Nothing) >>=
                              embedSMT . B.toBackend . Var |]
      Just [List sig,tp]
        -> [| $(liftTHTypes rsig) >>=
              \argTp -> $(liftTHType rtp) >>=
                        \resTp -> fmap Fun (embedSMT $ B.declareFun argTp resTp Nothing) |]
        where
          rtp = toType tp
          rsig = fmap toType sig

define :: QuasiQuoter
define = QuasiQuoter { quoteExp = quoteExpr }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = case parseArgs s of
      Just [body] -> [| $(toExpr Map.empty body) >>=
                        embedSMT . (B.defineVar Nothing) >>=
                        embedSMT . B.toBackend . Var |]
      Just [List args,body] -> do
        let sig = toVarSig args
        toFunDef sig body Map.empty []

toFunDef :: [(String,THType)] -> BasicExpr
         -> THBind
         -> [TH.ExpQ]
         -> TH.ExpQ
toFunDef ((name,tp):args) body mp vec = do
  fv <- TH.newName "fv"
  fve <- TH.newName "fve"
  expr <- TH.varE fve
  TH.appE [| fmap Fun |] $
    TH.appE [| (>>=) (embedSMT (B.createFunArg $(liftTHType tp)
                                (Just $(TH.litE $ TH.stringL name)))) |]
            (TH.lamE [TH.varP fv]
             (TH.appE [| (>>=) (embedSMT (B.toBackend (FVar $(TH.varE fv)))) |]
              (TH.lamE [TH.varP fve]
                (toFunDef args body
                  (Map.insert name (THExpr tp (return expr)) mp)
                  (TH.varE fv:vec)))))
toFunDef [] body mp vec = do
  let args = foldl (\args e -> [| Cons $(e) $(args) |]) [| Nil |] vec
  [| $(toExpr mp body) >>= embedSMT . B.defineFun Nothing $(args) |]

entypeExpr :: Proxy (t::Type) -> e t -> e t
entypeExpr _ = id

toExpr :: THBind -> BasicExpr -> TH.ExpQ
toExpr bind e = getExpr' (toExpression bind e)

enforceTypes :: Proxy tps -> (List e tps -> a) -> (List e tps -> a)
enforceTypes _ = id

toVarSig :: [BasicExpr] -> [(String,THType)]
toVarSig = fmap (\(List [Atom name,tp]) -> (name,toType tp))

toQuant :: [(String,TH.Type)] -> Map String TH.Exp -> TH.Q (TH.Exp,Map String TH.Exp)
toQuant [] mp = do
  expr <- [| return Nil |]
  return (expr,mp)
toQuant ((name,tp):args) mp = do
  q <- TH.newName "q"
  (rest,nmp) <- toQuant args mp
  expr <- TH.varE q
  exp' <- [| do
               v <- embedSMT $ B.createQVar (Just name)
               vs <- $(return rest)
               return (Cons (v :: $(return tp)) vs) |]
  return (exp',Map.insert name expr nmp)

quantSig :: [(String,TH.Type)] -> TH.TypeQ
quantSig [] = TH.promotedNilT
quantSig ((_,tp):tps) = [t| $(return tp) ': $(quantSig tps) |]

asSig :: Proxy sig -> (List e sig -> a) -> (List e sig -> a)
asSig _ = id

-- fieldProxy :: FromSMT repr => (dt -> ValueType repr) -> Proxy repr
-- fieldProxy _ = Proxy

toPat :: BasicExpr -> TH.PatQ
toPat (Atom "false") = [p| AnalyzedExpr (Just (Const (BoolValue False))) _ |]
toPat (Atom "true") = [p| AnalyzedExpr (Just (Const (BoolValue True))) _|]
toPat (List [Atom "var",HsExpr bind]) = case TH.parsePat bind of
  Right pat -> [p| AnalyzedExpr (Just (Var $(return pat))) _ |]
  Left err -> error $ "While parsing pattern: "++show bind++": "++err
toPat (Atom ('#':'x':rest)) = case [ num | (num,"") <- readHex rest ] of
  [n] -> let bw = genericLength rest*4
         in [p| AnalyzedExpr
                (Just (Const $(TH.sigP
                               [p| BitVecValue $(TH.litP $ TH.integerL n) |]
                               [t| forall con. Value con (BitVecType $(mkNum bw)) |]))) _ |]
toPat (List [Atom "_",Atom ('b':'v':val),Atom bw])
  = let num = read val
        rbw = read bw
    in [p| AnalyzedExpr
           (Just (Const $(TH.sigP
                          [p| BitVecValue $(TH.litP $ TH.integerL num) |]
                          [t| forall con. Value con (BitVecType $(mkNum rbw)) |]))) _ |]
toPat (List [Atom "_",Atom "as-array",fun])
  = [p| AnalyzedExpr (Just (AsArray $(match rfun))) _ |]
  where
    rfun = toFunction fun
toPat (Atom name)
  | isDigit (head name) = let num = read name
                           in [p| AnalyzedExpr (Just (Const (IntValue $(TH.litP $ TH.integerL num)))) _ |]
  | otherwise = [p| AnalyzedExpr _ $(TH.varP (TH.mkName name)) |]
toPat (List (fun:args))
  = [p| AnalyzedExpr (Just (App $(match rfun) $(mkArgsPat args))) _ |]
  where
    rfun = toFunction fun
toPat (HsExpr e) = case TH.parsePat e of
  Left err -> error $ "While parsing pattern: "++show e++": "++err
  Right pat -> [p| AnalyzedExpr _ $(return pat) |]

eq' :: Embed m e => [e t] -> m (e BoolType)
eq' (x:xs) = do
  tp <- embedTypeOf x
  allEqFromList (x:xs) $
    \n args -> embed (App (Eq tp n) args)

distinct' :: Embed m e => [e t] -> m (e BoolType)
distinct' (x:xs) = do
  tp <- embedTypeOf x
  allEqFromList (x:xs) $
    \n args -> embed (App (Distinct tp n) args)

arith' :: (Embed m e,SMTArith t) => ArithOp -> [e t] -> m (e t)
arith' Plus [] = embedConst (arithFromInteger 0)
arith' Plus [x] = return x
arith' Minus [] = embedConst (arithFromInteger 0)
arith' Mult [] = embedConst (arithFromInteger 1)
arith' Mult [x] = return x
arith' op xs = allEqFromList xs $
               \n args -> embed (App (arith op n) args) 

logic' :: (Embed m e) => LogicOp -> [e BoolType] -> m (e BoolType)
logic' And [] = embedConst (BoolValueC True)
logic' And [x] = return x
logic' Or [] = embedConst (BoolValueC False)
logic' Or [x] = return x
logic' op xs = allEqFromList xs $
               \n args -> embed (App (Logic op n) args)

and' :: Embed m e => [e BoolType] -> m (e BoolType)
and' [] = embedConst (BoolValueC True)
and' [x] = return x
and' xs = allEqFromList xs $
          \n args -> embed (App (Logic And n) args)

or' :: Embed m e => [e BoolType] -> m (e BoolType)
or' [] = embedConst (BoolValueC False)
or' [x] = return x
or' xs = allEqFromList xs $
         \n args -> embed (App (Logic Or n) args)

xor' :: Embed m e => [e BoolType] -> m (e BoolType)
xor' xs = allEqFromList xs $
          \n args -> embed (App (Logic XOr n) args)

implies' :: Embed m e => [e BoolType] -> m (e BoolType)
implies' xs = allEqFromList xs $
              \n args -> embed (App (Logic Implies n) args)

plus' :: (Embed m e,SMTArith t) => [e t] -> m (e t)
plus' [] = embedConst (arithFromInteger 0)
plus' [x] = return x
plus' xs = allEqFromList xs $
           \n args -> embed (App (plus n) args)

minus' :: (Embed m e,SMTArith t) => [e t] -> m (e t)
minus' [] = embedConst (arithFromInteger 0)
minus' xs = allEqFromList xs $
            \n args -> embed (App (minus n) args)

mult' :: (Embed m e,SMTArith t) => [e t] -> m (e t)
mult' [] = embedConst (arithFromInteger 1)
mult' [x] = return x
mult' xs = allEqFromList xs $
           \n args -> embed (App (mult n) args)

toType :: BasicExpr -> THType
toType (Atom "Bool") = DeterminedType BoolType
toType (Atom "Int") = DeterminedType IntType
toType (Atom "Real") = DeterminedType RealType
toType (List [Atom "_",Atom "BitVec",Atom bw])
  = DeterminedType (BitVecType (natInt $ read bw))
toType (List [Atom "Array",List idx,el])
  = case (do
             idx'' <- mapM (\tp -> case tp of
                             DeterminedType t -> return t
                             _ -> Nothing
                           ) idx'
             el' <- case el' of
               DeterminedType t -> return t
               _ -> Nothing
             return (ArrayType idx'' el')) of
    Just rtp -> DeterminedType rtp
    Nothing -> QueryType [| liftM2 ArrayRepr
                            $(liftTHTypes idx')
                            $(liftTHType el') |]
  where
    idx' = fmap toType idx
    el' = toType el
toType (Atom name) = QueryType [| return $ DataRepr $ getDatatype
                                  (Proxy::Proxy $(TH.conT $ TH.mkName name)) |]

thElementType :: THType -> THType
thElementType (DeterminedType (ArrayType _ el)) = DeterminedType el
thElementType (QueryType q) = QueryType [| $(q) >>= \repr -> case repr of
                                          ArrayRepr _ el -> return el |]

thIndexType :: THType -> Either [Type] TH.ExpQ
thIndexType (DeterminedType (ArrayType idx _)) = Left idx
thIndexType (QueryType q) = Right [| $(q) >>= \repr -> case repr of
                                    ArrayRepr idx _ -> return idx |]

thMakeArray :: Either [Type] TH.ExpQ -> THType -> THType
thMakeArray (Left idx) (DeterminedType el) = DeterminedType (ArrayType idx el)
thMakeArray idx el
  = QueryType [| liftM2 ArrayRepr
                 $(case idx of
                    Left idx' -> liftTHTypes (fmap DeterminedType idx')
                    Right q -> q)
                 $(liftTHType el) |]

mkArgsPat :: [BasicExpr] -> TH.PatQ
mkArgsPat [] = [p| Nil |]
mkArgsPat (x:xs) = [p| Cons $(toPat x) $(mkArgsPat xs) |]

mkAllEqPat :: [BasicExpr] -> TH.PatQ
mkAllEqPat xs = TH.viewP [| allEqToList |]
                (TH.listP (fmap toPat xs))

mkNum :: Integer -> TH.TypeQ
mkNum 0 = [t| Z |]
mkNum n = [t| S $(mkNum (n-1)) |]
