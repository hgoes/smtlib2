{-# LANGUAGE TemplateHaskell,ViewPatterns #-}
module Language.SMTLib2.Internals.TH where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Expression
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.LowLevel

import Data.Char
import Numeric
import Data.List (genericLength)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Data.Proxy
import Data.Map (Map)
import qualified Data.Map as Map

data BasicExpr = Atom String
               | List [BasicExpr]
               deriving Show

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

args :: QuasiQuoter
args = QuasiQuoter { quoteExp = quoteExpr }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = case parseArgs s of
      Nothing -> fail $ "Failed to parse arguments: "++s
      Just exprs -> toArgs exprs

expr :: QuasiQuoter
expr = QuasiQuoter { quoteExp = quoteExpr
                   , quotePat = quotePattern }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = case parseSingleExpr s of
      Nothing -> fail $ "Failed to parse expression: "++s
      Just expr -> toExpr Map.empty expr

    quotePattern :: String -> TH.PatQ
    quotePattern s = case parseSingleExpr s of
      Nothing -> fail $ "Failed to parse pattern: "++s
      Just expr -> toPat expr

declare :: QuasiQuoter
declare = declare' Nothing

declare' :: Maybe (TH.TypeQ -> TH.TypeQ) -> QuasiQuoter
declare' expr = QuasiQuoter { quoteExp = quoteExpr }
  where
    quoteExpr :: String -> TH.ExpQ
    quoteExpr s = do
      b <- TH.newName "b"
      case parseArgs s of
        Nothing -> fail $ "Failed to parse type: "++s
        Just [tp] -> case expr of
          Nothing -> do
            e <- TH.newName "e"
            TH.sigE [| var |] [t| forall e. Embed e => SMT (EmbedBackend e) (e $(toType tp)) |]
          Just exprName -> do
            TH.sigE [| var |] (exprName (toType tp))
        Just [List sig,tp] -> do
          TH.sigE [| fun |] [t| forall b con field. Backend b => SMT b (Function (B.Fun b) con field '( $(toTypes sig),$(toType tp))) |]

toArgs :: [BasicExpr] -> TH.ExpQ
toArgs [] = [| NoArg |]
toArgs (x:xs) = [| Arg $(toExpr Map.empty x) $(toArgs xs) |]

toExpr :: Map String TH.Exp -> BasicExpr -> TH.ExpQ
toExpr _ (Atom "false") = [| embed (Const (BoolValue False)) |]
toExpr _ (Atom "true") = [| embed (Const (BoolValue True)) |]
toExpr _ (Atom ('#':'x':rest)) = case [ num | (num,"") <- readHex rest ] of
  [n] -> let bw = genericLength rest*4
         in [| embed (Const (BitVecValue $(TH.litE $ TH.integerL n) :: Value con (BitVecType $(mkNum bw)))) |]
toExpr _ (List [Atom "_",Atom ('b':'v':val),Atom bw])
  = let num = read val
        rbw = read bw
    in [| embed (Const (BitVecValue $(TH.litE $ TH.integerL num) :: Value con (BitVecType $(mkNum rbw)))) |]
toExpr _ (List [Atom "_",Atom "as-array",fun]) = [| embed (AsArray $(toFun fun)) |]
toExpr bind (Atom name)
  | isDigit (head name) = let num = read name
                           in [| embed (Const (IntValue $(TH.litE $ TH.integerL num))) |]
  | otherwise = case Map.lookup name bind of
      Just res -> return res
      Nothing -> TH.varE (TH.mkName name)
toExpr bind (List [Atom "forall",List vars,body])
  = toQuantifier Forall bind vars body
toExpr bind (List [Atom "exists",List vars,body])
  = toQuantifier Exists bind vars body
toExpr bind (List [List [Atom "is",Atom dt,Atom con],expr])
  = [| SpecialExpr $ TestConstr $(TH.litE $ TH.stringL con)
                                (Proxy::Proxy $(TH.conT $ TH.mkName dt))
                                $(toExpr bind expr) |]
toExpr bind (List [List [Atom "get",Atom dt,Atom con,Atom field],expr])
  = [| SpecialExpr $ GetField $(TH.litE $ TH.stringL field)
                              $(TH.litE $ TH.stringL con)
                              (Proxy::Proxy $(TH.conT $ TH.mkName dt))
                              (fieldProxy $(TH.varE $ TH.mkName field))
                              $(toExpr bind expr) |]
toExpr bind (List (name:args)) = [| app $(toFun name) $(mkArgs bind args) |]

toQuantifier :: Quantifier -> Map String TH.Exp -> [BasicExpr] -> BasicExpr -> TH.ExpQ
toQuantifier q bind vars body = do
  sig <- toVarSig vars
  (pat,bind') <- toQuant sig bind
  [| embedQuantifier $(case q of
                         Forall -> [| Forall |]
                         Exists -> [| Exists |])
      (asSig (Proxy::Proxy $(quantSig sig)) $(TH.lamE [return pat] (toExpr bind' body))) |]

toVarSig :: [BasicExpr] -> TH.Q [(String,TH.Type)]
toVarSig = mapM (\(List [Atom name,tp]) -> do
                   tp' <- toType tp
                   return (name,tp')
                )

toQuant :: [(String,TH.Type)] -> Map String TH.Exp -> TH.Q (TH.Pat,Map String TH.Exp)
toQuant [] mp = do
  pat <- [p| NoArg |]
  return (pat,mp)
toQuant ((name,tp):args) mp = do
  q <- TH.newName "q"
  (pat,nmp) <- toQuant args mp
  expr <- TH.varE q
  pat' <- [p| Arg $(TH.varP q) $(return pat) |]
  return (pat',Map.insert name expr nmp)

quantSig :: [(String,TH.Type)] -> TH.TypeQ
quantSig [] = TH.promotedNilT
quantSig ((_,tp):tps) = [t| $(return tp) ': $(quantSig tps) |]

asSig :: Proxy sig -> (Args e sig -> a) -> (Args e sig -> a)
asSig _ = id

fieldProxy :: SMTValue tp repr => (dt -> tp) -> Proxy repr
fieldProxy _ = Proxy

toPat :: BasicExpr -> TH.PatQ
toPat (Atom "false") = [p| Const (BoolValue False) |]
toPat (Atom "true") = [p| Const (BoolValue True) |]
toPat (Atom ('#':'x':rest)) = case [ num | (num,"") <- readHex rest ] of
  [n] -> let bw = genericLength rest*4
         in TH.conP (TH.mkName "Const")
                    [TH.sigP [p| BitVecValue $(TH.litP $ TH.integerL n) |]
                             [t| forall con. Value con (BitVecType $(mkNum bw)) |]]
toPat (List [Atom "_",Atom ('b':'v':val),Atom bw])
  = let num = read val
        rbw = read bw
    in TH.conP (TH.mkName "Const")
               [TH.sigP [p| BitVecValue $(TH.litP $ TH.integerL num) |]
                        [t| forall con. Value con (BitVecType $(mkNum rbw)) |]]
toPat (List [Atom "_",Atom "as-array",fun]) = [p| AsArray $(toFunPat fun) |]
toPat (Atom name)
  | isDigit (head name) = let num = read name
                           in [p| Const (IntValue $(TH.litP $ TH.integerL num)) |]
  | otherwise = TH.varP (TH.mkName name)
toPat (List (name:args))
  = if funIsAllEq name
    then [p| App $(toFunPat name) $(mkAllEqPat args) |]
    else [p| App $(toFunPat name) $(mkArgsPat args) |]

data FunName = FunCon TH.Name [FunName]
             | FunVar TH.Name
             | FunSig FunName TH.TypeQ
             | FunInt Integer

funNameToExpr :: FunName -> TH.ExpQ
funNameToExpr (FunCon name xs) = mk (TH.conE name) xs
  where
    mk c [] = c
    mk c (x:xs) = mk (TH.appE c (funNameToExpr x)) xs
funNameToExpr (FunVar name) = TH.varE name
funNameToExpr (FunSig f sig) = TH.sigE (funNameToExpr f) sig
funNameToExpr (FunInt n) = TH.litE $ TH.integerL n

funNameToPattern :: FunName -> TH.PatQ
funNameToPattern (FunCon name xs) = TH.conP name (fmap funNameToPattern xs)
funNameToPattern (FunVar _) = fail "smtlib2: Cannot use overloaded functions in patterns."
funNameToPattern (FunSig f sig) = TH.sigP (funNameToPattern f) sig
funNameToPattern (FunInt n) = TH.litP $ TH.integerL n

funIsAllEq :: BasicExpr -> Bool
funIsAllEq (Atom "=") = True
funIsAllEq (Atom "distinct") = True
funIsAllEq (Atom "and") = True
funIsAllEq (Atom "or") = True
funIsAllEq (Atom "xor") = True
funIsAllEq (Atom "=>") = True
funIsAllEq (Atom "+") = True
funIsAllEq (Atom "-") = True
funIsAllEq (Atom "*") = True
funIsAllEq _ = False

funName :: BasicExpr -> Maybe FunName
funName (List [name,List sig,tp]) = do
  f <- funName name
  return $ FunSig f [t| forall fun con field. Function fun con field '( $(toTypes sig),$(toType tp)) |]
funName (Atom "=") = Just $ FunCon 'Eq []
funName (Atom "distinct") = Just $ FunCon 'Distinct []
funName (List [Atom "_",Atom "map",f]) = do
  f' <- funName f
  return (FunCon 'Map [f'])
funName (Atom "<") = Just $ FunVar 'lt
funName (Atom "<=") = Just $ FunVar 'le
funName (Atom ">") = Just $ FunVar 'gt
funName (Atom ">=") = Just $ FunVar 'ge
funName (Atom "+") = Just $ FunVar 'plus
funName (Atom "-") = Just $ FunVar 'minus
funName (Atom "*") = Just $ FunVar 'mult
funName (Atom "div") = Just $ FunCon 'ArithIntBin [FunCon 'Div []]
funName (Atom "mod") = Just $ FunCon 'ArithIntBin [FunCon 'Mod []]
funName (Atom "rem") = Just $ FunCon 'ArithIntBin [FunCon 'Rem []]
funName (Atom "/") = Just $ FunCon 'Divide []
funName (Atom "abs") = Just $ FunVar 'abs'
funName (Atom "not") = Just $ FunCon 'Not []
funName (Atom "and") = Just $ FunCon 'Logic [FunCon 'And []]
funName (Atom "or") = Just $ FunCon 'Logic [FunCon 'Or []]
funName (Atom "xor") = Just $ FunCon 'Logic [FunCon 'XOr []]
funName (Atom "=>") = Just $ FunCon 'Logic [FunCon 'Implies []]
funName (Atom "to-real") = Just $ FunCon 'ToReal []
funName (Atom "to-int") = Just $ FunCon 'ToInt []
funName (Atom "ite") = Just $ FunCon 'ITE []
funName (Atom "bvule") = Just $ FunCon 'BVComp [FunCon 'BVULE []]
funName (Atom "bvult") = Just $ FunCon 'BVComp [FunCon 'BVULT []]
funName (Atom "bvuge") = Just $ FunCon 'BVComp [FunCon 'BVUGE []]
funName (Atom "bvugt") = Just $ FunCon 'BVComp [FunCon 'BVUGT []]
funName (Atom "bvsle") = Just $ FunCon 'BVComp [FunCon 'BVSLE []]
funName (Atom "bvslt") = Just $ FunCon 'BVComp [FunCon 'BVSLT []]
funName (Atom "bvsge") = Just $ FunCon 'BVComp [FunCon 'BVSGE []]
funName (Atom "bvsgt") = Just $ FunCon 'BVComp [FunCon 'BVSGT []]
funName (Atom "bvadd") = Just $ FunCon 'BVBin [FunCon 'BVAdd []]
funName (Atom "bvsub") = Just $ FunCon 'BVBin [FunCon 'BVSub []]
funName (Atom "bvmul") = Just $ FunCon 'BVBin [FunCon 'BVMul []]
funName (Atom "bvurem") = Just $ FunCon 'BVBin [FunCon 'BVURem []]
funName (Atom "bvsrem") = Just $ FunCon 'BVBin [FunCon 'BVSRem []]
funName (Atom "bvudiv") = Just $ FunCon 'BVBin [FunCon 'BVUDiv []]
funName (Atom "bvsdiv") = Just $ FunCon 'BVBin [FunCon 'BVSDiv []]
funName (Atom "bvshl") = Just $ FunCon 'BVBin [FunCon 'BVSHL []]
funName (Atom "bvlshr") = Just $ FunCon 'BVBin [FunCon 'BVLSHR []]
funName (Atom "bvashr") = Just $ FunCon 'BVBin [FunCon 'BVASHR []]
funName (Atom "bvxor") = Just $ FunCon 'BVBin [FunCon 'BVXor []]
funName (Atom "bvand") = Just $ FunCon 'BVBin [FunCon 'BVAnd []]
funName (Atom "bvor") = Just $ FunCon 'BVBin [FunCon 'BVOr []]
funName (Atom "bvnot") = Just $ FunCon 'BVUn [FunCon 'BVNot []]
funName (Atom "bvneg") = Just $ FunCon 'BVUn [FunCon 'BVNeg []]
funName (Atom "select") = Just $ FunCon 'Select []
funName (Atom "store") = Just $ FunCon 'Store []
funName (List [Atom "as",Atom "const",List [Atom "Array",List idx,el]])
  = Just $ FunSig (FunCon 'ConstArray [])
           [t| forall fun con field. Function fun con field '( '[$(toType el)],ArrayType $(toTypes idx) $(toType el)) |]
funName (Atom "concat") = Just $ FunCon 'Concat []
funName (List [Atom "_",Atom "extract",Atom end,Atom start])
  = Just $ FunSig (FunCon 'Extract
                          [FunSig (FunCon 'Proxy [])
                                  [t| Proxy $(mkNum start') |]])
                  [t| forall fun con field bv. Function fun con field '( '[BitVecType bv],BitVecType $(mkNum $ end'-start')) |]
  where
    end' = read end
    start' = read start
funName (List [Atom "_",Atom "divisible",Atom n])
  = Just $ FunCon 'Divisible [FunInt (read n)]
funName _ = Nothing

toFun :: BasicExpr -> TH.ExpQ
toFun expr = case funName expr of
  Just name -> funNameToExpr name
  Nothing -> case expr of
    Atom name -> TH.varE (TH.mkName name)

toFunPat :: BasicExpr -> TH.PatQ
toFunPat expr = case funName expr of
  Just name -> funNameToPattern name

toType :: BasicExpr -> TH.TypeQ
toType (Atom "Bool") = [t| BoolType |]
toType (Atom "Int") = [t| IntType |]
toType (Atom "Real") = [t| RealType |]
toType (List [Atom "_",Atom "BitVec",Atom bw]) = [t| BitVecType $(mkNum $ read bw) |]
toType (List [Atom "Array",List idx,el]) = [t| ArrayType $(toTypes idx) $(toType el) |]
toType (Atom name) = [t| DataType $(TH.conT $ TH.mkName name) |]

toTypes :: [BasicExpr] -> TH.TypeQ
toTypes [] = [t| '[] |]
toTypes (x:xs) = [t| $(toType x) ': $(toTypes xs) |]

mkArgs :: Map String TH.Exp -> [BasicExpr] -> TH.ExpQ
mkArgs _ [] = [| NoArg |]
mkArgs bind (x:xs) = [| Arg $(toExpr bind x) $(mkArgs bind xs) |]

mkArgsPat :: [BasicExpr] -> TH.PatQ
mkArgsPat [] = [p| NoArg |]
mkArgsPat (x:xs) = [p| Arg $(toPat x) $(mkArgsPat xs) |]

mkAllEqPat :: [BasicExpr] -> TH.PatQ
mkAllEqPat xs = TH.viewP [| allEqToList |]
                (TH.listP (fmap toPat xs))

mkNum :: Integer -> TH.TypeQ
mkNum 0 = [t| Z |]
mkNum n = [t| S $(mkNum (n-1)) |]
