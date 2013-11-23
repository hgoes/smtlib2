{-# LANGUAGE OverloadedStrings,FlexibleInstances,TypeFamilies,FlexibleContexts,RankNTypes,GADTs,ScopedTypeVariables #-}
module QuickCheck where

import Test.QuickCheck as QC hiding ((.&&.),(.||.))
import qualified Test.QuickCheck.Property as QCP
import Language.SMTLib2 as SMT2
import Language.SMTLib2.Pipe
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Interface
import Data.Text as T hiding (concat)
import Data.Unit
import Data.Typeable
import Data.Map as Map
import Data.List
import Data.Monoid
import Data.AttoLisp as L
import qualified Data.ByteString.Char8 as BS
import Data.Attoparsec.ByteString as AP

commonTypes :: DataTypeInfo
commonTypes = emptyDataTypeInfo

eqTest = do
  quickCheck (QC.forAll genExpression ((\x -> x==x) :: SMTExpr Bool -> Bool))
  quickCheck (QC.forAll genExpression ((\x -> x==x) :: SMTExpr Integer -> Bool))

translateId = do
  quickCheck (QC.forAll (genExpression::Gen (SMTExpr Bool)) translateCheck)

translateExpr :: (forall a. SMTType a => SMTExpr a -> b) -> L.Lisp -> Maybe b
translateExpr f l = lispToExpr (commonFunctions `mappend` commonTheorems) nameToVar commonTypes f Nothing l

parseLispSimple :: String -> L.Lisp
parseLispSimple str = case AP.parse lisp (BS.pack str) of
  Done _ x -> x
  _ -> error $ "INVALID LISP: "++str

testExprs :: [L.Lisp]
testExprs = [L.Number 102
            ,parseLispSimple "(= b0 b1)"
            ,parseLispSimple "(_ as-array (= (Int Int) Bool))"
            ,parseLispSimple "((as const (Array Int Bool)) true)"
            ,parseLispSimple "(select ((as const (Array Int Int Int)) 5) 1 2)"
            ,L.Symbol "#x10"
            ,parseLispSimple "(concat #xaa #x0a)"
            ,parseLispSimple "((_ extract 7 0) #xaabb)"
            ,parseLispSimple "(let ((x 10) (y (+ x 8))) y)"
            ,parseLispSimple "(hypothesis false)"
            ,parseLispSimple "(let ((arr0 ((as const (Array (_ BitVec 16) Int)) 10))) (select arr0 #x0002))"
            ,parseLispSimple "(let ((arr0 ((as const (Array (_ BitVec 16) Int)) 10))) (let ((arr1 (store arr0 #x0001 5))) (store arr1 #x0002 9)))"
            ]

testResults = mapM_ (\res -> case res of
                        Nothing -> putStrLn "FAILED"
                        Just res -> putStrLn res) $
              fmap (translateExpr $ \expr -> show expr ++ " :: " ++ show (typeOf (getUndef expr))) testExprs

translateCheck :: SMTType a => SMTExpr a -> QCP.Result
translateCheck (expr::SMTExpr a)
  = let (l,_) = exprToLisp expr 0
        expr' = lispToExpr commonFunctions
                nameToVar
                commonTypes gcast (Just $ getSort (undefined::a) (extractAnnotation expr)) l
    in QCP.MkResult { QCP.ok = Just $ Just (Just expr) == expr'
                    , QCP.expect = True
                    , QCP.reason = show expr ++ " is parsed back as " ++ show expr'
                    , QCP.interrupted = False
                    , QCP.abort = False
                    , QCP.stamp = []
                    , QCP.callbacks = []
                    }

nameToVar :: Text -> Maybe UntypedExpr
nameToVar x = case T.unpack x of
  'b':_ -> Just (UntypedExpr (Var (T.unpack x) () :: SMTExpr Bool))
  'i':_ -> Just (UntypedExpr (Var (T.unpack x) () :: SMTExpr Integer))
  str -> Nothing

type BoundVars = Map TypeRep [UExpr]

data UExpr where
  UExpr :: Typeable a => SMTExpr a -> UExpr

newtype ExprGen a = ExprGen { genExpr :: BoundVars -> a }

castUntypedExpr :: Typeable a => UExpr -> SMTExpr a
castUntypedExpr (UExpr x) = case cast x of
  Just r -> r
  Nothing -> error $ "Type error in bound variable."

getBoundFor :: Typeable a => a -> BoundVars -> [SMTExpr a]
getBoundFor tp mp = fmap castUntypedExpr $ Map.findWithDefault [] (typeOf tp) mp

addBoundVar :: Typeable a => SMTExpr a -> BoundVars -> BoundVars
addBoundVar e b = Map.alter (\cur -> Just $ case cur of
                                Nothing -> [UExpr e]
                                Just cur' -> (UExpr e):cur')
                  (typeOf $ undefArg e) b
  where
    undefArg :: SMTExpr a -> a
    undefArg = const undefined

genExpression :: Arbitrary (ExprGen a) => Gen a
genExpression = do
  el <- arbitrary
  return $ genExpr el Map.empty

instance Arbitrary (ExprGen (SMTExpr Bool)) where
  arbitrary = genBool

instance Arbitrary (ExprGen (SMTExpr Integer)) where
  arbitrary = genInt

genBool :: Gen (ExprGen (SMTExpr Bool))
genBool = sized (\s -> if s == 0
                       then oneof [genVar,genConst]
                       else resize (s `div` 2) $ oneof [genVar
                                                        ,genConst
                                                        ,genEq
                                                        ,genOrd
                                                        ,genLogic
                                                        ,genITE
                                                        ,genExistQuant
                                                        ,genLet
                                                        ,genSelect])

instance (Arbitrary (ExprGen idx),Arbitrary (ExprGen (SMTExpr a)),SMTType a,SMT2.Args idx,Unit (ArgAnnotation idx),Liftable idx) => Arbitrary (ExprGen (SMTExpr (SMTArray idx a))) where
  arbitrary = oneof [genConstArray,genStore]

genInt :: Gen (ExprGen (SMTExpr Integer))
genInt = sized $ \s -> if s==0
                       then oneof [genVar,genConst]
                       else resize (s `div` 2) $ oneof [genVar
                                                       ,genConst
                                                       ,genArith
                                                       ,genDivModRem
                                                       ,genITE
                                                       ,genLet
                                                       ,genSelect]

genVar :: (SMTType a,Unit (SMTAnnotation a)) => Gen (ExprGen (SMTExpr a))
genVar = withUndef $ \u -> do
  b <- arbitrary
  i <- arbitrary
  return $ ExprGen $ \bound_vars -> if b
                                    then (case getBoundFor u bound_vars of
                                             [] -> genUnbound u i
                                             xs -> xs `genericIndex` (i `mod` (genericLength xs)))
                                    else genUnbound u i
  where
    genUnbound u i = Var ((tname u)++show (abs i::Integer)) unit
    withUndef :: (a -> Gen (ExprGen (SMTExpr a))) -> Gen (ExprGen (SMTExpr a))
    withUndef f = f undefined
    tname u
      | typeOf u == typeOf (undefined::Bool) = "b"
      | typeOf u == typeOf (undefined::Integer) = "i"

genConst :: (SMTValue a,Arbitrary a,Unit (SMTAnnotation a)) => Gen (ExprGen (SMTExpr a))
genConst = do
  c <- arbitrary
  return $ ExprGen $ const $ Const c unit

genAny :: (forall a. (Arbitrary (ExprGen (SMTExpr a)),SMTType a) => ExprGen (SMTExpr a) -> Gen b) -> Gen b
genAny f = oneof [genBool >>= f
                 ,genInt >>= f]

genAnyArg :: (forall a. (Arbitrary (ExprGen a),SMT2.Args a,Unit (ArgAnnotation a),Liftable a) => ExprGen a -> Gen b) -> Gen b
genAnyArg f = oneof [genBool >>= f
                    ,genInt >>= f]

genAnyNum :: (forall a. (Arbitrary (ExprGen (SMTExpr a)),SMTType a,Num a,SMTArith a,SMTOrd a) => ExprGen (SMTExpr a) -> Gen b) -> Gen b
genAnyNum f = oneof [genInt >>= f]

genEq :: Gen (ExprGen (SMTExpr Bool))
genEq = genAny (\lhs -> do
                   rhs <- arbitrary
                   return $ ExprGen $ \b -> (genExpr lhs b) .==. (genExpr rhs b))

genOrd :: Gen (ExprGen (SMTExpr Bool))
genOrd = genAnyNum (\lhs -> do
                       rhs <- arbitrary
                       op <- elements [(.>=.),(.>.),(.<=.),(.<.)]
                       return $ ExprGen $ \b -> op (genExpr lhs b) (genExpr rhs b))

genArith :: (Arbitrary (ExprGen (SMTExpr a)),SMTArith a) => Gen (ExprGen (SMTExpr a))
genArith = do
  lhs <- arbitrary
  rhs <- arbitrary
  op <- elements [\(x,y) -> App (SMTArith Plus) [x,y]
                 ,App SMTMinus
                 ,\(x,y) -> App (SMTArith Mult) [x,y]]
  return $ ExprGen $ \b -> op (genExpr lhs b,genExpr rhs b)

genDivModRem :: Gen (ExprGen (SMTExpr Integer))
genDivModRem = do
  lhs <- arbitrary
  rhs <- arbitrary
  op <- elements [Div,Mod,Rem]
  return $ ExprGen $ \b -> App (SMTIntArith op) (genExpr lhs b,genExpr rhs b)

genLogic :: Gen (ExprGen (SMTExpr Bool))
genLogic = oneof [do
                     x <- arbitrary
                     y <- arbitrary
                     return $ ExprGen $ \b -> (genExpr x b) .&&. (genExpr y b)
                 ,do
                     x <- arbitrary
                     y <- arbitrary
                     return $ ExprGen $ \b -> (genExpr x b) .||. (genExpr y b)
                 ,do
                     x <- arbitrary
                     y <- arbitrary
                     return $ ExprGen $ \b -> (genExpr x b) .=>. (genExpr y b)
                 ,do
                     x <- arbitrary
                     y <- arbitrary
                     return $ ExprGen $ \b -> App (SMTLogic XOr) [genExpr x b,genExpr y b]
                 ,do
                     x <- arbitrary
                     return $ ExprGen $ \b -> not' (genExpr x b)
                 ]

genITE :: (Arbitrary (ExprGen (SMTExpr a)),SMTType a) => Gen (ExprGen (SMTExpr a))
genITE = do
  iftrue <- arbitrary
  iffalse <- arbitrary
  cond <- arbitrary
  return $ ExprGen $ \b -> App SMTITE (genExpr cond b,genExpr iftrue b,genExpr iffalse b)

genExistQuant :: Gen (ExprGen (SMTExpr Bool))
genExistQuant = do
  body <- arbitrary
  elements [ExprGen $ \b -> Exists () (\e -> genExpr body (addBoundVar (e::SMTExpr Bool) b))
           ,ExprGen $ \b -> Exists () (\e -> genExpr body (addBoundVar (e::SMTExpr Integer) b))
           ,ExprGen $ \b -> Forall () (\e -> genExpr body (addBoundVar (e::SMTExpr Bool) b))
           ,ExprGen $ \b -> Forall () (\e -> genExpr body (addBoundVar (e::SMTExpr Integer) b))]

genLet :: (SMTType a,Arbitrary (ExprGen (SMTExpr a))) => Gen (ExprGen (SMTExpr a))
genLet = do
  body <- arbitrary
  oneof [do
            bound <- arbitrary
            return $ ExprGen $ \b -> Let () (genExpr bound b :: SMTExpr Bool) (\e -> genExpr body (addBoundVar e b))
        ,do
            bound <- arbitrary
            return $ ExprGen $ \b -> Let () (genExpr bound b :: SMTExpr Integer) (\e -> genExpr body (addBoundVar e b))
        ]

genConstArray :: (SMT2.Args idx,SMTType a,Arbitrary (ExprGen (SMTExpr a)),Unit (ArgAnnotation idx)) => Gen (ExprGen (SMTExpr (SMTArray idx a)))
genConstArray = do
  elem <- arbitrary
  return $ ExprGen $ \b -> constArray (genExpr elem b) unit

genStore :: (Arbitrary (ExprGen (SMTExpr (SMTArray idx a))),Arbitrary (ExprGen idx),Arbitrary (ExprGen (SMTExpr a)),SMTType a,Liftable idx) => Gen (ExprGen (SMTExpr (SMTArray idx a)))
genStore = do
  arr <- arbitrary
  idx <- arbitrary
  elem <- arbitrary
  return $ ExprGen $ \b -> store (genExpr arr b) (genExpr idx b) (genExpr elem b)

genSelect :: (Arbitrary (ExprGen (SMTExpr a)),SMTType a) => Gen (ExprGen (SMTExpr a))
genSelect = genAnyArg (\idx -> do
                          arr <- arbitrary
                          return $ ExprGen $ \b -> select (genExpr arr b) (genExpr idx b))
