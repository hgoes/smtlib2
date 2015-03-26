module Language.SMTLib2.ModulusEmulator
       (ModulusEmulator(),
        modulusEmulator,
        emulationAssertions) where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Proxy
import Data.Typeable

data ModulusEmulator b = ModulusEmulator { emulatedBackend :: b
                                         , emulations :: [Emulation]
                                         , addAssertions :: Maybe [Emulation]
                                         }

data Emulation = EmulatedMod { modulusResult :: Integer
                             , modulus :: Integer
                             , modulusExpr :: SMTExpr Integer }
               | EmulatedDiv { divResult :: Integer
                             , divExpr :: SMTExpr Integer
                             , divisor :: SMTExpr Integer
                             , divDiff :: Integer }

modulusEmulator :: Bool -> b -> ModulusEmulator b
modulusEmulator addAssert b = ModulusEmulator { emulatedBackend = b
                                              , emulations = []
                                              , addAssertions = if addAssert then Just [] else Nothing }

emulationAssertions :: ModulusEmulator b -> [SMTExpr Bool]
emulationAssertions b
  = concat $ fmap toAssert (emulations b)

toAssert :: Emulation -> [SMTExpr Bool]
toAssert (EmulatedMod res mod expr)
  = let resVar = Var res ()
    in [App (SMTDivisible mod) (expr - resVar)
       ,resVar .<. (constant mod)
       ,resVar .>=. (constant 0)]
toAssert (EmulatedDiv res expr div diff)
  = let resVar = Var res ()
        diffVar = Var diff ()
    in [resVar * div .==. expr - diffVar
       ,diffVar .>=. (constant 0)
       ,diffVar .<. div]

addEmulation :: Emulation -> ModulusEmulator b -> ModulusEmulator b
addEmulation emul b
  = b2
  where
    b1 = case addAssertions b of
      Nothing -> b
      Just stack -> b { addAssertions = Just $ emul:stack }
    b2 = b1 { emulations = emul:emulations b1 }

flushAssertions :: SMTBackend b m => Maybe InterpolationGroup -> ModulusEmulator b -> m (ModulusEmulator b)
flushAssertions interp b = case addAssertions b of
  Nothing -> return b
  Just [] -> return b
  Just stack -> do
    ((),nb) <- smtHandle (emulatedBackend b) (SMTAssert (app and' $ concat $ fmap toAssert stack) interp Nothing)
    return (b { emulatedBackend = nb
              , addAssertions = Just [] })

emulateModulus :: (SMTBackend b m,SMTType a) => SMTExpr a -> ModulusEmulator b
               -> m (SMTExpr a,ModulusEmulator b)
emulateModulus (App (SMTIntArith Mod) (x,y)) b = case y of
  Const y () -> do
    (x',b1) <- emulateModulus x b
    (resVar,nb) <- smtHandle (emulatedBackend b1)
                   (SMTDeclareFun (FunInfo { funInfoProxy = Proxy::Proxy ((),Integer)
                                           , funInfoArgAnn = ()
                                           , funInfoResAnn = ()
                                           , funInfoName = Nothing }))
    let b2 = b1 { emulatedBackend = nb }
    return (Var resVar (),addEmulation (EmulatedMod resVar y x') b2)
emulateModulus (App (SMTIntArith Rem) (x,y)) b = case y of
  Const y () -> do
    (x',b1) <- emulateModulus x b
    (resVar,nb) <- smtHandle (emulatedBackend b1)
                   (SMTDeclareFun (FunInfo { funInfoProxy = Proxy::Proxy ((),Integer)
                                           , funInfoArgAnn = ()
                                           , funInfoResAnn = ()
                                           , funInfoName = Nothing }))
    let b2 = b1 { emulatedBackend = nb }
    return (ite (x' .>. 0)
            (Var resVar ())
            ((Var resVar ())-(constant y)),addEmulation (EmulatedMod resVar y x') b2)
emulateModulus (App (SMTIntArith Div) (x,y)) b = do
  (x',b1) <- emulateModulus x b
  (y',b2) <- emulateModulus y b1
  (resVar,nb1) <- smtHandle (emulatedBackend b2)
                  (SMTDeclareFun (FunInfo { funInfoProxy = Proxy::Proxy ((),Integer)
                                          , funInfoArgAnn = ()
                                          , funInfoResAnn = ()
                                          , funInfoName = Nothing }))
  (diffVar,nb2) <- smtHandle nb1
                   (SMTDeclareFun (FunInfo { funInfoProxy = Proxy::Proxy ((),Integer)
                                           , funInfoArgAnn = ()
                                           , funInfoResAnn = ()
                                           , funInfoName = Nothing }))
  let b3 = b2 { emulatedBackend = nb2 }
  return (Var resVar (),addEmulation (EmulatedDiv resVar x' y' diffVar) b3)
emulateModulus (App fun args) b = do
  (nargs,nb) <- emulateModulus' args b
  return (App fun nargs,nb)
emulateModulus expr b = return (expr,b)

emulateModulus' :: (SMTBackend b m,Args arg) => arg -> ModulusEmulator b
                 -> m (arg,ModulusEmulator b)
emulateModulus' args b = do
  (nb,nargs) <- foldExprs (\cb expr ann -> do
                              (nexpr,nb) <- emulateModulus expr cb
                              return (nb,nexpr)
                          ) b args (extractArgAnnotation args)
  return (nargs,nb)

unemulateModulus :: SMTType a => ModulusEmulator b -> SMTExpr a -> SMTExpr a
unemulateModulus b (Var i ann)
  = case [ (mod,expr) | EmulatedMod res mod expr <- emulations b
                      , i==res ] of
     (mod,expr):_ -> case cast (mod' expr (constant mod)) of
       Just r -> r
     [] -> case [ (expr,div,diff) | EmulatedDiv res expr div diff <- emulations b
                                  , i==res ] of
            (expr,div,diff):_ -> case cast (div' expr div) of
              Just r -> r
            [] -> case [ (res,expr,div) | EmulatedDiv res expr div diff <- emulations b
                                        , i==diff ] of
                   (res,expr,div):_ -> case cast (mod' expr div) of
                     Just r -> r
                   [] -> Var i ann
unemulateModulus b (App fun args) = App fun nargs
  where
    (_,nargs) = foldExprsId (\_ expr _ -> ((),unemulateModulus b expr)
                            ) () args (extractArgAnnotation args)
unemulateModulus _ expr = expr

instance (SMTBackend b m,Monad m) => SMTBackend (ModulusEmulator b) m where
  smtHandle b (SMTAssert f grp clid) = do
    (nf,b1) <- emulateModulus f b
    ((),nb') <- smtHandle (emulatedBackend b1) (SMTAssert nf grp clid)
    let b2 = b1 { emulatedBackend = nb' }
    b3 <- flushAssertions grp b2
    return ((),b3)
  smtHandle b (SMTDefineFun name parg arg body) = do
    (nbody,nb) <- emulateModulus body b
    (var,nb') <- smtHandle (emulatedBackend nb) (SMTDefineFun name parg arg nbody)
    return (var,nb { emulatedBackend = nb' })
  smtHandle b (SMTGetValue expr) = do
    (nexpr,nb) <- emulateModulus expr b
    (val,nb') <- smtHandle (emulatedBackend nb) (SMTGetValue nexpr)
    return (val,nb { emulatedBackend = nb' })
  smtHandle b SMTGetProof = do
    (proof,nb') <- smtHandle (emulatedBackend b) SMTGetProof
    let nb = b { emulatedBackend = nb' }
    return (unemulateModulus nb proof,nb)
  smtHandle b (SMTGetInterpolant grps) = do
    (res,nb') <- smtHandle (emulatedBackend b) (SMTGetInterpolant grps)
    let nb = b { emulatedBackend = nb' }
    return (unemulateModulus nb res,nb)
  smtHandle b req = do
    (res,nb) <- smtHandle (emulatedBackend b) req
    return (res,b { emulatedBackend = nb })
  smtGetNames b = smtGetNames (emulatedBackend b)
  smtNextName b = smtNextName (emulatedBackend b)
