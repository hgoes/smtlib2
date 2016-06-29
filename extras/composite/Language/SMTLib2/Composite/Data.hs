module Language.SMTLib2.Composite.Data (makeComposite) where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class

import qualified Language.Haskell.TH as TH
import Data.GADT.Compare
import Data.GADT.Show
import Control.Monad

makeComposite :: String -- ^ Name of the composite type
              -> String -- ^ Name of the description type
              -> String -- ^ Name of the reverse type
              -> Int -- ^ Parameter number
              -> [(String,String,[(String,String,String,TH.TypeQ -> [TH.TypeQ] -> TH.TypeQ)])]
              -> TH.Q [TH.Dec]
makeComposite name dname rname par' cons = do
  let name' = TH.mkName name
      e = TH.mkName "e"
      par = take par' (fmap (\c -> [c]) ['a'..'z'])
  i1 <- TH.dataD (TH.cxt []) name'
    ((fmap (TH.PlainTV . TH.mkName) par)++
     [TH.KindedTV e (TH.appK (TH.appK TH.arrowK (TH.conK ''Type)) TH.starK)])
    [ TH.recC (TH.mkName con)
      [ TH.varStrictType (TH.mkName field)
        (TH.strictType TH.notStrict
         (TH.appT (tp (TH.conT name') (fmap (TH.varT . TH.mkName) par)) (TH.varT e)))
      | (field,_,_,tp) <- fields]
    | (con,_,fields) <- cons ] []
  i2 <- TH.dataD (TH.cxt []) (TH.mkName dname)
    (fmap (TH.PlainTV . TH.mkName) par)
    [ TH.recC (TH.mkName dcon)
      [ TH.varStrictType (TH.mkName dfield)
        (TH.strictType TH.notStrict
         (TH.appT (TH.conT ''CompDescr) (tp (TH.conT name') (fmap (TH.varT . TH.mkName) par))))
      | (_,dfield,_,tp) <- fields ]
    | (_,dcon,fields) <- cons     
    ] []
  i3 <- TH.dataD (TH.cxt []) (TH.mkName rname)
    ((fmap (TH.PlainTV . TH.mkName) par)++
     [TH.PlainTV $ TH.mkName "tp"])
    [ TH.normalC (TH.mkName rev)
      [TH.strictType TH.notStrict
       (TH.appT (TH.appT (TH.conT ''RevComp)
                 (tp (TH.conT name') (fmap (TH.varT . TH.mkName) par)))
        (TH.varT $ TH.mkName "tp"))]
    | (_,_,fields) <- cons
    , (_,_,rev,tp) <- fields ] []
  let lpar = length par
      revs = concat $ fmap (\(_,_,fields)
                            -> fmap (\(_,_,rev,_) -> TH.mkName rev) fields
                           ) cons
  i4 <- deriveDescrOrd lpar (TH.mkName dname)
  i5 <- deriveRevShow lpar (TH.mkName rname) revs
  i6 <- deriveRevGEq lpar (TH.mkName rname) revs
  i7 <- deriveRevGCompare lpar (TH.mkName rname) revs
  i8 <- deriveComposite lpar (TH.mkName name) (TH.mkName dname) (TH.mkName rname)
    [ (TH.mkName con,TH.mkName dcon,
       [ (TH.mkName field,TH.mkName dfield,TH.mkName rev)
       | (field,dfield,rev,tp) <- fields ])
    | (con,dcon,fields) <- cons ]
  return $ [i1,i2,i3]++i4++i5++i6++i7++i8

deriveComposite :: Int -> TH.Name -> TH.Name -> TH.Name
                -> [(TH.Name,TH.Name,[(TH.Name,TH.Name,TH.Name)])]
                -> TH.Q [TH.Dec]
deriveComposite numPar name dname rname cons = do
  pars <- replicateM numPar (TH.newName "c")
  let ctx = TH.cxt $ fmap (\par -> (TH.conT ''Composite) `TH.appT` (TH.varT par)
                          ) pars
      compArgs n = foldr (\par tp -> TH.appT tp (TH.varT par)
                         ) n pars
  i1 <- TH.instanceD ctx ((TH.conT ''Composite) `TH.appT` (compArgs (TH.conT name)))
    [TH.tySynInstD ''CompDescr (TH.tySynEqn [compArgs (TH.conT name)]
                                (compArgs (TH.conT dname)))
    ,TH.tySynInstD ''RevComp (TH.tySynEqn [compArgs (TH.conT name)]
                              (compArgs (TH.conT rname)))
    ,TH.funD 'compositeType
     [ do
         fieldNames <- mapM (const (TH.newName "arg")) fields
         TH.clause [TH.conP dcon
                    [ TH.varP fieldName
                    | fieldName <- fieldNames ]]
           (TH.normalB (foldl
                        (\cur fieldName -> cur `TH.appE` (TH.appE (TH.varE 'compositeType)
                                                          (TH.varE fieldName)))
                        (TH.conE con) fieldNames)) []
     | (con,dcon,fields) <- cons ]
    ,TH.funD 'foldExprs
     [ do
         fName <- TH.newName "f"
         fieldNames <- mapM (const (TH.newName "arg")) fields
         nfieldNames <- mapM (const (TH.newName "res")) fields
         TH.clause [TH.varP fName
                   ,TH.conP con
                    [ TH.varP fieldName
                    | fieldName <- fieldNames ]]
           (TH.normalB $ TH.doE $
            [ TH.bindS (TH.varP new) (TH.appsE [TH.varE 'foldExprs
                                               ,TH.appsE [TH.varE '(.)
                                                         ,TH.varE fName
                                                         ,TH.conE rev]
                                               ,TH.varE old
                                               ])
            | (old,new,(_,_,rev)) <- zip3 fieldNames nfieldNames fields ] ++
            [ TH.noBindS (TH.appE (TH.varE 'return)
                          (foldl (\cur fieldName
                                   -> cur `TH.appE` (TH.varE fieldName)
                                 ) (TH.conE con) nfieldNames)) ]
           ) []
     | (con,dcon,fields) <- cons ]
    ,TH.funD 'accessComposite
     [ do
         matchName <- TH.newName "x"
         revName <- TH.newName "rev"
         TH.clause [TH.conP rev [TH.varP revName]
                   ,TH.conP con ((replicate n TH.wildP)++[TH.varP matchName]++(replicate (length fields - n - 1) TH.wildP))]
           (TH.normalB $ TH.appsE [TH.varE 'accessComposite
                                  ,TH.varE revName
                                  ,TH.varE matchName]) []
     | (con,dcon,fields) <- cons
     , (n,(field,_,rev)) <- zip [0..] fields ]
    ]
  return [i1]

deriveRevGEq :: Int -> TH.Name -> [TH.Name] -> TH.Q [TH.Dec]
deriveRevGEq numPar rname rcons = do
  pars <- replicateM numPar (TH.newName "c")
  let ctx = TH.cxt $ fmap (\par -> (TH.conT ''Composite) `TH.appT` (TH.varT par)
                          ) pars
      compArgs n = foldl (\tp par -> TH.appT tp (TH.varT par)
                         ) n pars
  i <- TH.instanceD ctx ((TH.conT ''GEq) `TH.appT` (compArgs (TH.conT rname)))
    [TH.funD 'geq $
     [ do
         r1 <- TH.newName "r1"
         r2 <- TH.newName "r2"
         TH.clause [TH.conP rev [TH.varP r1]
                   ,TH.conP rev [TH.varP r2]]
           (TH.normalB $ TH.doE
            [TH.bindS (TH.conP 'Refl []) (TH.appsE [TH.varE 'geq
                                                   ,TH.varE r1
                                                   ,TH.varE r2])
            ,TH.noBindS $ TH.appsE [TH.varE 'return
                                   ,TH.conE 'Refl]]) []
     | rev <- rcons ] ++
    [ TH.clause [TH.wildP,TH.wildP] (TH.normalB $ TH.conE 'Nothing) [] ]]
  return [i]

deriveRevGCompare :: Int -> TH.Name -> [TH.Name] -> TH.Q [TH.Dec]
deriveRevGCompare numPar rname rcons = do
  pars <- replicateM numPar (TH.newName "c")
  let ctx = TH.cxt $ fmap (\par -> (TH.conT ''Composite) `TH.appT` (TH.varT par)
                          ) pars
      compArgs n = foldl (\tp par -> TH.appT tp (TH.varT par)
                         ) n pars
  i <- TH.instanceD ctx ((TH.conT ''GCompare) `TH.appT` (compArgs (TH.conT rname)))
    [TH.funD 'gcompare $
     concat
     [ [ do
           r1 <- TH.newName "r1"
           r2 <- TH.newName "r2"
           TH.clause [TH.conP rev [TH.varP r1]
                     ,TH.conP rev [TH.varP r2]]
             (TH.normalB $ TH.caseE (TH.appsE [TH.varE 'gcompare,TH.varE r1,TH.varE r2])
              [TH.match (TH.conP 'GEQ []) (TH.normalB $ TH.conE 'GEQ) []
              ,TH.match (TH.conP 'GLT []) (TH.normalB $ TH.conE 'GLT) []
              ,TH.match (TH.conP 'GGT []) (TH.normalB $ TH.conE 'GGT) []]) []
       ,TH.clause [TH.conP rev [TH.wildP]
                  ,TH.wildP]
        (TH.normalB $ TH.conE 'GLT) []
       ,TH.clause [TH.wildP
                  ,TH.conP rev [TH.wildP]]
        (TH.normalB $ TH.conE 'GGT) []]
     | rev <- rcons ]]
  return [i]

deriveRevShow :: Int -> TH.Name -> [TH.Name] -> TH.Q [TH.Dec]
deriveRevShow numPar rname rcons = do
  pars <- replicateM numPar (TH.newName "c")
  tp <- TH.newName "tp"
  let ctx = TH.cxt $ fmap (\par -> (TH.conT ''Composite) `TH.appT` (TH.varT par)
                          ) pars
      compArgs n = foldl (\tp par -> TH.appT tp (TH.varT par)
                         ) n pars
  i1 <- TH.instanceD ctx ((TH.conT ''Show) `TH.appT` (TH.appT (compArgs (TH.conT rname))
                                                     (TH.varT tp)))
    [TH.funD 'showsPrec $
     [ do
         p <- TH.newName "p"
         r <- TH.newName "r"
         TH.clause [TH.varP p
                   ,TH.conP rev [TH.varP r]]
           (TH.normalB $ [| showParen ($(TH.varE p) > 10)
                              (showString $(TH.stringE ((TH.nameBase rev)++" ")) .
                               gshowsPrec 11 $(TH.varE r)) |]) []
     | rev <- rcons ]]
  i2 <- TH.instanceD ctx ((TH.conT ''GShow) `TH.appT` (compArgs (TH.conT rname)))
    [TH.funD 'gshowsPrec [TH.clause [] (TH.normalB $ TH.varE 'showsPrec) []]]
  return [i1,i2]

deriveDescrOrd :: Int -> TH.Name -> TH.Q [TH.Dec]
deriveDescrOrd numPar dname = do
  pars <- replicateM numPar (TH.newName "c")
  let ctx = TH.cxt $ fmap (\par -> (TH.conT ''Composite) `TH.appT` (TH.varT par)
                          ) pars
      compArgs n = foldl (\tp par -> TH.appT tp (TH.varT par)
                         ) n pars
  i1 <- TH.standaloneDerivD ctx ((TH.conT ''Eq) `TH.appT` (compArgs (TH.conT dname)))
  i2 <- TH.standaloneDerivD ctx ((TH.conT ''Ord) `TH.appT` (compArgs (TH.conT dname)))
  return [i1,i2]
