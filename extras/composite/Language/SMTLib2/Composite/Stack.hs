module Language.SMTLib2.Composite.Stack where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Container
import Language.SMTLib2.Composite.List
import Language.SMTLib2.Composite.Choice
import Language.SMTLib2.Composite.Null
import Language.SMTLib2.Composite.Singleton
import Language.SMTLib2.Composite.Array
import Language.SMTLib2.Composite.Convert
import Language.SMTLib2.Internals.Embed

import Data.GADT.Compare
import Data.GADT.Show
import Data.Monoid
import qualified Data.Vector as Vec
import Data.List (partition,find)
import Data.Foldable
import Data.Proxy

class (Composite idx) => IsStack st idx where
  stackElement :: (Composite a,Embed m e,Monad m)
               => idx e
               -> Access (st a) ('Seq a 'Id) a m e
  stackEmpty :: (Composite a,Embed m e,Monad m)
             => m (a e)
             -> m (Stack st idx a e)
  stackSingleton :: (Composite a,Embed m e,Monad m)
                 => a e
                 -> m (Stack st idx a e)
  stackPush :: (Composite a,Embed m e,Monad m,GCompare e)
            => [e BoolType]
            -> a e
            -> Stack st idx a e
            -> m (Stack st idx a e)
  stackPop :: (Composite a,Embed m e,Monad m,GCompare e)
           => [e BoolType]
           -> Stack st idx a e
           -> m (Stack st idx a e)
  stackTop :: (Composite a,Embed m e,Monad m)
           => Stack st idx a e
           -> m (idx e)
  stackElementRev :: (Composite a)
                  => Proxy st
                  -> Proxy idx
                  -> Proxy a
                  -> (forall tp'. RevComp a tp' -> r)
                  -> RevComp (st a) tp
                  -> r
  stackElements :: Monad m
                => Proxy idx
                -> (forall e'. a e' -> m ())
                -> st a e
                -> m ()
  stackIndexType :: st a e -> idx Repr -> Maybe (idx Repr)
  stackAt :: Proxy st -> Proxy idx -> Proxy a
          -> RevComp (st a) tp
          -> String
  stackAt _ _ _ _ = ""

data Stack st idx (a::(Type -> *) -> *) (e::Type -> *)
  = Stack { _stack :: st a e
          , _stackTop :: idx e }

top :: (IsStack st idx,Composite a,Embed m e,Monad m)
    => Access (Stack st idx a) ('Seq a 'Id) a m e
top st = do
  tidx <- stackTop st
  acc <- stackElement tidx (_stack st)
  return $ AccFun _stack (\x -> Stack x (_stackTop st)) acc

element :: (IsStack st idx,Composite a,Embed m e,Monad m)
        => idx e -> Access (Stack st idx a) ('Seq a 'Id) a m e
element idx st@(Stack s top) = do
  acc <- stackElement idx s
  return $ AccFun _stack (\x -> Stack x top) acc

data RevStack st idx (a::(Type -> *) -> *) tp
  = RevStack !(RevComp (st a) tp)
  | RevTop !(RevComp idx tp)

instance (IsStack st idx,Composite (st a)) => Composite (Stack st idx a) where
  type RevComp (Stack st idx a) = RevStack st idx a
  foldExprs f (Stack st top) = do
    nst <- foldExprs (f.RevStack) st
    ntop <- foldExprs (f.RevTop) top
    return $ Stack nst ntop
  getRev (RevStack r) (Stack st _) = getRev r st
  getRev (RevTop r) (Stack _ top) = getRev r top
  setRev (RevStack r) v (Just (Stack st top)) = do
    nst <- setRev r v (Just st)
    return $ Stack nst top
  setRev (RevTop r) v (Just (Stack st top)) = do
    ntop <- setRev r v (Just top)
    return $ Stack st ntop
  setRev _ _ Nothing = Nothing
  compCompare (Stack st1 top1) (Stack st2 top2)
    = compCompare st1 st2 `mappend`
      compCompare top1 top2
  compCombine f (Stack st1 top1) (Stack st2 top2) = do
    nst <- compCombine f st1 st2
    case nst of
      Nothing -> return Nothing
      Just nst' -> do
        ntop <- compCombine f top1 top2
        case ntop of
          Nothing -> return Nothing
          Just ntop' -> return $ Just $ Stack nst' ntop'
  compShow p (Stack st top) = showParen (p>10) $
                              showString "Stack " .
                              compShow 11 st . showChar ' ' .
                              compShow 11 top

instance (IsStack st idx,Composite (st a)) => GEq (RevStack st idx a) where
  geq (RevStack r1) (RevStack r2) = geq r1 r2
  geq (RevTop r1) (RevTop r2) = geq r1 r2
  geq _ _ = Nothing

instance (IsStack st idx,Composite (st a)) => GCompare (RevStack st idx a) where
  gcompare (RevStack r1) (RevStack r2) = gcompare r1 r2
  gcompare (RevStack _) _ = GLT
  gcompare _ (RevStack _) = GGT
  gcompare (RevTop r1) (RevTop r2) = gcompare r1 r2

instance (IsStack st idx,Composite (st a)) => GShow (RevStack st idx a) where
  gshowsPrec p (RevStack r) = showParen (p>10) $
                              showString "RevStack " .
                              gshowsPrec 11 r
  gshowsPrec p (RevTop r) = showParen (p>10) $
                            showString "RevTop " .
                            gshowsPrec 11 r

-- Stack instances

newtype StackList a e
  = StackList { stackList :: CompList a e }

instance Composite a => Composite (StackList a) where
  type RevComp (StackList a) = RevList a
  foldExprs f (StackList ch) = fmap StackList $ foldExprs f ch
  getRev r (StackList ch) = getRev r ch
  setRev r v idx = do
    nch <- setRev r v (fmap stackList idx)
    return (StackList nch)
  compCombine f (StackList i1) (StackList i2)
    = fmap (fmap StackList) $ compCombine f i1 i2
  compCompare (StackList i1) (StackList i2) = compCompare i1 i2
  compShow p (StackList i) = compShow p i

newtype StackArray tp a e
  = StackArray { stackArray :: CompArray '[tp] a e }

instance Composite a => Composite (StackArray tp a) where
  type RevComp (StackArray tp a) = RevArray '[tp] a
  foldExprs f (StackArray ch) = fmap StackArray $ foldExprs f ch
  getRev r (StackArray ch) = getRev r ch
  setRev r v idx = do
    nch <- setRev r v (fmap stackArray idx)
    return (StackArray nch)
  compCombine f (StackArray i1) (StackArray i2)
    = fmap (fmap StackArray) $ compCombine f i1 i2
  compCompare (StackArray i1) (StackArray i2) = compCompare i1 i2
  compShow p (StackArray i) = compShow p i

newtype StackListIndex e
  = StackListIndex { stackListIndex :: Choice BoolEncoding (NoComp Int) e }

instance Composite StackListIndex where
  type RevComp StackListIndex = RevChoice BoolEncoding (NoComp Int)
  foldExprs f (StackListIndex ch) = fmap StackListIndex $ foldExprs f ch
  getRev r (StackListIndex ch) = getRev r ch
  setRev r v idx = do
    nch <- setRev r v (fmap stackListIndex idx)
    return (StackListIndex nch)
  compCombine f (StackListIndex i1) (StackListIndex i2)
    = fmap (fmap StackListIndex) $ compCombine f i1 i2
  compCompare (StackListIndex i1) (StackListIndex i2) = compCompare i1 i2
  compShow p (StackListIndex i) = compShow p i

newtype StackArrayIndex tp e
  = StackArrayIndex { stackArrayIndex :: Comp tp e }

instance Composite (StackArrayIndex tp) where
  type RevComp (StackArrayIndex tp) = (:~:) tp
  foldExprs f (StackArrayIndex ch) = fmap StackArrayIndex $ foldExprs f ch
  getRev r (StackArrayIndex ch) = getRev r ch
  setRev r v idx = do
    nch <- setRev r v (fmap stackArrayIndex idx)
    return (StackArrayIndex nch)
  compCombine f (StackArrayIndex i1) (StackArrayIndex i2)
    = fmap (fmap StackArrayIndex) $ compCombine f i1 i2
  compCompare (StackArrayIndex i1) (StackArrayIndex i2) = compCompare i1 i2
  compShow p (StackArrayIndex i) = compShow p i

instance IsStack StackList StackListIndex where
  stackElement (StackListIndex idx) _ = do
    lst <- getChoices idx
    return $ AccFun stackList StackList $
      AccSeq [ (ListIndex i,cond,AccId)
             | (NoComp i,cond) <- lst ]
  stackEmpty _ = do
    let top = initialBoolean []
    return $ Stack (StackList $ CompList Vec.empty) (StackListIndex top)
  stackSingleton el = do
    top <- singleton (boolEncoding [NoComp 0]) (NoComp 0)
    return $ Stack
      (StackList $ CompList $ Vec.singleton el)
      (StackListIndex top)
  stackPush pushCond el (Stack (StackList (CompList els)) (StackListIndex top)) = do
    let sz = Vec.length els
    lst <- getChoices top
    let (existing,new) = partition (\(NoComp i,_) -> i<sz-1) lst
    upd <- mapM (\(NoComp i,cond) -> do
                    case cond++pushCond of
                      [] -> return (i+1,el)
                      [c] -> do
                        Just nel <- compITE c el (els Vec.! (i+1))
                        return (i+1,nel)
                      cs -> do
                        c <- and' cs
                        Just nel <- compITE c el (els Vec.! (i+1))
                        return (i+1,nel)
                ) existing
    let els1 = els Vec.// upd
        els2 = case new of
          [] -> els1
          [_] -> Vec.snoc els1 el
    top1 <- mapChoices (\_ (NoComp i) -> return (NoComp (i+1))
                       ) top
    top2 <- case pushCond of
      [] -> return top1
      cs -> do
        c <- and' cs
        Just res <- compITE c top1 top
        return res
    return $ Stack (StackList (CompList els2)) (StackListIndex top2)
  stackPop popCond (Stack (StackList (CompList els)) (StackListIndex top)) = do
    let sz = Vec.length els
    lst <- getChoices top
    top1 <- mapChoices (\_ (NoComp i) -> if i>0
                                         then return (NoComp (i-1))
                                         else return (NoComp i)
                       ) top
    top2 <- case popCond of
      [] -> return top1
      cs -> do
        c <- and' cs
        Just res <- compITE c top1 top
        return res
    let nels = if null popCond
               then case find (\(NoComp i,cond) -> i==sz-1 && null cond) lst of
                      Nothing -> els
                      Just _ -> Vec.take (sz-1) els
               else els
    return $ Stack (StackList (CompList nels)) (StackListIndex top2)
  stackTop = return._stackTop
  stackElementRev _ _ _ f (RevList _ r) = f r
  stackElements _ f (StackList (CompList els)) = mapM_ f els
  stackIndexType (StackList (CompList els)) _
    = Just $ StackListIndex $ boolEncoding [NoComp i | i <- [0..Vec.length els-1]]
  stackAt _ _ _ (RevList i _) = show i++"."

instance (Num (Value tp)) => IsStack StackList (StackArrayIndex tp) where
  stackElement (StackArrayIndex (Comp idx)) (StackList (CompList els)) = do
    ch <- mapM (\(i,_) -> do
                   cond <- idx .==. constant (fromIntegral i)
                   return (ListIndex i,[cond],AccId)
               ) $ zip [0..] (Vec.toList els)
    return $ AccFun stackList StackList $ AccSeq ch
  stackEmpty _ = do
    top <- constant 0
    return $ Stack (StackList $ CompList Vec.empty) (StackArrayIndex $ Comp top)
  stackSingleton el = do
    top <- constant 1
    return $ Stack
      (StackList $ CompList $ Vec.singleton el)
      (StackArrayIndex $ Comp top)
  stackPush pushCond el (Stack (StackList (CompList els)) (StackArrayIndex (Comp top))) = do
    nels <- Vec.imapM (\i cel -> do
                          c <- top .==. constant (fromIntegral (i-1))
                          rc <- case pushCond of
                            [] -> return c
                            _ -> and' (c:pushCond)
                          Just nel <- compITE rc el cel
                          return nel
                      ) els
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    succTop <- case topTp of
      IntRepr -> top .+. cint 1
      BitVecRepr bw -> top `bvadd` cbv 1 bw
    ntop <- case pushCond of
      [] -> return succTop
      [c] -> ite c succTop top
      cs -> ite (and' cs) succTop top
    return $ Stack
      (StackList $ CompList $ Vec.snoc nels el)
      (StackArrayIndex $ Comp ntop)
  stackPop popCond (Stack (StackList (CompList els)) (StackArrayIndex (Comp top))) = do
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    predTop <- case topTp of
      IntRepr -> top .-. cint 1
      BitVecRepr bw -> top `bvsub` cbv 1 bw
    ntop <- case popCond of
      [] -> return predTop
      [c] -> ite c predTop top
      cs -> ite (and' cs) predTop top
    return $ Stack
      (StackList $ CompList $ if Vec.null els
                              then els
                              else Vec.take (Vec.length els-1) els)
      (StackArrayIndex $ Comp ntop)
  stackTop (Stack _ (StackArrayIndex (Comp top))) = do
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    predTop <- case topTp of
      IntRepr -> top .-. cint 1
      BitVecRepr bw -> top `bvsub` cbv 1 bw
    return $ StackArrayIndex $ Comp predTop
  stackElementRev _ _ _ f (RevList _ r) = f r
  stackElements _ f (StackList (CompList els)) = mapM_ f els
  stackIndexType (StackList (CompList els)) = Just . id

instance (Num (Value tp)) => IsStack (StackArray tp) (StackArrayIndex tp) where
  stackElement (StackArrayIndex (Comp idx)) _
    = return $ AccFun stackArray StackArray $
      AccSeq [ (ArrayIndex (idx:::Nil),[],AccId) ]
  stackEmpty def = do
    top <- constant 0
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    defEl <- def
    arr <- newConstantArray (topTp:::Nil) defEl
    return $ Stack (StackArray arr) (StackArrayIndex $ Comp top)
  stackSingleton el = do
    top <- constant 1
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    arr <- newConstantArray (topTp:::Nil) el
    return $ Stack (StackArray arr) (StackArrayIndex $ Comp top)
  stackPush pushCond el (Stack (StackArray arr) (StackArrayIndex (Comp top))) = do
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    succTop <- case topTp of
      IntRepr -> top .+. cint 1
      BitVecRepr bw -> top `bvadd` cbv 1 bw
    ntop <- case pushCond of
      [] -> return succTop
      [c] -> ite c succTop top
      cs -> ite (and' cs) succTop top
    rcond <- case pushCond of
      [] -> return Nothing
      [c] -> return $ Just c
      cs -> fmap Just $ and' cs
    Just narr <- storeArrayCond rcond arr (top:::Nil) el
    return $ Stack (StackArray narr) (StackArrayIndex (Comp ntop))
  stackPop popCond (Stack arr (StackArrayIndex (Comp top))) = do
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    predTop <- case topTp of
      IntRepr -> top .-. cint 1
      BitVecRepr bw -> top `bvsub` cbv 1 bw
    ntop <- case popCond of
      [] -> return predTop
      [c] -> ite c predTop top
      cs -> ite (and' cs) predTop top
    return $ Stack arr (StackArrayIndex $ Comp top)
  stackTop (Stack _ (StackArrayIndex (Comp top))) = do
    topTp <- fmap (\tp -> tp top) $ embedTypeOf
    predTop <- case topTp of
      IntRepr -> top .-. cint 1
      BitVecRepr bw -> top `bvsub` cbv 1 bw
    return $ StackArrayIndex $ Comp predTop
  stackElementRev _ _ _ f (RevArray r) = f r
  stackElements _ f (StackArray (CompArray _ arr)) = f arr
  stackIndexType (StackArray (CompArray (idx:::Nil) _)) _
    = Just $ StackArrayIndex (Comp idx)

instance (Num (Value tp)) => IsStack (StackArray tp) StackListIndex where
  stackElement (StackListIndex idx) _ = do
    lst <- getChoices idx
    acc <- mapM (\(NoComp i,cond) -> do
                    ri <- constant $ fromIntegral i
                    return (ArrayIndex (ri:::Nil),cond,AccId)
                ) lst
    return $ AccFun stackArray StackArray $ AccSeq acc
  stackEmpty (def::m (a e)) = do
    (topEx::e tp) <- constant 0
    (topTp::Repr tp) <- fmap (\tp -> tp topEx) $ embedTypeOf
    defEl <- def
    (arr::CompArray '[tp] a e) <- newConstantArray (topTp:::Nil) defEl
    let top = initialBoolean []
    return $ Stack (StackArray arr) (StackListIndex top)
  stackSingleton (el::a e) = do
    (topEx::e tp) <- constant 0
    (topTp::Repr tp) <- fmap (\tp -> tp topEx) $ embedTypeOf
    (arr::CompArray '[tp] a e) <- newConstantArray (topTp:::Nil) el
    top <- singleton (boolEncoding [NoComp 0]) (NoComp 0)
    return $ Stack (StackArray arr) (StackListIndex top)
  stackPush pushCond el (Stack (StackArray arr) (StackListIndex top)) = do
    top1 <- mapChoices (\_ (NoComp i) -> return (NoComp (i+1))
                       ) top
    top2 <- case pushCond of
      [] -> return top1
      cs -> do
        c <- and' cs
        Just res <- compITE c top1 top
        return res
    ch <- getChoices top
    narr <- foldlM (\carr (NoComp i,cond) -> do
                       rcond <- case pushCond++cond of
                         [] -> return Nothing
                         [c] -> return $ Just c
                         cs -> fmap Just $ and' cs
                       ri <- constant $ fromIntegral $ i+1
                       Just narr <- storeArrayCond rcond carr (ri:::Nil) el
                       return narr
                   ) arr ch
    return $ Stack (StackArray narr) (StackListIndex top2)
  stackPop popCond (Stack arr (StackListIndex top)) = do
    top1 <- mapChoices (\_ (NoComp i) -> return (NoComp (if i>0
                                                         then i+1
                                                         else 0))
                       ) top
    top2 <- case popCond of
      [] -> return top1
      cs -> do
        c <- and' cs
        Just res <- compITE c top1 top
        return res
    return $ Stack arr (StackListIndex top2)
  stackTop = return . _stackTop
  stackElementRev _ _ _ f (RevArray r) = f r
  stackElements _ f (StackArray (CompArray _ arr)) = f arr
  stackIndexType _ _ = Nothing

instance (ConvertC stA stB,Convert idxA idxB,
          IsStack stA idxA,IsStack stA idxB,IsStack stB idxA,IsStack stB idxB)
         => IsStack (FallbackC stA stB) (Fallback idxA idxB) where
  stackElement (Start idx) (StartC st) = do
    acc <- stackElement idx st
    return $ AccFun _startC StartC acc
  stackElement (Alternative idx) (StartC st) = do
    acc <- stackElement idx st
    return $ AccFun _startC StartC acc
  stackElement (Start idx) (AlternativeC st) = do
    acc <- stackElement idx st
    return $ AccFun _alternativeC AlternativeC acc
  stackElement (Alternative idx) (AlternativeC st) = do
    acc <- stackElement idx st
    return $ AccFun _alternativeC AlternativeC acc
  stackEmpty def = do
    Stack st idx <- stackEmpty def
    return $ Stack (StartC st) (Start idx)
  stackSingleton el = do
    Stack st idx <- stackSingleton el
    return $ Stack (StartC st) (Start idx)
  stackPush cond el (Stack (StartC st) (Start top)) = do
    Stack nst ntop <- stackPush cond el (Stack st top)
    return $ Stack (StartC nst) (Start ntop)
  stackPush cond el (Stack (StartC st) (Alternative top)) = do
    Stack nst ntop <- stackPush cond el (Stack st top)
    return $ Stack (StartC nst) (Alternative ntop)
  stackPush cond el (Stack (AlternativeC st) (Start top)) = do
    Stack nst ntop <- stackPush cond el (Stack st top)
    return $ Stack (AlternativeC nst) (Start ntop)
  stackPush cond el (Stack (AlternativeC st) (Alternative top)) = do
    Stack nst ntop <- stackPush cond el (Stack st top)
    return $ Stack (AlternativeC nst) (Alternative ntop)
  stackPop cond (Stack (StartC st) (Start top)) = do
    Stack nst ntop <- stackPop cond (Stack st top)
    return $ Stack (StartC nst) (Start ntop)
  stackPop cond (Stack (StartC st) (Alternative top)) = do
    Stack nst ntop <- stackPop cond (Stack st top)
    return $ Stack (StartC nst) (Alternative ntop)
  stackPop cond (Stack (AlternativeC st) (Start top)) = do
    Stack nst ntop <- stackPop cond (Stack st top)
    return $ Stack (AlternativeC nst) (Start ntop)
  stackPop cond (Stack (AlternativeC st) (Alternative top)) = do
    Stack nst ntop <- stackPop cond (Stack st top)
    return $ Stack (AlternativeC nst) (Alternative ntop)
  stackTop (Stack (StartC st) (Start top)) = do
    rtop <- stackTop $ Stack st top
    return $ Start rtop
  stackTop (Stack (AlternativeC st) (Start top)) = do
    rtop <- stackTop $ Stack st top
    return $ Start rtop
  stackTop (Stack (StartC st) (Alternative top)) = do
    rtop <- stackTop $ Stack st top
    return $ Alternative rtop
  stackTop (Stack (AlternativeC st) (Alternative top)) = do
    rtop <- stackTop $ Stack st top
    return $ Alternative rtop
  stackElementRev (_::Proxy (FallbackC stA stB)) (_::Proxy (Fallback idxA idxB)) p f r = case r of
    RevStart r' -> stackElementRev (Proxy::Proxy stA) (Proxy::Proxy idxA) p f r'
    RevAlternative r' -> stackElementRev (Proxy::Proxy stB) (Proxy::Proxy idxB) p f r'
  stackElements (_::Proxy (Fallback idxA idxB)) f (StartC st)
    = stackElements (Proxy::Proxy idxA) f st
  stackElements (_::Proxy (Fallback idxA idxB)) f (AlternativeC st)
    = stackElements (Proxy::Proxy idxB) f st
  stackIndexType (StartC st) (Start idx) = fmap Start $ stackIndexType st idx
  stackIndexType (StartC st) (Alternative idx) = fmap Alternative $ stackIndexType st idx
  stackIndexType (AlternativeC st) (Start idx) = fmap Start $ stackIndexType st idx
  stackIndexType (AlternativeC st) (Alternative idx) = fmap Alternative $ stackIndexType st idx
