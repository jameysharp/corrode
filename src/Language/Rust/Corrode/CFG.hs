{-# LANGUAGE Rank2Types #-}
module Language.Rust.Corrode.CFG where

import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.Array.ST.Safe
import Data.Foldable
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.IntSet as IntSet
import Data.Maybe
import Text.PrettyPrint.HughesPJClass hiding (empty)

type Label = Int
data Terminator' c l
    = Unreachable
    | Branch l
    | CondBranch c l l
type Terminator c = Terminator' c Label
data BasicBlock' s t = BasicBlock s t
type BasicBlock s c = BasicBlock' s (Terminator c)
data CFG s c = CFG Label (IntMap.IntMap (BasicBlock s c))

instance Functor (Terminator' c) where
    fmap _ Unreachable = Unreachable
    fmap f (Branch l) = Branch (f l)
    fmap f (CondBranch c l1 l2) = CondBranch c (f l1) (f l2)

instance Foldable (Terminator' c) where
    foldMap _ Unreachable = mempty
    foldMap f (Branch l) = f l
    foldMap f (CondBranch _ l1 l2) = f l1 `mappend` f l2

instance Functor (BasicBlock' s) where
    fmap f (BasicBlock b t) = BasicBlock b (f t)

prettyCFG :: (s -> Doc) -> (c -> Doc) -> CFG s c -> Doc
prettyCFG fmtS fmtC (CFG entry blocks) = vcat $
    (text "start @" <> text (show entry)) : blocks'
    where
    blocks' = do
        (label, BasicBlock stmts term) <- reverse (IntMap.toList blocks)
        let blockHead = text (show label) <> text ":"
        let blockBody = fmtS stmts
        let blockTail = case term of
                Unreachable -> text "// unreachable"
                Branch to -> text ("goto " ++ show to ++ ";")
                CondBranch cond true false ->
                    text "if(" <> fmtC cond <> text ") goto " <> text (show true) <> text "; else goto " <> text (show false) <> text ";"
        blockHead : map (nest 4) [blockBody, blockTail] ++ [text ""]

data BuildState s c = BuildState
    { buildLabel :: Label
    , buildBlocks :: IntMap.IntMap (BasicBlock s c)
    }
type BuildCFGT m s c = StateT (BuildState s c) m

mapBuildCFGT :: (forall st. m (a, st) -> n (b, st)) -> BuildCFGT m s c a -> BuildCFGT n s c b
mapBuildCFGT = mapStateT

newLabel :: Monad m => BuildCFGT m s c Label
newLabel = do
    old <- get
    put old { buildLabel = buildLabel old + 1 }
    return (buildLabel old)

addBlock :: Monad m => Label -> s -> Terminator c -> BuildCFGT m s c ()
addBlock label stmt terminator = do
    modify (\ st -> st { buildBlocks = IntMap.insert label (BasicBlock stmt terminator) (buildBlocks st) })

buildCFG :: Monad m => BuildCFGT m s c Label -> m (CFG s c)
buildCFG root = do
    (label, final) <- runStateT root (BuildState 0 IntMap.empty)
    return (CFG label (buildBlocks final))

removeEmptyBlocks :: Foldable f => CFG (f s) c -> CFG (f s) c
removeEmptyBlocks (CFG start blocks) = CFG (rewrite start) blocks'
    where
    go = do
        (empties, done) <- get
        case IntMap.minViewWithKey empties of
            Nothing -> return ()
            Just ((from, to), empties') -> do
                put (empties', done)
                step from to
                go
    step from to = do
        (empties, done) <- get
        case IntMap.splitLookup to empties of
            (_, Nothing, _) -> return ()
            (e1, Just to', e2) -> do
                put (e1 `IntMap.union` e2, done)
                step to to'
        (empties', done') <- get
        let to' = IntMap.findWithDefault to to done'
        put (empties', IntMap.insert from to' done')
    isBlockEmpty (BasicBlock s (Branch to)) | null s = Just to
    isBlockEmpty _ = Nothing
    rewrites = snd $ execState go (IntMap.mapMaybe isBlockEmpty blocks, IntMap.empty)
    rewrite to = IntMap.findWithDefault to to rewrites
    discards = IntMap.keysSet (IntMap.filterWithKey (/=) rewrites)
    rewriteBlock from _ | from `IntSet.member` discards = Nothing
    rewriteBlock _ (BasicBlock b term) = Just (BasicBlock b (fmap rewrite term))
    blocks' = IntMap.mapMaybeWithKey rewriteBlock blocks

predecessors :: CFG s c -> IntMap.IntMap IntSet.IntSet
predecessors (CFG _ blocks) = IntMap.foldrWithKey grow IntMap.empty blocks
    where
    grow from (BasicBlock _ term) rest = foldr (\ to -> IntMap.insertWith IntSet.union to (IntSet.singleton from)) rest term

dominators :: CFG s c -> Maybe (IntMap.IntMap IntSet.IntSet)
dominators cfg@(CFG start blocks) = case foldl go IntMap.empty dfs of
    seen | all (check seen) (IntMap.keys blocks) -> Just seen
    _ -> Nothing
    where
    search label = do
        (seen, order) <- get
        if label `IntSet.member` seen then return () else do
            put (IntSet.insert label seen, order)
            case IntMap.lookup label blocks of
                Just (BasicBlock _ term) -> traverse_ search term
                _ -> return ()
            modify (\ (seen', order') -> (seen', label : order'))
    dfs = snd (execState (search start) (IntSet.empty, []))

    update seen label = IntSet.insert label self
        where
        allPredecessors = predecessors cfg
        selfPredecessors = maybe [] IntSet.toList (IntMap.lookup label allPredecessors)
        predecessorDominators = mapMaybe (\ parent -> IntMap.lookup parent seen) selfPredecessors
        self = case predecessorDominators of
            [] -> IntSet.empty
            _ -> foldr1 IntSet.intersection predecessorDominators

    go seen label = IntMap.insert label (update seen label) seen
    check seen label = Just (update seen label) == IntMap.lookup label seen

data TransformState st s c = TransformState
    { transformBlocks :: STArray st Label (Maybe (BasicBlock s c))
    , transformEntries :: STUArray st Label Int
    }
type TransformCFG' st s c = ReaderT (TransformState st s c) (MaybeT (ST st))
newtype TransformCFG s c = TransformCFG { unTransformCFG :: forall st. Label -> TransformCFG' st s c (BasicBlock s c) }

runTransformCFG :: [TransformCFG s c] -> CFG s c -> CFG s c
runTransformCFG transforms (CFG start blocks) = runST $ do
    let bounds = (fst (IntMap.findMin blocks), fst (IntMap.findMax blocks))
    partial <- TransformState <$> newArray bounds Nothing <*> newArray bounds 0
    writeArray (transformEntries partial) start 1
    forM_ (IntMap.toList blocks) $ \ (label, b@(BasicBlock _ terminator)) -> do
        writeArray (transformBlocks partial) label (Just b)
        traverse_ (modifyArray (transformEntries partial) (+1)) terminator
    applyTransforms partial
    finalBlocks <- getAssocs (transformBlocks partial)
    finalEntries <- getElems (transformEntries partial)
    return $ CFG start $ IntMap.fromDistinctAscList
        [ (label, b)
        | ((label, Just b), e) <- zip finalBlocks finalEntries
        , e > 0
        ]
    where
    modifyArray a f i = do
        old <- readArray a i
        writeArray a i (f old)
    checkDead :: TransformState st s c -> Label -> ST st ()
    checkDead partial label = do
        entries <- readArray (transformEntries partial) label
        when (entries == 0) $ do
            old <- readArray (transformBlocks partial) label
            case old of
                Just (BasicBlock _ term) ->
                    traverse_ (modifyArray (transformEntries partial) (subtract 1)) term
                Nothing -> return ()
            writeArray (transformBlocks partial) label Nothing
    applyTransforms partial = foldr (applyTransform partial) (return ()) transforms
    applyTransform partial transform next = do
        blocks' <- getAssocs (transformBlocks partial)
        changes <- forM blocks' $ \ (label, mblock) -> case mblock of
            Nothing -> return False
            Just (BasicBlock _ oldTerminator) -> do
                block' <- runMaybeT (runReaderT (unTransformCFG transform label) partial)
                case block' of
                    Nothing -> return False
                    Just (b@(BasicBlock _ terminator)) -> do
                        traverse_ (modifyArray (transformEntries partial) (+ 1)) terminator
                        traverse_ (modifyArray (transformEntries partial) (subtract 1)) oldTerminator
                        traverse_ (checkDead partial) oldTerminator
                        writeArray (transformBlocks partial) label (Just b)
                        return True
        if or changes then applyTransforms partial else next

block :: Label -> TransformCFG' st s c (BasicBlock s c)
block label = do
    blocks <- asks transformBlocks
    lift $ MaybeT $ readArray blocks label

entryPoints :: Label -> TransformCFG' st s c Int
entryPoints label = do
    entries <- asks transformEntries
    lift $ lift $ readArray entries label

sameTarget :: Terminator c -> Terminator c -> TransformCFG' st s c (Terminator c)
sameTarget Unreachable b = return b
sameTarget a Unreachable = return a
sameTarget (Branch a) (Branch b) | a == b = return (Branch a)
sameTarget _ _ = fail "different branch targets"

singleUse :: Monoid s => TransformCFG s c
singleUse = TransformCFG $ \ start -> do
    BasicBlock startBody (Branch next) <- block start
    1 <- entryPoints next
    BasicBlock nextBody nextTerminator <- block next
    return (BasicBlock (startBody `mappend` nextBody) nextTerminator)

ifThenElse :: Monoid s => (c -> s -> s -> s) -> TransformCFG s c
ifThenElse mkIf = TransformCFG $ \ start -> do
    BasicBlock before (CondBranch cond trueBlock falseBlock) <- block start
    BasicBlock trueBody trueTerminator <- optionalBlock trueBlock
    BasicBlock falseBody falseTerminator <- optionalBlock falseBlock
    after <- sameTarget trueTerminator falseTerminator
    return (BasicBlock (before `mappend` mkIf cond trueBody falseBody) after)
    where
    optionalBlock label = do
            1 <- entryPoints label
            block label
        <|> return (BasicBlock mempty (Branch label))

loopForever :: Monoid s => (s -> s) -> TransformCFG s c
loopForever mkLoop = TransformCFG $ \ start -> do
    BasicBlock body (Branch after) <- block start
    guard (start == after)
    return (BasicBlock (mkLoop body) Unreachable)

while :: Monoid s => (c -> b) -> (c -> b) -> (s -> b -> s -> s) -> TransformCFG s c
while pos neg mkWhile = TransformCFG $ \ start -> do
    BasicBlock preCond (CondBranch cond trueBlock falseBlock) <- block start
    let isLoop mkCond label other = do
            1 <- entryPoints label
            BasicBlock body (Branch after) <- block label
            guard (start == after)
            return (BasicBlock (mkWhile preCond (mkCond cond) body) (Branch other))
    isLoop pos trueBlock falseBlock <|> isLoop neg falseBlock trueBlock
