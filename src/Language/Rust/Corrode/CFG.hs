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
import Data.Maybe

type Label = Int
data Terminator c
    = Unreachable
    | Branch Label
    | CondBranch c Label Label
data BasicBlock s c = BasicBlock s (Terminator c)
data CFG s c = CFG Label [(Label, BasicBlock s c)]

data BuildState s c = BuildState
    { buildLabel :: Label
    , buildBlocks :: [(Label, BasicBlock s c)]
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
    modify (\ st -> st { buildBlocks = (label, BasicBlock stmt terminator) : buildBlocks st })

buildCFG :: Monad m => BuildCFGT m s c Label -> m (CFG s c)
buildCFG root = do
    (label, final) <- runStateT root (BuildState 0 [])
    return (CFG label (buildBlocks final))

data TransformState st s c = TransformState
    { transformBlocks :: STArray st Label (Maybe (BasicBlock s c))
    , transformEntries :: STUArray st Label Int
    }
type TransformCFG st s c a = ReaderT (TransformState st s c) (MaybeT (ST st)) a

runTransformCFG :: (forall st. Label -> TransformCFG st s c (BasicBlock s c)) -> CFG s c -> CFG s c
runTransformCFG transform (CFG start blocks) = runST $ do
    let labels = map fst blocks
    let bounds = (minimum labels, maximum labels)
    partial <- TransformState <$> newArray bounds Nothing <*> newArray bounds 0
    writeArray (transformEntries partial) start 1
    forM_ blocks $ \ (label, b@(BasicBlock _ terminator)) -> do
        writeArray (transformBlocks partial) label (Just b)
        updateEntries (transformEntries partial) (+1) terminator
    applyTransform partial
    finalBlocks <- getAssocs (transformBlocks partial)
    finalEntries <- getElems (transformEntries partial)
    return $ CFG start
        [ (label, b)
        | ((label, Just b), e) <- zip finalBlocks finalEntries
        , e > 0
        ]
    where
    modifyArray a i f = do
        old <- readArray a i
        writeArray a i (f old)
    updateEntries _ _ Unreachable = return ()
    updateEntries a f (Branch target) = modifyArray a target f
    updateEntries a f (CondBranch _ true false) = do
        modifyArray a true f
        modifyArray a false f
    applyTransform partial = do
        blocks' <- getAssocs (transformBlocks partial)
        changes <- forM blocks' $ \ (label, mblock) -> case mblock of
            Nothing -> return False
            Just (BasicBlock _ oldTerminator) -> do
                block' <- runMaybeT (runReaderT (transform label) partial)
                case block' of
                    Nothing -> return False
                    Just (b@(BasicBlock _ terminator)) -> do
                        updateEntries (transformEntries partial) (subtract 1) oldTerminator
                        updateEntries (transformEntries partial) (+ 1) terminator
                        writeArray (transformBlocks partial) label (Just b)
                        return True
        if or changes then applyTransform partial else return ()

block :: Label -> TransformCFG st s c (BasicBlock s c)
block label = do
    blocks <- asks transformBlocks
    lift $ MaybeT $ readArray blocks label

entryPoints :: Label -> TransformCFG st s c Int
entryPoints label = do
    entries <- asks transformEntries
    lift $ lift $ readArray entries label

sameTarget :: Terminator c -> Terminator c -> TransformCFG st s c (Terminator c)
sameTarget Unreachable b = return b
sameTarget a Unreachable = return a
sameTarget (Branch a) (Branch b) | a == b = return (Branch a)
sameTarget _ _ = fail "different branch targets"

singleUse :: Monoid s => Label -> TransformCFG st s c (BasicBlock s c)
singleUse start = do
    BasicBlock startBody (Branch next) <- block start
    1 <- entryPoints next
    BasicBlock nextBody nextTerminator <- block next
    return (BasicBlock (startBody `mappend` nextBody) nextTerminator)

emptyBlock :: Foldable f => Label -> TransformCFG st (f s) c (BasicBlock (f s) c)
emptyBlock start = do
    BasicBlock startBody startTerminator <- block start
    case startTerminator of
        Branch next -> do
            after <- nextLabel next
            return (BasicBlock startBody (Branch after))
        CondBranch cond true false -> do
            afterTrue <- optional (nextLabel true)
            afterFalse <- optional (nextLabel false)
            guard (isJust afterTrue || isJust afterFalse)
            let true' = fromMaybe true afterTrue
            let false' = fromMaybe false afterFalse
            return (BasicBlock startBody (CondBranch cond true' false'))
        _ -> empty
    where
    nextLabel next = do
        BasicBlock nextBody (Branch after) <- block next
        guard (null nextBody)
        return after

uselessIf :: Monoid s => (c -> s) -> Label -> TransformCFG st s c (BasicBlock s c)
uselessIf mkStmt start = do
    BasicBlock before (CondBranch cond trueBlock falseBlock) <- block start
    guard (trueBlock == falseBlock)
    return (BasicBlock (before `mappend` mkStmt cond) (Branch trueBlock))

ifThen :: Monoid s => (c -> s -> s) -> Label -> TransformCFG st s c (BasicBlock s c)
ifThen mkIf start = do
    BasicBlock before (CondBranch cond trueBlock falseBlock) <- block start
    1 <- entryPoints trueBlock
    BasicBlock trueBody trueTerminator <- block trueBlock
    after <- sameTarget (Branch falseBlock) trueTerminator
    return (BasicBlock (before `mappend` mkIf cond trueBody) after)

ifThenElse :: Monoid s => (c -> s -> s -> s) -> Label -> TransformCFG st s c (BasicBlock s c)
ifThenElse mkIf start = do
    BasicBlock before (CondBranch cond trueBlock falseBlock) <- block start
    1 <- entryPoints trueBlock
    1 <- entryPoints falseBlock
    BasicBlock trueBody trueTerminator <- block trueBlock
    BasicBlock falseBody falseTerminator <- block falseBlock
    after <- sameTarget trueTerminator falseTerminator
    return (BasicBlock (before `mappend` mkIf cond trueBody falseBody) after)

loopForever :: Monoid s => (s -> s) -> Label -> TransformCFG st s c (BasicBlock s c)
loopForever mkLoop start = do
    BasicBlock body (Branch after) <- block start
    guard (start == after)
    return (BasicBlock (mkLoop body) Unreachable)

while :: Monoid s => (s -> c -> s -> s) -> Label -> TransformCFG st s c (BasicBlock s c)
while mkWhile start = do
    BasicBlock preCond (CondBranch cond trueBlock falseBlock) <- block start
    1 <- entryPoints trueBlock
    BasicBlock trueBody (Branch afterTrue) <- block trueBlock
    guard (start == afterTrue)
    return (BasicBlock (mkWhile preCond cond trueBody) (Branch falseBlock))
