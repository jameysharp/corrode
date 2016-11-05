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
import Text.PrettyPrint.HughesPJClass hiding (empty)

type Label = Int
data Terminator c
    = Unreachable
    | Branch Label
    | CondBranch c Label Label
data BasicBlock s c = BasicBlock s (Terminator c)
data CFG s c = CFG Label [(Label, BasicBlock s c)]

prettyCFG :: (s -> Doc) -> (c -> Doc) -> CFG s c -> Doc
prettyCFG fmtS fmtC (CFG entry blocks) = vcat $
    (text "start @" <> text (show entry)) : blocks'
    where
    blocks' = do
        (label, BasicBlock stmts term) <- reverse blocks
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
type TransformCFG' st s c = ReaderT (TransformState st s c) (MaybeT (ST st))
newtype TransformCFG s c = TransformCFG { unTransformCFG :: forall st. Label -> TransformCFG' st s c (BasicBlock s c) }

runTransformCFG :: [TransformCFG s c] -> CFG s c -> CFG s c
runTransformCFG transforms (CFG start blocks) = runST $ do
    let labels = map fst blocks
    let bounds = (minimum labels, maximum labels)
    partial <- TransformState <$> newArray bounds Nothing <*> newArray bounds 0
    writeArray (transformEntries partial) start 1
    forM_ blocks $ \ (label, b@(BasicBlock _ terminator)) -> do
        writeArray (transformBlocks partial) label (Just b)
        updateEntries (modifyArray (transformEntries partial) (+1)) terminator
    applyTransforms partial
    finalBlocks <- getAssocs (transformBlocks partial)
    finalEntries <- getElems (transformEntries partial)
    return $ CFG start
        [ (label, b)
        | ((label, Just b), e) <- zip finalBlocks finalEntries
        , e > 0
        ]
    where
    modifyArray a f i = do
        old <- readArray a i
        writeArray a i (f old)
    updateEntries _ Unreachable = return ()
    updateEntries f (Branch target) = f target
    updateEntries f (CondBranch _ true false) = do
        f true
        f false
    checkDead :: TransformState st s c -> Label -> ST st ()
    checkDead partial label = do
        entries <- readArray (transformEntries partial) label
        when (entries == 0) $ do
            old <- readArray (transformBlocks partial) label
            case old of
                Just (BasicBlock _ term) ->
                    updateEntries (modifyArray (transformEntries partial) (subtract 1)) term
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
                        updateEntries (modifyArray (transformEntries partial) (+ 1)) terminator
                        updateEntries (modifyArray (transformEntries partial) (subtract 1)) oldTerminator
                        updateEntries (checkDead partial) oldTerminator
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

emptyBlock :: Foldable f => TransformCFG (f s) c
emptyBlock = TransformCFG $ \ start -> do
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
        _ -> mzero
    where
    nextLabel next = do
        BasicBlock nextBody (Branch after) <- block next
        guard (null nextBody)
        return after

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
