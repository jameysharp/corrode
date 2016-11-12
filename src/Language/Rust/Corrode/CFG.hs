{-# LANGUAGE Rank2Types #-}
module Language.Rust.Corrode.CFG where

import Control.Monad
import Control.Monad.Trans.State
import Data.Either
import Data.Foldable
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.IntSet as IntSet
import Data.List
import qualified Data.Map.Lazy as Map
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

data Unordered
data DepthFirst
data CFG k s c = CFG Label (IntMap.IntMap (BasicBlock s c))

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

prettyCFG :: (s -> Doc) -> (c -> Doc) -> CFG k s c -> Doc
prettyCFG fmtS fmtC (CFG entry blocks) = vcat $
    (text "start @" <> text (show entry)) : blocks'
    where
    blocks' = do
        (label, BasicBlock stmts term) <- IntMap.toList blocks
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

buildCFG :: Monad m => BuildCFGT m s c Label -> m (CFG Unordered s c)
buildCFG root = do
    (label, final) <- runStateT root (BuildState 0 IntMap.empty)
    return (CFG label (buildBlocks final))

removeEmptyBlocks :: Foldable f => CFG k (f s) c -> CFG Unordered (f s) c
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

predecessors :: CFG k s c -> IntMap.IntMap IntSet.IntSet
predecessors (CFG _ blocks) = IntMap.foldrWithKey grow IntMap.empty blocks
    where
    grow from (BasicBlock _ term) rest = foldr (\ to -> IntMap.insertWith IntSet.union to (IntSet.singleton from)) rest term

depthFirstOrder :: CFG k s c -> CFG DepthFirst s c
depthFirstOrder (CFG start blocks) = CFG start' blocks'
    where
    search label = do
        (seen, order) <- get
        unless (label `IntSet.member` seen) $ do
            put (IntSet.insert label seen, order)
            case IntMap.lookup label blocks of
                Just (BasicBlock _ term) -> traverse_ search term
                _ -> return ()
            modify (\ (seen', order') -> (seen', label : order'))
    final = snd (execState (search start) (IntSet.empty, []))
    start' = 0
    mapping = IntMap.fromList (zip final [start'..])
    rewrite label = IntMap.findWithDefault (error "basic block disappeared") label mapping
    rewriteBlock label (BasicBlock body term) = (label, BasicBlock body (fmap rewrite term))
    blocks' = IntMap.fromList (IntMap.elems (IntMap.intersectionWith rewriteBlock mapping blocks))

dominators :: CFG DepthFirst s c -> Either String (IntMap.IntMap IntSet.IntSet)
dominators cfg@(CFG start blocks) = case foldl go IntMap.empty (IntMap.keys blocks) of
    seen | all (check seen) (IntMap.keys blocks) -> Right seen
    _ -> Left "irreducible control flow"
    where
    update _ label | label == start = IntSet.singleton start
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

backEdges :: CFG DepthFirst s c -> Either String (IntMap.IntMap IntSet.IntSet)
backEdges cfg = do
    dom <- dominators cfg
    return
        $ IntMap.filter (not . IntSet.null)
        $ IntMap.intersectionWith IntSet.intersection (flipEdges dom)
        $ predecessors cfg
    where
    flipEdges :: IntMap.IntMap IntSet.IntSet -> IntMap.IntMap IntSet.IntSet
    flipEdges edges = IntMap.unionsWith IntSet.union [ IntMap.fromSet (const (IntSet.singleton from)) to | (from, to) <- IntMap.toList edges ]

type NaturalLoops = IntMap.IntMap IntSet.IntSet

naturalLoops :: CFG DepthFirst s c -> Either String NaturalLoops
naturalLoops cfg = do
    back <- backEdges cfg
    return (IntMap.mapWithKey makeLoop back)
    where
    makeLoop header inside = execState (growLoop inside) (IntSet.singleton header)
    allPredecessors = predecessors cfg
    growLoop toAdd = do
        inLoop <- get
        let new = toAdd `IntSet.difference` inLoop
        unless (IntSet.null new) $ do
            put (inLoop `IntSet.union` new)
            growLoop (IntSet.unions (mapMaybe (\ label -> IntMap.lookup label allPredecessors) (IntSet.toList new)))

data Exit = BreakFrom Label | Continue
    deriving Show
type Exits = Map.Map (Label, Label) Exit

exitEdges :: CFG DepthFirst s c -> NaturalLoops -> Exits
exitEdges (CFG _ blocks) = Map.unions . map eachLoop . IntMap.toList
    where
    successors = IntMap.map (\ (BasicBlock _ term) -> nub (toList term)) blocks
    eachLoop (header, nodes) = Map.fromList
        [ ((from, to), if to == header then Continue else BreakFrom header)
        | from <- IntSet.toList nodes
        , to <- IntMap.findWithDefault [] from successors
        , to == header || to `IntSet.notMember` nodes
        ]

unifyBreaks :: CFG DepthFirst s c -> NaturalLoops -> (IntMap.IntMap Label, Exits)
unifyBreaks cfg loops = (breaks, Map.fromList exits')
    where
    exits = exitEdges cfg loops
    (breakList, continues) = partitionEithers
        [ case exit of
            BreakFrom header -> Left (header, IntSet.singleton to)
            Continue -> Right orig
        | orig@((_, to), exit) <- Map.toList exits
        ]
    breaks = IntMap.map IntSet.findMax (IntMap.fromListWith IntSet.union breakList)
    breakExits header to = fromMaybe [] $ do
        candidates <- IntMap.lookup to (predecessors cfg)
        insideLoop <- IntMap.lookup header loops
        return (IntSet.toList (candidates `IntSet.intersection` insideLoop))
    exits' =
        [ ((from, to), BreakFrom header)
        | (header, to) <- IntMap.toList breaks
        , from <- breakExits header to
        ] ++ continues

structureCFG :: Monoid s => (Label -> s) -> (Label -> s) -> (Label -> s -> s) -> (c -> s -> s -> s) -> CFG DepthFirst s c -> Either String s
structureCFG mkBreak mkContinue mkLoop mkIf cfg@(CFG start blocks) = do
    loops <- naturalLoops cfg
    closed (unifyBreaks cfg loops) (IntMap.keysSet loops) start
    where
    allPredecessors = predecessors cfg
    closed (breaks, exits) loops entry = do
        (body, rest) <- go entry
        case rest of
            Nothing -> return body
            Just after -> Left ("unexpected edge from " ++ show entry ++ " to " ++ show after)
        where
        go label | IntSet.member label loops = do
            body <- closed (breaks, exits) (IntSet.delete label loops) label
            let loop = mkLoop label body
            case IntMap.lookup label breaks of
                Nothing -> return (loop, Nothing)
                Just after -> do
                    (rest1, rest2) <- go after
                    return (loop `mappend` rest1, rest2)
        go label = do
            BasicBlock body term <- maybe (Left ("missing block " ++ show label)) Right (IntMap.lookup label blocks)
            (rest1, rest2) <- case term of
                Unreachable -> return (mempty, Nothing)
                Branch to -> next 1 label to
                CondBranch c t f -> do
                    (t', afterT) <- next 1 label t
                    (f', afterF) <- next 1 label f
                    case (afterT, afterF) of
                        (_, Nothing) -> return (mkIf c mempty f' `mappend` t', afterT)
                        (Nothing, _) -> return (mkIf c t' mempty `mappend` f', afterF)
                        (Just (nextT, branchesT), Just (nextF, branchesF)) | nextT == nextF -> do
                            (rest1, rest2) <- next (branchesT + branchesF) label nextT
                            return (mkIf c t' f' `mappend` rest1, rest2)
                        _ -> Left ("unsupported conditional branch from " ++ show label ++ " to " ++ show afterT ++ " and " ++ show afterF)
            return (body `mappend` rest1, rest2)

        next branches label to = case Map.lookup (label, to) exits of
            Nothing ->
                let p = IntSet.toList (fromMaybe IntSet.empty (IntMap.lookup to allPredecessors))
                    q = filter (\ from -> Map.notMember (from, to) exits) p
                in if length q == branches
                then go to
                else return (mempty, Just (to, branches))
            Just (BreakFrom header) -> return (mkBreak header, Nothing)
            Just Continue -> return (mkContinue to, Nothing)
