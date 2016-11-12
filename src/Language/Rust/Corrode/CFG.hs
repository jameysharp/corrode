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
import Data.Ord
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

depthFirstOrder :: CFG s c -> [Label]
depthFirstOrder (CFG start blocks) = snd (execState (search start) (IntSet.empty, []))
    where
    search label = do
        (seen, order) <- get
        unless (label `IntSet.member` seen) $ do
            put (IntSet.insert label seen, order)
            case IntMap.lookup label blocks of
                Just (BasicBlock _ term) -> traverse_ search term
                _ -> return ()
            modify (\ (seen', order') -> (seen', label : order'))

dominators :: CFG s c -> Either String (IntMap.IntMap IntSet.IntSet)
dominators cfg@(CFG _ blocks) = case foldl go IntMap.empty (depthFirstOrder cfg) of
    seen | all (check seen) (IntMap.keys blocks) -> Right seen
    _ -> Left "irreducible control flow"
    where
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

backEdges :: CFG s c -> Either String (IntMap.IntMap IntSet.IntSet)
backEdges cfg = do
    dom <- dominators cfg
    return
        $ IntMap.filter (not . IntSet.null)
        $ IntMap.intersectionWith IntSet.intersection (flipEdges dom)
        $ predecessors cfg
    where
    flipEdges :: IntMap.IntMap IntSet.IntSet -> IntMap.IntMap IntSet.IntSet
    flipEdges edges = IntMap.unionsWith IntSet.union [ IntMap.fromSet (const (IntSet.singleton from)) to | (from, to) <- IntMap.toList edges ]

naturalLoops :: CFG s c -> Either String (IntMap.IntMap IntSet.IntSet)
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

newtype Loops = Loops (IntMap.IntMap (IntSet.IntSet, Loops))
    deriving Show

nestLoops :: CFG s c -> Either String Loops
nestLoops cfg = do
    loops <- naturalLoops cfg
    return (foldl insertLoop (Loops IntMap.empty) (sortBy (comparing (IntSet.size . snd)) (IntMap.toList loops)))
    where
    insertLoop (Loops loops) (header, inside) =
        case IntMap.partitionWithKey (\ header' _ -> header' `IntSet.member` inside) loops of
        (nested, disjoint) -> Loops (IntMap.insert header (inside, Loops nested) disjoint)

data Exit = BreakFrom Label | Continue
    deriving Show

exitEdges :: CFG s c -> Loops -> Map.Map (Label, Label) Exit
exitEdges (CFG _ blocks) = go
    where
    successors = IntMap.map (\ (BasicBlock _ term) -> nub (toList term)) blocks
    go (Loops loops) = Map.unions (map eachLoop (IntMap.toList loops))
    eachLoop (header, (nodes, nested)) = exits `Map.union` go nested
        where
        exits = Map.fromList
            [ ((from, to), if to == header then Continue else BreakFrom header)
            | from <- IntSet.toList nodes
            , to <- IntMap.findWithDefault [] from successors
            , to == header || to `IntSet.notMember` nodes
            ]

unifyBreaks :: CFG s c -> Loops -> (IntMap.IntMap Label, Map.Map (Label, Label) Exit)
unifyBreaks cfg loops = (breaks, Map.fromList exits')
    where
    exits = exitEdges cfg loops
    (breakList, continueList) = partitionEithers
        [ case exit of
            BreakFrom header -> Left (header, IntSet.singleton to)
            Continue -> Right (to, IntSet.singleton from)
        | ((from, to), exit) <- Map.toList exits
        ]
    order = IntMap.fromList (zip (depthFirstOrder cfg) [0 :: Int ..])
    unify targets = fst (maximumBy (comparing snd) (IntMap.toList (order `IntMap.intersection` IntMap.fromSet id targets)))
    combine = IntMap.fromListWith IntSet.union
    breaks = IntMap.map unify (combine breakList)
    continues = combine continueList
    advancing = IntMap.differenceWith (\ a b -> Just (IntSet.difference a b)) (predecessors cfg) continues
    exits' = [ ((from, to), Continue) | (to, froms) <- IntMap.toList continues, from <- IntSet.toList froms ]
        ++ [ ((from, to), BreakFrom header) | (header, to) <- IntMap.toList breaks, from <- maybe [] IntSet.toList (IntMap.lookup to advancing) ]

structureCFG :: Monoid s => (Label -> s) -> (Label -> s) -> (Label -> s -> s) -> (c -> s -> s -> s) -> CFG s c -> Either String s
structureCFG mkBreak mkContinue mkLoop mkIf cfg@(CFG start blocks) = do
    loops <- nestLoops cfg
    closed (unifyBreaks cfg loops) loops start
    where
    allPredecessors = predecessors cfg
    closed (breaks, exits) loops label = do
        (body, rest) <- go (breaks, exits) loops label
        case rest of
            Nothing -> return body
            Just after -> Left ("unexpected edge from " ++ show label ++ " to " ++ show after)
    go (breaks, exits) (Loops loops) label =
        case IntMap.lookup label loops of
        Just (_, nested) -> do
            body <- closed (breaks, exits) nested label
            let loop = mkLoop label body
            case IntMap.lookup label breaks of
                Nothing -> return (loop, Nothing)
                Just after -> do
                    (rest1, rest2) <- go (breaks, exits) (Loops loops) after
                    return (loop `mappend` rest1, rest2)
        Nothing -> do
            BasicBlock body term <- maybe (Left ("missing block " ++ show label)) Right (IntMap.lookup label blocks)
            (rest1, rest2) <- case term of
                Unreachable -> return (mempty, Nothing)
                Branch to -> next 1 to
                CondBranch c t f -> do
                    (t', afterT) <- next 1 t
                    (f', afterF) <- next 1 f
                    case (afterT, afterF) of
                        (Just (nextT, branchesT), Just (nextF, branchesF)) | nextT == nextF -> do
                            (rest1, rest2) <- next (branchesT + branchesF) nextT
                            return (mkIf c t' f' `mappend` rest1, rest2)
                        (Nothing, Nothing) -> return (mkIf c t' mempty `mappend` f', Nothing)
                        _ -> Left ("unsupported conditional branch from " ++ show label ++ " to " ++ show afterT ++ " and " ++ show afterF)
            return (body `mappend` rest1, rest2)
        where
        next branches to = case Map.lookup (label, to) exits of
            Nothing ->
                let p = IntSet.toList (fromMaybe IntSet.empty (IntMap.lookup to allPredecessors))
                    q = filter (\ from -> Map.notMember (from, to) exits) p
                in if length q == branches
                then go (breaks, exits) (Loops loops) to
                else return (mempty, Just (to, branches))
            Just (BreakFrom header) -> return (mkBreak header, Nothing)
            Just Continue -> return (mkContinue to, Nothing)
