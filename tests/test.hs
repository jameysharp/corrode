import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Lazy
import Data.Either
import Data.Foldable
import Data.Functor.Identity
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.List
import Language.Rust.Corrode.CFG
import Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import Text.PrettyPrint.HughesPJClass hiding (empty)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
    [ QC.testProperty "structuring CFGs conserves code" cfgStructureConservesCode
    , QC.testProperty "CFG structuring round-trips" cfgRoundTrip
    ]

data Stmt
    = Stmt Int
    | Return
    | Loop Label [Stmt]
    | Break (Maybe Label)
    | Continue (Maybe Label)
    | If Cond [Stmt] [Stmt]
    | Goto Int
    deriving (Show, Eq)

data Cond
    = Cond Int
    | Match Int
    deriving (Show, Eq)

instance Pretty Stmt where
    pPrint (Loop l b) = vcat
        [ text ("Loop " ++ show l ++ " {")
        , nest 4 (prettyStmts b)
        , text "}"
        ]
    pPrint (If c t f) = vcat
        [ text ("If " ++ show c ++ " {")
        , nest 4 (prettyStmts t)
        , text "} else {"
        , nest 4 (prettyStmts f)
        , text "}"
        ]
    pPrint s = text (show s)

prettyStmts :: [Stmt] -> Doc
prettyStmts = vcat . map pPrint

stmtToCFG :: [Stmt] -> CFG DepthFirst [Stmt] Cond
stmtToCFG = depthFirstOrder . staticCFG . runIdentity . buildCFG . convert [] ([], Unreachable)
    where
    makeBlock ([], Branch to) = return to
    makeBlock (after, term) = do
        b <- newLabel
        addBlock b after term
        return b

    convert loops term stmts = convert' loops term stmts >>= makeBlock
    convert' loops = foldrM go
        where
        getLoop Nothing = case loops of
            (_, labels) : _ -> labels
            [] -> error "stmtToCFG: loop exit without an enclosing loop"
        getLoop (Just l) = case lookup l loops of
            Just labels -> labels
            Nothing -> error ("stmtToCFG: loop " ++ show l ++ " not in " ++ show loops)
        go Return _ = return ([Return], Unreachable)
        go (Loop l stmts) (after, term) = do
            brk <- makeBlock (after, term)
            cont <- newLabel
            (after', term') <- convert' ((l, (brk, cont)) : loops) ([], Branch cont) stmts
            addBlock cont after' term'
            return ([], Branch cont)
        go (Break l) _ = return ([], Branch (fst (getLoop l)))
        go (Continue l) _ = return ([], Branch (snd (getLoop l)))
        go (If c t f) term = do
            term' <- (,) [] <$> Branch <$> makeBlock term
            t' <- convert loops term' t
            f' <- convert loops term' f
            return ([], CondBranch c t' f')
        go s (after, term) = return (s : after, term)

staticCFG :: CFG k [Stmt] Cond -> CFG Unordered [Stmt] Cond
staticCFG (CFG start blocks) = removeEmptyBlocks $ evalState (buildCFG $ foo initialState start) Map.empty
    where
    initialState = -1
    getGoto (Goto l) = Right l
    getGoto s = Left s
    extractGoto current stmts = case partitionEithers $ map getGoto stmts of
        (stmts', gotos) -> (last (current : gotos), stmts')
    foo current b = do
        let key = (current, b)
        seen <- lift get
        case key `Map.lookup` seen of
            Just b' -> return b'
            Nothing -> case IntMap.lookup b blocks of
                Nothing -> fail ("staticCFG: block " ++ show b ++ " missing")
                Just (BasicBlock stmts term) -> do
                    b' <- newLabel
                    lift $ put $ Map.insert key b' seen
                    let (current', stmts') = extractGoto current stmts
                    term' <- case term of
                        CondBranch (Match n) t f
                            | current' == n -> Branch <$> foo current' t
                            | otherwise -> Branch <$> foo current' f
                        _ -> mapM (foo current') term
                    addBlock b' stmts' term'
                    return b'

data BigramFst = FstStmt Int | FstCond Int Bool
    deriving (Eq, Ord, Show)
data BigramSnd = SndStmt Int | SndCond Int | SndReturn
    deriving (Eq, Ord, Show)

bigrams :: CFG DepthFirst [Stmt] Cond -> Map.Map BigramFst BigramSnd
bigrams (CFG start blocks) = snd $ IntMap.findWithDefault undefined start $ allBlocks $ allBlocks IntMap.empty
    where
    allBlocks seen = IntMap.foldrWithKey perBlock seen blocks

    perBlock l (BasicBlock stmts term) seen = IntMap.insert l (foldr perStmt (perTerm go term) stmts) seen
        where
        go to = IntMap.findWithDefault (Nothing, Map.empty) to seen

    newBigram _ (Nothing, seen) = seen
    newBigram bigramFst (Just bigramSnd, seen) = Map.insert bigramFst bigramSnd seen

    perStmt (Stmt s) next = (Just (SndStmt s), newBigram (FstStmt s) next)
    perStmt Return _ = (Just SndReturn, Map.empty)
    perStmt s _ = error ("bigrams: unsupported statment " ++ show s)

    perTerm go term = case term of
        Unreachable -> (Nothing, Map.empty)
        Branch to -> go to
        CondBranch (Cond c) t f -> (Just (SndCond c), bar True t `Map.union` bar False f)
            where
            bar matched to = newBigram (FstCond c matched) (go to)
        CondBranch c _ _ -> error ("bigrams: unsupported condition " ++ show c)

fingerprintStmt :: [Stmt] -> (IntMap.IntMap Int, IntMap.IntMap Int)
fingerprintStmt = foldr go (IntMap.empty, IntMap.empty)
    where
    go (Stmt l) (stmts, conds) = (IntMap.insertWith (+) l 1 stmts, conds)
    go Return rest = rest
    go (Loop _ stmts) rest = foldr go rest stmts
    go (Break _) rest = rest
    go (Continue _) rest = rest
    go (If c t f) rest = case c of
        Cond l -> (stmts, IntMap.insertWith (+) l 1 conds)
        Match _ -> (stmts, conds)
        where (stmts, conds) = foldr go (foldr go rest t) f
    go (Goto _) rest = rest

fingerprintCFG :: CFG k [Stmt] Cond -> (IntMap.IntMap Int, IntMap.IntMap Int)
fingerprintCFG (CFG _ blocks) = mconcat $ map go $ IntMap.elems blocks
    where
    go (BasicBlock stmt term) =
        let (stmts, conds) = fingerprintStmt stmt in case term of
        CondBranch (Cond c) _ _ -> (stmts, IntMap.insertWith (+) c 1 conds)
        _ -> (stmts, conds)

genStmts :: CFG DepthFirst s c -> CFG DepthFirst [Stmt] c
genStmts (CFG start blocks) = CFG start (IntMap.mapWithKey go blocks)
    where
    go _ (BasicBlock _ Unreachable) = BasicBlock [Return] Unreachable
    go l (BasicBlock _ term) = BasicBlock [Stmt l] term

genCFG :: QC.Gen (CFG DepthFirst [Stmt] Cond)
genCFG = QC.sized $ \ n -> fmap (genStmts . depthFirstOrder) $ buildCFG $ do
    labels <- replicateM (1 + n) newLabel
    let chooseLabel = QC.elements labels
    forM_ labels $ \ label -> do
        term <- lift $ QC.oneof
            [ return Unreachable
            , Branch <$> chooseLabel
            , CondBranch (Cond label) <$> chooseLabel <*> chooseLabel
            ]
        addBlock label () term
    return (head labels)

shrinkCFG :: CFG DepthFirst [Stmt] Cond -> [CFG DepthFirst [Stmt] Cond]
shrinkCFG (CFG entry blocks) = map (genStmts . depthFirstOrder) (removeEdges ++ skipBlocks)
    where
    removeEdges = map (CFG entry . IntMap.fromList) $ go $ IntMap.toList blocks
        where
        go [] = []
        go ((l, BasicBlock b term) : xs) =
            [ (l, BasicBlock b term') : xs | term' <- removeEdge term ] ++
            [ (l, BasicBlock b term) : xs' | xs' <- go xs ]
    removeEdge (CondBranch _ t f) = Unreachable : map Branch (nub [t, f])
    removeEdge (Branch _) = [Unreachable]
    removeEdge Unreachable = []

    skipBlocks = [ skipBlock from to | (from, BasicBlock _ (Branch to)) <- IntMap.toList blocks ]
    skipBlock from to = CFG (rewrite entry) (IntMap.map (\ (BasicBlock b term) -> BasicBlock b (fmap rewrite term)) blocks)
        where rewrite label = if label == from then to else label

structureStmtCFG :: CFG DepthFirst [Stmt] Cond -> [Stmt]
structureStmtCFG = snd . structureCFG
    (return . Break)
    (return . Continue)
    (\ l b -> [Loop l b])
    (\ c t f -> [If c t f])
    (return . Goto)
    (flip (foldr (\ (l, t) f -> [If (Match l) t f])))

subtractMap :: IntMap.IntMap Int -> IntMap.IntMap Int -> IntMap.IntMap Int
subtractMap = IntMap.mergeWithKey (\ _ a b -> Just (a - b)) id (IntMap.map negate)

cfgStructureConservesCode :: QC.Property
cfgStructureConservesCode = QC.forAllShrink genCFG shrinkCFG $ \ cfg ->
    let (cfgStmts, cfgConds) = fingerprintCFG cfg
        structured = structureStmtCFG cfg
        (structuredStmts, structuredConds) = fingerprintStmt structured
    in QC.counterexample (render (prettyStructure (relooperRoot cfg) $+$ prettyStmts structured))
        (conserved "statements" structuredStmts cfgStmts QC..&&. conserved "conditions" structuredConds cfgConds)
    where
    conserved kind structured cfg = case IntMap.toList $ IntMap.filter (/= 0) $ subtractMap structured cfg of
        [] -> QC.property True
        miss -> QC.counterexample (kind ++ " not conserved: " ++ show miss) False

cfgRoundTrip :: QC.Property
cfgRoundTrip = QC.forAllShrink genCFG shrinkCFG $ \ cfg ->
    let bi = bigrams cfg
        stmts = structureStmtCFG cfg
        cfg' = stmtToCFG stmts
        bi' = bigrams cfg'
    in foldr QC.counterexample (QC.property (bi == bi')) $
        map (++ "\n")
            [ render (prettyStructure (relooperRoot cfg))
            , render (prettyStmts stmts)
            , show bi
            , show bi'
            , show cfg'
            ]
