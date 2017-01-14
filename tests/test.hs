import Control.Monad
import Control.Monad.Trans.Class
import qualified Data.IntMap as IntMap
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
    ]

data Stmt
    = Stmt Int
    | Loop Label [Stmt]
    | Break Label
    | Continue Label
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

fingerprintStmt :: [Stmt] -> (IntMap.IntMap Int, IntMap.IntMap Int)
fingerprintStmt = foldr go (IntMap.empty, IntMap.empty)
    where
    go (Stmt l) (stmts, conds) = (IntMap.insertWith (+) l 1 stmts, conds)
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

genCFG :: QC.Gen (CFG DepthFirst [Stmt] Cond)
genCFG = QC.sized $ \ n -> fmap depthFirstOrder $ buildCFG $ do
    labels <- replicateM (1 + n) newLabel
    let chooseLabel = QC.elements labels
    forM_ labels $ \ label -> do
        term <- lift $ QC.oneof
            [ return Unreachable
            , Branch <$> chooseLabel
            , CondBranch (Cond label) <$> chooseLabel <*> chooseLabel
            ]
        addBlock label [Stmt label] term
    return (head labels)

shrinkCFG :: CFG DepthFirst [Stmt] Cond -> [CFG DepthFirst [Stmt] Cond]
shrinkCFG (CFG entry blocks) = map depthFirstOrder (removeEdges ++ skipBlocks)
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
structureStmtCFG = structureCFG
    (return . Break)
    (return . Continue)
    (\ l b -> [Loop l b])
    (\ c t f -> [If c t f])
    (return . Goto)
    (foldr (\ (l, t) f -> [If (Match l) t f]) [])

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
