module Language.Rust.Corrode.CFG.C (dumpCFGs) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.Foldable
import Data.Maybe
import Language.C
import Language.Rust.Corrode.CFG
import Text.PrettyPrint

dumpCFGs :: CTranslUnit -> IO ()
dumpCFGs (CTranslUnit decls _) = mapM_ perDecl decls
    where
    perDecl (CFDefExt f) = dumpFunction f
    perDecl _ = return ()

type CSourceCFGT = Reader ControlFlow
type CSourceBuildCFGT = BuildCFGT CSourceCFGT [CExpr] CExpr

dumpFunction :: CFunDef -> IO ()
dumpFunction (CFunDef _ declr _ body _) = do
    let (CFG entry blocks) = simplifiedCFG

    putStrLn (render (pretty declr) ++ ": " ++ show entry)
    forM_ (reverse blocks) $ \ (label, BasicBlock stmts term) -> do
        putStrLn (show label ++ ":")
        putStrLn (render (nest 4 (vcat (map pretty stmts))))
        case term of
            Unreachable -> putStrLn "    // unreachable"
            Branch to -> putStrLn ("    goto " ++ show to ++ ";")
            CondBranch cond true false -> putStrLn (render (nest 4 ifstmt))
                where
                ifstmt = text "if(" <> pretty cond <> text ") goto " <> text (show true) <> text "; else goto " <> text (show false) <> text ";"
        putStrLn ""

    where
    builder = buildCFG $ do
        (early, term) <- walkStatement body ([], Unreachable)
        entry <- newLabel
        addBlock entry early term
        return entry

    rawCFG = runReader builder emptyControlFlow

    simplifiedCFG = runTransformCFG (runReaderT simplify) rawCFG

    simplify = ReaderT singleUse <|> ReaderT emptyBlock

    emptyControlFlow = ControlFlow
        { breakLabel = Nothing
        , continueLabel = Nothing
        }

data ControlFlow = ControlFlow
    { breakLabel :: Maybe Label
    , continueLabel :: Maybe Label
    }

localControlFlow :: ControlFlow -> CSourceBuildCFGT a -> CSourceBuildCFGT a
localControlFlow flow = mapBuildCFGT (local (const flow))

walkStatement :: CStat -> ([CExpr], Terminator CExpr) -> CSourceBuildCFGT ([CExpr], Terminator CExpr)
walkStatement (CExpr (Just expr) _) (rest, end) = return (expr : rest, end)
walkStatement (CExpr Nothing _) (rest, end) = return (rest, end)

walkStatement (CCompound [] items _) (rest, end) = foldrM walkBlockItem (rest, end) items
walkStatement (CIf cond trueStmt mfalseStmt _) (rest, end) = do
    after <- newLabel
    addBlock after rest end

    falseLabel <- case mfalseStmt of
        Nothing -> return after
        Just falseStmt -> do
            (falseEntry, falseTerm) <- walkStatement falseStmt ([], Branch after)
            falseLabel <- newLabel
            addBlock falseLabel falseEntry falseTerm
            return falseLabel

    (trueEntry, trueTerm) <- walkStatement trueStmt ([], Branch after)
    trueLabel <- newLabel
    addBlock trueLabel trueEntry trueTerm

    return ([], CondBranch cond trueLabel falseLabel)

walkStatement (CWhile cond body doWhile _) (rest, end) = do
    after <- newLabel
    addBlock after rest end

    headerLabel <- newLabel
    let flow = ControlFlow
            { breakLabel = Just after
            , continueLabel = Just headerLabel
            }
    (bodyEntry, bodyTerm) <- localControlFlow flow $
        walkStatement body ([], Branch headerLabel)

    bodyLabel <- newLabel
    addBlock bodyLabel bodyEntry bodyTerm

    addBlock headerLabel [] (CondBranch cond bodyLabel after)

    return ([], Branch (if doWhile then bodyLabel else headerLabel))

walkStatement (CFor initial mcond mincr body _) (rest, end) = do
    after <- newLabel
    addBlock after rest end

    headerLabel <- newLabel
    incrLabel <- newLabel
    addBlock incrLabel (maybeToList mincr) (Branch headerLabel)

    let flow = ControlFlow
            { breakLabel = Just after
            , continueLabel = Just incrLabel
            }
    (bodyEntry, bodyTerm) <- localControlFlow flow $
        walkStatement body ([], Branch incrLabel)

    bodyLabel <- newLabel
    addBlock bodyLabel bodyEntry bodyTerm

    addBlock headerLabel [] $ case mcond of
        Just cond -> CondBranch cond bodyLabel after
        Nothing -> Branch bodyLabel

    return $ case initial of
        Left mexpr -> (maybeToList mexpr, Branch headerLabel)
        Right _ -> ([], Branch headerLabel)

walkStatement (CCont _) _ = do
    Just label <- lift (asks continueLabel)
    return ([], Branch label)

walkStatement (CBreak _) _ = do
    Just label <- lift (asks breakLabel)
    return ([], Branch label)

walkStatement (CReturn _mexpr _) _ = return ([], Unreachable)

walkBlockItem :: CBlockItem -> ([CExpr], Terminator CExpr) -> CSourceBuildCFGT ([CExpr], Terminator CExpr)
walkBlockItem (CBlockStmt stmt) (rest, end) = walkStatement stmt (rest, end)
walkBlockItem _ (rest, end) = return (rest, end)
