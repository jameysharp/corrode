{-# LANGUAGE ViewPatterns #-}

module Language.Rust.Idiomatic (
    itemIdioms
) where

import qualified Language.Rust.AST as Rust

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = Nothing
unsnoc (x:xs) = case unsnoc xs of
    Just (a, b) -> Just (x:a, b)
    Nothing -> Just ([], x)

tailExpr :: Rust.Expr -> Maybe (Maybe Rust.Expr)
-- If the last statement in this block is a return statement, extract
-- its expression (if any) to the final expression position.
tailExpr (Rust.Return e) = Just e
-- If the last statement is a block, that's a tail-block.
tailExpr (Rust.BlockExpr b) = Just (Just (Rust.BlockExpr (tailBlock b)))
-- If the last statement is an if-expression, its true and false blocks
-- are themselves tail-blocks.
-- TODO: treat match-expressions like if-expressions.
tailExpr (Rust.IfThenElse c t f) = Just (Just (Rust.IfThenElse c (tailBlock t) (tailBlock f)))
-- Otherwise, there's nothing to rewrite.
tailExpr _ = Nothing

-- Eliminate any return statement that has no statements which
-- dynamically follow it.
tailBlock :: Rust.Block -> Rust.Block
-- If this block already has a final expression, just try to get rid of
-- return statements within that expression.
tailBlock (Rust.Block b (Just (tailExpr -> Just e))) = Rust.Block b e
-- If there's no final expression but the final statement consists of an
-- expression that makes sense in the tail position, move it.
tailBlock (Rust.Block (unsnoc -> Just (b, Rust.Stmt (tailExpr -> Just e))) Nothing) = Rust.Block b e
-- Otherwise, leave this block unchanged.
tailBlock b = b

itemIdioms :: Rust.Item -> Rust.Item
itemIdioms (Rust.Item attrs vis (Rust.Function fattrs name formals ret b)) = Rust.Item attrs vis (Rust.Function fattrs name formals ret (tailBlock b))
itemIdioms i = i
