module Language.Rust.Corrode.CrateMap where

import Data.Foldable
import Data.List
import qualified Data.Map as Map
import Data.Maybe

data ItemKind
    = Enum
    | Struct
    | Union
    | Type
    | Symbol
    deriving (Eq, Ord, Show)

type ModuleMap = [((ItemKind, String), String)]
type CrateMap = Map.Map String ModuleMap
type CratesMap = Map.Map String CrateMap
type ItemRewrites = Map.Map (ItemKind, String) [String]

parseCrateMap :: String -> Either String CrateMap
parseCrateMap = fmap root . foldrM parseLine (Map.empty, []) . filter (not . null) . map cleanLine . lines
    where
    root (crate, []) = crate
    root (crate, unassigned) = Map.insert "" unassigned crate

    cleanLine = words . takeWhile (/= '#')

    parseLine ("-" : item) (crate, items) = do
        item' <- parseItem item
        return (crate, item' : items)
    parseLine [name] (crate, items) | ":" `isSuffixOf` name = return (Map.insert (init name) items crate, [])
    parseLine contents _ = Left (unwords ("invalid crate map entry:" : contents))

    parseItem contents = case parseItemKind contents of
        (kind, [name]) -> return ((kind, name), name)
        (kind, [old, "as", new]) -> return ((kind, old), new)
        _ -> Left (unwords ("unsupported crate map item:" : contents))

    parseItemKind ("enum" : rest) = (Enum, rest)
    parseItemKind ("struct" : rest) = (Struct, rest)
    parseItemKind ("union" : rest) = (Union, rest)
    parseItemKind ("typedef" : rest) = (Type, rest)
    parseItemKind rest = (Symbol, rest)

mergeCrateMaps :: [(String, CrateMap)] -> Map.Map String CrateMap
mergeCrateMaps = Map.fromListWith (Map.unionWith (++))

splitModuleMap :: String -> CratesMap -> (ModuleMap, CratesMap)
splitModuleMap modName crates = fromMaybe ([], crates) $ do
    thisCrate <- Map.lookup "" crates
    thisModule <- Map.lookup modName thisCrate
    let thisCrate' = Map.delete modName thisCrate
    let crates' = Map.insert "" thisCrate' crates
    return (thisModule, crates')

rewritesFromCratesMap :: CratesMap -> ItemRewrites
rewritesFromCratesMap crates = Map.fromList
    [ (item, setCrate [modName, new])
    | (crateName, mods) <- Map.toList crates
    , let setCrate = case crateName of
            "" -> id
            _ -> (crateName :)
    , (modName, items) <- Map.toList mods
    , (item, new) <- items
    ]
