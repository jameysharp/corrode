import qualified Data.ByteString.Char8 as BS
import Language.C
import Language.C.System.GCC
import Language.C.System.Preprocess
import Language.Rust.Corrode.C
import Language.Rust.Idiomatic
import System.Environment
import System.Exit
import System.FilePath
import Text.PrettyPrint.HughesPJClass

main :: IO ()
main = do
    options <- getArgs
    let cc = newGCC "gcc"
    args <- case parseCPPArgs cc options of
        Left err -> die err
        Right (args, _other) -> return args { outputFile = Nothing }

    input <- if isPreprocessed (inputFile args)
        then readInputStream (inputFile args)
        else do
            result <- runPreprocessor cc args
            case result of
                Left status -> die ("Preprocessor failed with status " ++ show status)
                Right input -> return input

    case parseC input (initPos (inputFile args)) of
        Left err -> die (show err)
        Right t -> do
            let items = BS.unlines
                    [ BS.pack (prettyShow (itemIdioms item))
                    | item <- interpretTranslationUnit t
                    ]
            BS.writeFile (replaceExtension (inputFile args) ".rs") $! items
