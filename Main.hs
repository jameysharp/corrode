import Control.Monad
import Language.C
import Language.C.System.GCC
import Language.Rust.Corrode.C
import Language.Rust.Idiomatic
import System.Environment
import Text.PrettyPrint.HughesPJClass

main :: IO ()
main = do
    args <- getArgs
    forM_ args $ \ arg -> do
        parsed <- parseCFile (newGCC "gcc") Nothing [] arg
        case parsed of
            Left err -> print err
            Right t -> mapM_ (putStrLn . prettyShow . itemIdioms) (interpretTranslationUnit t)
