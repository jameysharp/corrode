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
        Right (CTranslUnit decls _node) <- parseCFile (newGCC "gcc") Nothing [] arg
        forM_ decls $ \ decl -> case decl of
            CFDefExt f -> putStrLn (prettyShow (itemIdioms (interpretFunction f)))
            _ -> print decl
