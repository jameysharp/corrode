import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Language.C
import Language.C.System.GCC
import Language.C.System.Preprocess
import Language.Rust.Corrode.CFG
import Language.Rust.Corrode.CFG.C
import System.Environment
import System.Exit
import Text.PrettyPrint

try :: Either e a -> ExceptT e IO a
try = tryIO . return

tryIO :: IO (Either e a) -> ExceptT e IO a
tryIO = ExceptT

main :: IO ()
main = dieOnError $ do
    let cc = newGCC "gcc"
    options <- lift getArgs
    (args, _other) <- try (parseCPPArgs cc options)

    input <- if isPreprocessed (inputFile args)
        then lift (readInputStream (inputFile args))
        else withExceptT
            (\ status -> "Preprocessor failed with status " ++ show status)
            (tryIO (runPreprocessor cc args))

    CTranslUnit decls _ <- withExceptT show (try (parseC input (initPos (inputFile args))))

    lift $ forM_ decls $ \ decl -> case decl of
        CFDefExt f@(CFunDef _ declr _ _ _) -> do
            putStrLn (render (pretty declr) ++ ":")
            putStrLn (render (prettyCFG (vcat . map pretty) pretty (functionCFG f)))
        _ -> return ()

dieOnError :: ExceptT String IO a -> IO a
dieOnError m = do
    result <- runExceptT m
    case result of
        Left err -> die err
        Right a -> return a
