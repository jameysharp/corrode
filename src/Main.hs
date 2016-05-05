import Control.Monad
import Language.C
import Language.C.Data.Ident
import Language.C.System.GCC
import System.Environment

data Signed = Signed | Unsigned

data RustType
    = VoidType
    | BoolType
    | IntType Signed (Maybe Int)
    | FloatType Int

instance Show RustType where
    show VoidType = "()"
    show BoolType = "bool"
    show (IntType s width) = (case s of Signed -> 'i'; Unsigned -> 'u') : maybe "size" show width
    show (FloatType width) = 'f' : show width

rustTypeOf :: Show a => [CDeclarationSpecifier a] -> RustType
rustTypeOf = foldr go (IntType Signed (Just 32))
    where
    go (CTypeSpec (CSignedType _)) (IntType _ width) = IntType Signed width
    go (CTypeSpec (CUnsigType _)) (IntType _ width) = IntType Unsigned width
    go (CTypeSpec (CCharType _)) (IntType s _) = IntType s (Just 8)
    go (CTypeSpec (CShortType _)) (IntType s _) = IntType s (Just 16)
    go (CTypeSpec (CIntType _)) (IntType s _) = IntType s (Just 32)
    go (CTypeSpec (CLongType _)) (IntType s _) = IntType s Nothing
    go (CTypeSpec (CFloatType _)) _ = FloatType 32
    go (CTypeSpec (CDoubleType _)) _ = FloatType 64
    go (CTypeSpec (CVoidType _)) _ = VoidType
    go (CTypeSpec (CBoolType _)) _ = BoolType
    go spec _ = error ("rustTypeOf: unsupported declaration specifier " ++ show spec)

rustBinOpOf :: CBinaryOp -> String
rustBinOpOf CMulOp = "*"
rustBinOpOf CDivOp = "/"
rustBinOpOf CRmdOp = "%"
rustBinOpOf CAddOp = "+"
rustBinOpOf CSubOp = "-"
rustBinOpOf CShlOp = "<<"
rustBinOpOf CShrOp = ">>"
rustBinOpOf CLeOp = "<"
rustBinOpOf CGrOp = ">"
rustBinOpOf CLeqOp = "<="
rustBinOpOf CGeqOp = ">="
rustBinOpOf CEqOp = "=="
rustBinOpOf CNeqOp = "!="
rustBinOpOf CAndOp = "&"
rustBinOpOf CXorOp = "^"
rustBinOpOf COrOp = "|"
rustBinOpOf CLndOp = "&&"
rustBinOpOf CLorOp = "||"

translateExpression :: Show a => CExpression a -> String
translateExpression (CBinary op lhs rhs _) = translateExpression lhs ++ " " ++ rustBinOpOf op ++ " " ++ translateExpression rhs
translateExpression (CConst (CIntConst (CInteger i _repr _flags) _)) = show i
translateExpression (CVar (Ident n _ _) _) = n
translateExpression expr = show expr

translateStatement :: Show a => CStatement a -> IO ()
translateStatement (CCompound [] items _) = forM_ items $ \ item -> case item of
    CBlockStmt stmt -> translateStatement stmt
    _ -> print item
translateStatement (CReturn Nothing _) = putStrLn ("    return;")
translateStatement (CReturn (Just expr) _) = putStrLn ("    return " ++ translateExpression expr ++ ";")
translateStatement stmt = print stmt

translateFunction :: Show a => CFunctionDef a -> IO ()
translateFunction (CFunDef specs (CDeclr (Just (Ident name _ _)) [CFunDeclr (Right (args, False)) _ _] _asm _attrs _) _ body _) = do
    putStrLn ("fn " ++ name ++ "(")
    forM_ args $ \ (CDecl argspecs [(Just (CDeclr (Just (Ident argname _ _)) [] _ _ _), Nothing, Nothing)] _) ->
        putStrLn (argname ++ " : " ++ show (rustTypeOf argspecs))
    putStrLn (") -> " ++ show (rustTypeOf specs) ++ " {")
    translateStatement body
    putStrLn "}"

main :: IO ()
main = do
    args <- getArgs
    forM_ args $ \ arg -> do
        Right (CTranslUnit decls _node) <- parseCFile (newGCC "gcc") Nothing [] arg
        forM_ decls $ \ decl -> case decl of
            CFDefExt f -> translateFunction f
            _ -> print decl
