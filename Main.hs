{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Monad
import Data.String
import Language.C
import Language.C.Interpret
import Language.C.Interpret.Class
import Language.C.Data.Ident
import Language.C.System.GCC
import System.Environment

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

newtype Source = Source String
    deriving (Monoid, IsString)

instance Num Source where
    (+) a b = a `mappend` " + " `mappend` b
    (-) a b = a `mappend` " - " `mappend` b
    (*) a b = a `mappend` " * " `mappend` b
    negate a = "-" `mappend` a
    fromInteger i = Source (show i)

instance Fractional Source where
    (/) a b = a `mappend` " / " `mappend` b
    recip a = "1 / " `mappend` a
    fromRational r = Source (show (fromRational r :: Double))

instance Read Source where
    readsPrec p s = [ (Source (show (v :: Double)), r) | (v, r) <- readsPrec p s ]

instance OrdInterpretation Source Source where
    (.<) a b = a `mappend` " < " `mappend` b
    (.>) a b = a `mappend` " > " `mappend` b
    (.<=) a b = a `mappend` " <= " `mappend` b
    (.>=) a b = a `mappend` " >= " `mappend` b
    (.==) a b = a `mappend` " == " `mappend` b
    (./=) a b = a `mappend` " != " `mappend` b

instance IntInterpretation Source where
    (./) a b = a `mappend` " / " `mappend` b
    (.%) a b = a `mappend` " % " `mappend` b
    (.<<) a b = a `mappend` " << " `mappend` b
    (.>>) a b = a `mappend` " >> " `mappend` b
    (.&) a b = a `mappend` " & " `mappend` b
    (.|) a b = a `mappend` " | " `mappend` b
    (.^) a b = a `mappend` " ^ " `mappend` b
    (.~) a = "~" `mappend` a
    (.!) a = "!" `mappend` a
    (.&&) a b = a `mappend` " && " `mappend` b
    (.||) a b = a `mappend` " || " `mappend` b

instance Interpretation Source Source where
    intToFloat i = i `mappend` " as f64"

extractSource :: Value Source Source -> String
extractSource (IntValue (Source s) _ _) = s
extractSource (FloatValue (Source s) _) = s

translateStatement :: Show a => CStatement a -> IO ()
translateStatement (CCompound [] items _) = forM_ items $ \ item -> case item of
    CBlockStmt stmt -> translateStatement stmt
    _ -> print item
translateStatement (CReturn Nothing _) = putStrLn ("    return;")
translateStatement (CReturn (Just expr) _) = putStrLn ("    return " ++ extractSource (interpretExpr expr) ++ ";")
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
