module Language.Rust.AST where

import Data.Char
import Numeric
import Text.PrettyPrint.HughesPJClass

newtype Lifetime = Lifetime String
    deriving (Show, Eq)
newtype Type = TypeName String
    deriving (Show, Eq)
data LitIntRepr
    = DecRepr
    | OctalRepr
    | HexRepr
    deriving (Show, Eq)
data Lit
    = LitByteStr String
    | LitByteChar Char
    | LitBool Bool
    | LitInt Integer LitIntRepr Type
    | LitFloat String Type
    deriving (Show, Eq)
newtype Var = VarName String
    deriving (Show, Eq)
newtype Path = PathSegments [String]
    deriving Show

instance Pretty Lifetime where
    pPrint (Lifetime s) = text "'" <> text s

instance Pretty Type where
    pPrint (TypeName s) = text s

instance Pretty Lit where
    pPrint lit = case lit of
        LitByteStr s -> text $ "b\"" ++ concatMap rustByteLit s ++ "\""
        LitByteChar ch -> text $ "b'" ++ rustByteLit ch ++ "'"
        LitBool b -> text $ if b then "true" else "false"
        LitInt i repr (TypeName ty) -> text $ s ++ ty
            where
            s = case repr of
                DecRepr -> show i
                OctalRepr -> "0o" ++ showOct i ""
                HexRepr -> "0x" ++ showHex i ""
        LitFloat s (TypeName ty) -> text $ s ++ ty
        where
        -- Rust character and string literals have only a few special
        -- escape sequences, so we can't reuse any functions for
        -- escaping Haskell or C strings.
        rustByteLit '"' = "\\\""
        rustByteLit '\'' = "\\'"
        rustByteLit '\n' = "\\n"
        rustByteLit '\r' = "\\r"
        rustByteLit '\t' = "\\t"
        rustByteLit '\\' = "\\\\"
        rustByteLit '\NUL' = "\\0"
        rustByteLit ch | ch >= ' ' && ch <= '~' = [ch]
        rustByteLit ch = "\\x" ++
            let (u, l) = ord ch `divMod` 16
            in map (toUpper . intToDigit) [u, l]

instance Pretty Var where
    pPrint (VarName s) = text s

instance Pretty Path where
    pPrint (PathSegments names) = hcat (punctuate (text "::") (map text names))

data Visibility = Public | Private
    deriving (Show, Eq)

data Mutable = Immutable | Mutable
    deriving (Show, Eq)

data Stmt
    = Stmt Expr
    | Let Mutable Var (Maybe Type) (Maybe Expr)
    | StmtItem [Attribute] ItemKind
    deriving Show

instance Pretty Stmt where
    -- Any statement consisting of an expression whose syntax ends with
    -- a block does not need to be followed by a semicolon, and
    -- including one anyway is poor style.
    pPrint (Stmt (BlockExpr b)) = pPrintBlock empty b -- no parens, no semicolon
    pPrint (Stmt e@(IfThenElse{})) = pPrint e -- no semicolon
    pPrint (Stmt e@(Loop{})) = pPrint e -- no semicolon
    pPrint (Stmt e@(While{})) = pPrint e -- no semicolon
    pPrint (Stmt e@(For{})) = pPrint e -- no semicolon
    pPrint (Stmt e) = pPrint e <> text ";"
    pPrint (Let mut var mty minit) = sep
        [ hsep [text "let", if mut == Mutable then text "mut" else empty, pPrint var]
        , nest 4 $ maybe empty (\ ty -> text ":" <+> pPrint ty) mty
        , nest 4 $ maybe empty (\ initial -> text "=" <+> pPrint initial) minit
        ] <> text ";"
    pPrint (StmtItem attrs k) = vcat $
        [ text "#[" <> text attr <> text "]" | Attribute attr <- attrs ] ++ [pPrint k]

data Block = Block [Stmt] (Maybe Expr)
    deriving Show

pPrintBlock :: Doc -> Block -> Doc
pPrintBlock pre (Block [] e) = sep [pre <+> text "{", nest 4 (maybe empty pPrint e), text "}"]
pPrintBlock pre (Block ss e) = pre <+> text "{" $+$ nest 4 (vcat (map pPrint ss ++ [maybe empty pPrint e])) $+$ text "}"

data Attribute = Attribute String
    deriving Show
data Item = Item [Attribute] Visibility ItemKind
    deriving Show

instance Pretty Item where
    pPrint (Item attrs vis k) = vcat $
        [ text "#[" <> text attr <> text "]" | Attribute attr <- attrs ] ++
        [(if vis == Public then zeroWidthText "pub " else empty) <> pPrint k]

data FunctionAttribute
    = UnsafeFn
    | ExternABI (Maybe String)
    deriving Show

instance Pretty FunctionAttribute where
    pPrint UnsafeFn = text "unsafe"
    pPrint (ExternABI mabi) = text "extern" <+> maybe empty (text . show) mabi

data ItemKind
    = Function [FunctionAttribute] String [(Mutable, Var, Type)] Type Block
    | Static Mutable Var Type Expr
    | Struct String [(String, Type)]
    | Extern [ExternItem]
    | Use String
    | Enum String [Enumerator]
    | CloneImpl Type -- TODO: generalize `impl` syntax
    deriving Show

instance Pretty ItemKind where
    pPrint (Function attrs nm args ret body) = pPrintBlock (cat
        [ hsep (map pPrint attrs) <+> text "fn" <+> text nm <> text "("
        , nest 4 $ sep $ punctuate (text ",")
            [ sep [case mut of Mutable -> text "mut"; Immutable -> empty, pPrint v, text ":", pPrint t] | (mut, v, t) <- args ]
        , text ")" <+> if ret == TypeName "()" then empty else text "->" <+> pPrint ret
        ]) body
    pPrint (Static mut var ty initial) = sep
        [ hsep [text "static", if mut == Mutable then text "mut" else empty, pPrint var]
        , nest 4 $ text ":" <+> pPrint ty
        , nest 4 $ text "=" <+> pPrint initial
        ] <> text ";"
    pPrint (Struct name fields) =
        text "struct" <+> text name <+> text "{" $+$
        nest 4 (vcat [ text "pub" <+> text field <+> text ":" <+> pPrint ty <> text "," | (field, ty) <- fields ]) $+$
        text "}"
    pPrint (Extern defs) = vcat
        ( text "extern {"
        : map (nest 4 . pPrint) defs
        ++ [text "}"]
        )
    pPrint (Use path) = text "use" <+> text path <> text ";"
    pPrint (Enum name enums) =
        text "enum" <+> text name <+> text "{" $+$
        nest 4 (vcat [ pPrint enum <> text "," | enum <- enums ]) $+$
        text "}"
    pPrint (CloneImpl ty) =
        hsep [text "impl", text "Clone", text "for", pPrint ty] <+> text "{" $+$
            nest 4 (hsep
                [ text "fn"
                , text "clone" <> parens (text "&self")
                , text "->"
                , text "Self"
                , text "{"
                , nest 4 (text "*self")
                , text "}"
                ]) $+$
            text "}"

data ExternItem
    = ExternFn String [(Var, Type)] Bool Type
    | ExternStatic Mutable Var Type
    deriving Show

instance Pretty ExternItem where
    pPrint (ExternFn nm args variadic ret) = cat
        [ text "fn" <+> text nm <> text "("
        , nest 4 $ sep $ punctuate (text ",")
            ( [ sep [pPrint v, text ":", pPrint t] | (v, t) <- args ]
            ++ if variadic then [text "..."] else []
            )
        , text ")" <+> (if ret == TypeName "()" then empty else text "->" <+> pPrint ret) <> text ";"
        ]
    pPrint (ExternStatic mut var ty) = hsep
        [ text "static"
        , if mut == Mutable then text "mut" else empty
        , pPrint var
        , text ":"
        , pPrint ty
        ] <> text ";"

data Enumerator
    = EnumeratorAuto String
    | EnumeratorExpr String Expr
    deriving Show

instance Pretty Enumerator where
    pPrint (EnumeratorAuto name) = text name
    pPrint (EnumeratorExpr name expr) = text name <+> text "=" <+> pPrint expr

data Expr
    = Lit Lit
    | Var Var
    | Path Path
    | Index Expr Expr
    | ArrayExpr [Expr]
    | RepeatArray Expr Expr
    | StructExpr String [(String, Expr)] (Maybe Expr)
    | Call Expr [Expr]
    | MethodCall Expr Var [Expr]
    | Lambda [Var] Expr
    | Member Expr Var
    | BlockExpr Block
    | UnsafeExpr Block
    | IfThenElse Expr Block Block
    | Loop (Maybe Lifetime) Block
    | While (Maybe Lifetime) Expr Block
    | For (Maybe Lifetime) Var Expr Block
    | Break (Maybe Lifetime)
    | Continue (Maybe Lifetime)
    | Return (Maybe Expr)
    -- "Unary operators have the same precedence level and are stronger than any of the binary operators."
    -- precedence 12
    | Neg Expr
    | Deref Expr
    | Not Expr -- NOTE: this is both logical not and bitwise complement
    | Borrow Mutable Expr
    -- "Operators at the same precedence level are evaluated left-to-right."
    -- precedence 11
    | Cast Expr Type
    -- precedence 10
    | Mul Expr Expr
    | Div Expr Expr
    | Mod Expr Expr
    -- precedence 9
    | Add Expr Expr
    | Sub Expr Expr
    -- precedence 8
    | ShiftL Expr Expr
    | ShiftR Expr Expr
    -- precedence 7
    | And Expr Expr
    -- precedence 6
    | Xor Expr Expr
    -- precedence 5
    | Or Expr Expr
    -- precedence 4
    | CmpLT Expr Expr
    | CmpGT Expr Expr
    | CmpLE Expr Expr
    | CmpGE Expr Expr
    | CmpEQ Expr Expr
    | CmpNE Expr Expr
    -- precedence 3
    | LAnd Expr Expr
    -- precedence 2
    | LOr Expr Expr
    -- precedence 1
    | Range Expr Expr
    | Assign Expr AssignOp Expr
    deriving Show

data AssignOp
    = (:=)
    | (:+=)
    | (:-=)
    | (:*=)
    | (:/=)
    | (:%=)
    | (:&=)
    | (:|=)
    | (:^=)
    | (:<<=)
    | (:>>=)
    deriving Show

-- If a block is at the beginning of a statement, Rust parses it as if
-- it were followed by a semicolon. If we didn't intend to put an
-- implicit semicolon there, then we need to wrap the block in
-- parentheses. The top-most expression doesn't need parentheses, but
-- otherwise the first block encountered by following left children down
-- the AST does. Any sub-expression that has an operator or keyword in
-- front of it is not a left child.
--
-- If we get this wrong, Rust will either mis-parse the expression (if
-- we don't have enough parentheses) or warn about excess parentheses.
-- So it's worth going to some trouble to get this right.
data ExprPosition = TopExpr | LeftExpr | RightExpr
    deriving Show

instance Pretty Expr where
    pPrintPrec _ = go TopExpr
        where
        leftParens LeftExpr body = parens body
        leftParens _ body = body
        left TopExpr = LeftExpr
        left pos = pos

        go _ _ (Lit x) = pPrint x
        go _ _ (Var x) = pPrint x
        go _ _ (Path x) = pPrint x
        go pos _ (Index arr idx) = cat [go (left pos) 13 arr <> text "[", nest 4 (go RightExpr 0 idx), text "]"]
        go _ _ (ArrayExpr els) = sep
            [ text "["
            , sep (punctuate (text ",") (map (nest 4 . go RightExpr 0) els))
            , text "]"
            ]
        go _ _ (RepeatArray el size) = text "[" <> go RightExpr 0 el <> text ";" <+> go RightExpr 0 size <> text "]"
        go _ _ (StructExpr str fields base) = sep
            ( text str <+> text "{"
            : punctuate (text ",") ([ nest 4 (text name <> text ":" <+> go RightExpr 0 val) | (name, val) <- fields ] ++ maybe [] (\b -> [ text ".." <> go RightExpr 0 b ]) base)
            ++ [text "}"]
            )
        go pos _ (Call f args) = cat
            ( go (left pos) 14 f <> text "("
            : punctuate (text ",") (map (nest 4 . go RightExpr 0) args)
            ++ [text ")"]
            )
        go pos _ (MethodCall self f args) = cat
            ( go (left pos) 13 self <> text "." <> pPrint f <> text "("
            : punctuate (text ",") (map (nest 4 . go RightExpr 0) args)
            ++ [text ")"]
            )
        go _ _ (Lambda args body) =
            let args' = sep (punctuate (text ",") (map pPrint args))
            in text "|" <> args' <> text "|" <+> go RightExpr 0 body
        go pos d (Member obj field) = maybeParens (d > 13) (go (left pos) 13 obj <> text "." <> pPrint field)
        go pos _ (BlockExpr x) = leftParens pos (pPrintBlock empty x)
        go pos _ (UnsafeExpr x) = leftParens pos (pPrintBlock (text "unsafe") x)
        go pos _ (IfThenElse c t f) = leftParens pos ((if any hasStmt clauses then vcat else sep) (concatMap body clauses ++ [text "}"]))
            where
            clauses = (text "if" <+> go RightExpr 0 c <+> text "{", t) : ladder f
            hasStmt (_, Block [] _) = False
            hasStmt _ = True
            body (pre, Block ss e) = pre : map (nest 4) (map pPrint ss ++ [maybe empty (go LeftExpr 0) e])
            ladder (Block [] Nothing) = []
            ladder (Block [] (Just (IfThenElse c' t' f'))) = elseIf c' t' f'
            ladder (Block [Stmt (IfThenElse c' t' f')] Nothing) = elseIf c' t' f'
            ladder f' = [(text "}" <+> text "else" <+> text "{", f')]
            elseIf c' t' f' = (text "} else if" <+> go RightExpr 0 c' <+> text "{", t') : ladder f'
        go pos _ (Loop lt b) = leftParens pos (pPrintBlock (optLabel lt <+> text "loop") b)
        go pos _ (While lt c b) = leftParens pos (pPrintBlock (optLabel lt <+> text "while" <+> go RightExpr 0 c) b)
        go pos _ (For lt v i b) = leftParens pos (pPrintBlock (optLabel lt <+> text "for" <+> pPrint v <+> text "in" <+> go RightExpr 0 i) b)
        go _ _ (Break lt) = text "break" <+> maybe empty pPrint lt
        go _ _ (Continue lt) = text "continue" <+> maybe empty pPrint lt
        go _ _ (Return Nothing) = text "return"
        go _ _ (Return (Just e)) = hang (text "return") 4 (go RightExpr 0 e)
        -- operators:
        go _   d (Neg       e) = unary     d 12 "-" e
        go _   d (Deref     e) = unary     d 12 "*" e
        go _   d (Not       e) = unary     d 12 "!" e
        go _   d (Borrow m  e) = unary     d 12 (case m of Immutable -> "&"; Mutable -> "&mut ") e
        go pos d (Cast   e t) = maybeParens (d > 11) (go (left pos) 11 e <+> text "as" <+> parens (pPrint t))
        go pos d (Mul    a b) = binary pos d 10 a "*" b
        go pos d (Div    a b) = binary pos d 10 a "/" b
        go pos d (Mod    a b) = binary pos d 10 a "%" b
        go pos d (Add    a b) = binary pos d  9 a "+" b
        go pos d (Sub    a b) = binary pos d  9 a "-" b
        go pos d (ShiftL a b) = binary pos d  8 a "<<" b
        go pos d (ShiftR a b) = binary pos d  8 a ">>" b
        go pos d (And    a b) = binary pos d  7 a "&" b
        go pos d (Xor    a b) = binary pos d  6 a "^" b
        go pos d (Or     a b) = binary pos d  5 a "|" b
        go pos d (CmpLT  a b) = nonass pos d  4 a "<" b
        go pos d (CmpGT  a b) = nonass pos d  4 a ">" b
        go pos d (CmpLE  a b) = nonass pos d  4 a "<=" b
        go pos d (CmpGE  a b) = nonass pos d  4 a ">=" b
        go pos d (CmpEQ  a b) = nonass pos d  4 a "==" b
        go pos d (CmpNE  a b) = nonass pos d  4 a "!=" b
        go pos d (LAnd   a b) = binary pos d  3 a "&&" b
        go pos d (LOr    a b) = binary pos d  2 a "||" b
        go pos d (Range  a b) = binary pos d  1 a ".." b
        go pos d (Assign a op b) = binary pos d 1 a (assignOp op ++ "=") b

        optLabel = maybe empty (\ label -> pPrint label <> text ":")

        unary d n op e = maybeParens (d > n) (text op <> go RightExpr n e)

        -- If a same-precedence operator appears nested on the right,
        -- then it needs parens, so increase the precedence there.
        binary pos d n a op b = maybeParens (d > n) (go (left pos) n a <+> text op <+> go RightExpr (n + 1) b)

        -- Non-associative operators need parens if they're nested.
        nonass pos d n a op b = maybeParens (d >= n) (go (left pos) n a <+> text op <+> go RightExpr n b)

        assignOp (:=) = ""
        assignOp (:+=) = "+"
        assignOp (:-=) = "-"
        assignOp (:*=) = "*"
        assignOp (:/=) = "/"
        assignOp (:%=) = "%"
        assignOp (:&=) = "&"
        assignOp (:|=) = "|"
        assignOp (:^=) = "^"
        assignOp (:<<=) = "<<"
        assignOp (:>>=) = ">>"

-- These instances are mostly convenient for typing expressions in GHCi.

instance Num Expr where
    (+) = Add
    (-) = Sub
    (*) = Mul
    negate = Neg
    fromInteger i = Lit (LitInt i DecRepr (TypeName ""))

instance Fractional Expr where
    (/) = Div
    recip = Div (Lit (LitFloat "1.0" (TypeName "")))
    fromRational r = Lit (LitFloat (show (fromRational r :: Double)) (TypeName ""))
