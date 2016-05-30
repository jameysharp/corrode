module Language.Rust.AST where

import Text.PrettyPrint.HughesPJClass

newtype Type = TypeName String
    deriving Eq
newtype Lit = LitRep String
    deriving Eq
newtype Var = VarName String
    deriving Eq

instance Pretty Type where
    pPrint (TypeName s) = text s

instance Pretty Lit where
    pPrint (LitRep s) = text s

instance Pretty Var where
    pPrint (VarName s) = text s

data Visibility = Public | Private
    deriving Eq

data Mutable = Immutable | Mutable
    deriving Eq

data Stmt
    = Stmt Expr
    | Let Mutable Var (Maybe Type) (Maybe Expr)

instance Pretty Stmt where
    -- Any statement consisting of an expression whose syntax ends with
    -- a block does not need to be followed by a semicolon, and
    -- including one anyway is poor style.
    pPrint (Stmt (BlockExpr b)) = pPrint b -- no parens, no semicolon
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

data Block = Block [Stmt] (Maybe Expr)

instance Pretty Block where
    pPrint (Block ss e) = sep (text "{" : map (nest 4 . pPrint) ss ++ [maybe empty (nest 4 . pPrint) e, text "}"])

data Item = Function Visibility String [(Var, Type)] Type Block

instance Pretty Item where
    pPrint (Function vis nm args ret body) = cat
        [ (if vis == Public then text "pub" else empty) <+> text "fn" <+> text nm <> text "("
        , nest 4 $ sep $ punctuate (text ",")
            [ sep [text "mut", pPrint v, text ":", pPrint t] | (v, t) <- args ]
        , text ")" <+> if ret == TypeName "()" then empty else text "->" <+> pPrint ret
        , pPrint body
        ]

data Expr
    = Lit Lit
    | Var Var
    | Call Expr [Expr]
    | BlockExpr Block
    | IfThenElse Expr Block Block
    | Loop Block
    | While Expr Block
    | For Var Expr Block
    | Break
    | Continue
    | Return (Maybe Expr)
    -- "Unary operators have the same precedence level and are stronger than any of the binary operators."
    -- precedence 12
    | Neg Expr
    | Deref Expr
    | Not Expr -- NOTE: this is both logical not and bitwise complement
    | Borrow Expr
    | MutBorrow Expr
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

instance Pretty Expr where
    pPrintPrec l d e' = case e' of
        Lit x -> pPrint x
        Var x -> pPrint x
        Call f args -> cat
            ( pPrint f <> text "("
            : punctuate (text ",") (map (nest 4 . pPrint) args)
            ++ [text ")"]
            )
        -- If a block is at the beginning of a statement, Rust parses it
        -- as if it were followed by a semicolon. Parenthesizing all
        -- block expressions is excessive but correct.
        BlockExpr x -> text "(" <> pPrint x <> text ")"
        IfThenElse c t f -> text "if" <+> pPrint c <+> pPrint t <+> case f of
            Block [] Nothing -> empty
            Block [] (Just n@(IfThenElse{})) -> text "else" <+> pPrint n
            Block [Stmt n@(IfThenElse{})] Nothing -> text "else" <+> pPrint n
            _ -> text "else" <+> pPrint f
        Loop b -> text "loop" <+> pPrint b
        While c b -> text "while" <+> pPrint c <+> pPrint b
        For v i b -> text "for" <+> pPrint v <+> text "in" <+> pPrint i <+> pPrint b
        Break -> text "break"
        Continue -> text "continue"
        Return Nothing -> text "return"
        Return (Just e) -> hang (text "return") 4 (pPrint e)
        -- operators:
        Neg       e -> unary 12 "-" e
        Deref     e -> unary 12 "*" e
        Not       e -> unary 12 "!" e
        Borrow    e -> unary 12 "&" e
        MutBorrow e -> unary 12 "&mut " e
        Cast   e t -> binary 11 e "as" t
        Mul    a b -> binary 10 a "*" b
        Div    a b -> binary 10 a "/" b
        Mod    a b -> binary 10 a "%" b
        Add    a b -> binary  9 a "+" b
        Sub    a b -> binary  9 a "-" b
        ShiftL a b -> binary  8 a "<<" b
        ShiftR a b -> binary  8 a ">>" b
        And    a b -> binary  7 a "&" b
        Xor    a b -> binary  6 a "^" b
        Or     a b -> binary  5 a "|" b
        CmpLT  a b -> binary  4 a "<" b
        CmpGT  a b -> binary  4 a ">" b
        CmpLE  a b -> binary  4 a "<=" b
        CmpGE  a b -> binary  4 a ">=" b
        CmpEQ  a b -> binary  4 a "==" b
        CmpNE  a b -> binary  4 a "!=" b
        LAnd   a b -> binary  3 a "&&" b
        LOr    a b -> binary  2 a "||" b
        Range  a b -> binary  1 a ".." b
        Assign a op b -> binary 1 a (assignOp op ++ "=") b
        where
        unary n op e = maybeParens (d > n) (text op <> pPrintPrec l n e)
        -- If a same-precedence operator appears nested on the right,
        -- then it needs parens, so increase the precedence there.
        binary n a op b = maybeParens (d > n) (pPrintPrec l n a <+> text op <+> pPrintPrec l (n + 1) b)

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
    fromInteger i = Lit (LitRep (show i))

instance Fractional Expr where
    (/) = Div
    recip = Div (Lit (LitRep "1.0"))
    fromRational r = Lit (LitRep (show (fromRational r :: Double)))
