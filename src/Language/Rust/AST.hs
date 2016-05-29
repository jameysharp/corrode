module Language.Rust.AST where

import Text.PrettyPrint.HughesPJClass

newtype Type = TypeName String
newtype Lit = LitRep String
newtype Var = VarName String
newtype Stmt = Stmt Expr

instance Pretty Type where
    pPrint (TypeName s) = text s

instance Pretty Lit where
    pPrint (LitRep s) = text s

instance Pretty Var where
    pPrint (VarName s) = text s

instance Pretty Stmt where
    pPrint (Stmt e) = pPrint e <> text ";"

data Expr
    = Lit Lit
    | Var Var
    | Block [Stmt] (Maybe Expr)
    | IfThenElse Expr Expr Expr
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
    | Assign Expr Expr
    | Range Expr Expr

instance Pretty Expr where
    pPrintPrec l d e' = case e' of
        Lit x -> pPrint x
        Var x -> pPrint x
        Block ss e -> sep (text "{" : map (nest 4 . pPrint) ss ++ [maybe empty (nest 4 . pPrint) e, text "}"])
        IfThenElse c t f -> sep
            [ text "if" <+> pPrint c <+> text "{"
            , nest 4 (pPrint t)
            , text "} else {"
            , nest 4 (pPrint f)
            , text "}"
            ]
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
        Assign a b -> binary  1 a "=" b
        Range  a b -> binary  1 a ".." b
        where
        unary n op e = maybeParens (d > n) (text op <> pPrintPrec l n e)
        -- If a same-precedence operator appears nested on the right,
        -- then it needs parens, so increase the precedence there.
        binary n a op b = maybeParens (d > n) (pPrintPrec l n a <+> text op <+> pPrintPrec l (n + 1) b)

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
