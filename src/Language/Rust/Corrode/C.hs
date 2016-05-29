module Language.Rust.Corrode.C where

import Control.Monad
import Control.Monad.Trans.State.Lazy
import Language.C
import qualified Language.Rust.AST as Rust

data Signed = Signed | Unsigned
    deriving (Eq, Ord)

data IntWidth = BitWidth Int | WordWidth
    deriving (Eq, Ord)

data CType
    = IsInt Signed IntWidth
    | IsFloat Int
    deriving (Eq, Ord)

toRustType :: CType -> Rust.Type
toRustType (IsInt s w) = Rust.TypeName ((case s of Signed -> 'i'; Unsigned -> 'u') : (case w of BitWidth b -> show b; WordWidth -> "size"))
toRustType (IsFloat w) = Rust.TypeName ('f' : show w)

-- * The "integer promotions" (C99 section 6.3.1.1 paragraph 2)
intPromote :: CType -> CType
-- "If an int can represent all values of the original type, the value is
-- converted to an int,"
intPromote (IsInt _ (BitWidth w)) | w < 32 = IsInt Signed (BitWidth 32)
-- "otherwise, it is converted to an unsigned int. ... All other types are
-- unchanged by the integer promotions."
intPromote x = x

-- * The "usual arithmetic conversions" (C99 section 6.3.1.8)
usual :: CType -> CType -> CType
usual a@(IsFloat _) b = max a b
usual a b@(IsFloat _) = max a b
usual a b
    | a' == b' = a'
    | as == bs = IsInt as (max aw bw)
    | as == Unsigned = if aw >= bw then a' else b'
    | otherwise      = if bw >= aw then b' else a'
    where
    a'@(IsInt as aw) = intPromote a
    b'@(IsInt bs bw) = intPromote b

type Result = (CType, Rust.Expr)

promote :: (Rust.Expr -> Rust.Expr -> Rust.Expr) -> Result -> Result -> Result
promote op (at, av) (bt, bv) = (rt, rv)
    where
    rt = usual at bt
    to t v | t == rt = v
    to _ v = Rust.Cast v (toRustType rt)
    rv = op (to at av) (to bt bv)

fromBool :: Result -> Result
fromBool (_, v) = (IsInt Signed (BitWidth 32), Rust.IfThenElse v 1 0)

toBool :: Result -> Result
toBool (_, v) = (IsInt Signed (BitWidth 32),
    case v of
        Rust.IfThenElse v' (Rust.Lit (Rust.LitRep "1")) (Rust.Lit (Rust.LitRep "0")) -> v'
        _ -> Rust.CmpNE v 0
    )

type Environment = [[(Ident, CType)]]
type EnvMonad = State Environment

interpretExpr :: CExpression n -> EnvMonad Result
interpretExpr (CBinary op lhs rhs _) = do
    lhs' <- interpretExpr lhs
    rhs' <- interpretExpr rhs
    return $ case op of
        CMulOp -> promote Rust.Mul lhs' rhs'
        CDivOp -> promote Rust.Div lhs' rhs'
        CRmdOp -> promote Rust.Mod lhs' rhs'
        CAddOp -> promote Rust.Add lhs' rhs'
        CSubOp -> promote Rust.Sub lhs' rhs'
        CShlOp -> promote Rust.ShiftL lhs' rhs'
        CShrOp -> promote Rust.ShiftR lhs' rhs'
        CLeOp -> fromBool $ promote Rust.CmpLT lhs' rhs'
        CGrOp -> fromBool $ promote Rust.CmpGT lhs' rhs'
        CLeqOp -> fromBool $ promote Rust.CmpLE lhs' rhs'
        CGeqOp -> fromBool $ promote Rust.CmpGE lhs' rhs'
        CEqOp -> fromBool $ promote Rust.CmpEQ lhs' rhs'
        CNeqOp -> fromBool $ promote Rust.CmpNE lhs' rhs'
        CAndOp -> promote Rust.And lhs' rhs'
        CXorOp -> promote Rust.Xor lhs' rhs'
        COrOp -> promote Rust.Or lhs' rhs'
        CLndOp -> fromBool $ promote Rust.LAnd (toBool lhs') (toBool rhs')
        CLorOp -> fromBool $ promote Rust.LOr (toBool lhs') (toBool rhs')
interpretExpr (CUnary op expr _) = do
    expr' <- interpretExpr expr
    return $ case op of
        CPlusOp -> expr'
        CMinOp -> fmap Rust.Neg expr'
        CCompOp -> fmap Rust.Not expr'
        CNegOp -> fromBool $ fmap Rust.Not $ toBool expr'
        _ -> error ("interpretExpr: unsupported unary operator " ++ show op)
interpretExpr (CVar ident _) = do
    env <- get
    -- Take the definition from the first scope where it's found.
    case msum (map (lookup ident) env) of
        Just ty -> return (ty, Rust.Var (Rust.VarName (identToString ident)))
        Nothing -> error ("interpretExpr: reference to undefined variable " ++ identToString ident)
interpretExpr (CConst c) = return $ case c of
    CIntConst (CInteger v _repr _flags) _ -> (IsInt Signed (BitWidth 32), fromInteger v)
    CFloatConst (CFloat str) _ -> case span (`notElem` "fF") str of
        (v, "") -> (IsFloat 64, Rust.Lit (Rust.LitRep v))
        (v, [_]) -> (IsFloat 32, Rust.Lit (Rust.LitRep (v ++ "f32")))
        _ -> error ("interpretExpr: failed to parse float " ++ show str)
    _ -> error "interpretExpr: non-integer literals not implemented yet"
interpretExpr _ = error "interpretExpr: unsupported expression"
