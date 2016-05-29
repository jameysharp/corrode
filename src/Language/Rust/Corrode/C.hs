module Language.Rust.Corrode.C where

import Control.Monad
import Control.Monad.Trans.State.Lazy
import Language.C
import qualified Language.Rust.AST as Rust

data Signed = Signed | Unsigned
    deriving Eq

data Value
    = IntValue Rust.Expr Signed (Maybe Int)
    | FloatValue Rust.Expr Int

type Environment = [[(Ident, Value)]]
type EnvMonad = State Environment

toFloat :: Value -> Value
toFloat (IntValue v _s _w) = FloatValue (Rust.Cast v (Rust.TypeName "f64")) 64
toFloat (FloatValue v w) = FloatValue v w

promote
    :: (Signed -> Maybe Int -> Rust.Expr -> Rust.Expr -> r)
    -> (Int -> Rust.Expr -> Rust.Expr -> r)
    -> Value
    -> Value
    -> r
-- TODO: fix sign and width of the representation of the integers
promote i _ (IntValue av as aw) (IntValue bv bs bw) = i s w av bv
    where
    s = if (as, bs) == (Unsigned, Unsigned) then Unsigned else Signed
    w = max 32 <$> (max <$> aw <*> bw)
promote _ f (FloatValue av aw) b = let FloatValue bv bw = toFloat b in f (max aw bw) av bv
promote _ f a (FloatValue bv bw) = let FloatValue av aw = toFloat a in f (max aw bw) av bv

promoteArithmetic
    :: (Rust.Expr -> Rust.Expr -> Rust.Expr)
    -> (Rust.Expr -> Rust.Expr -> Rust.Expr)
    -> Value -> Value -> Value
promoteArithmetic i f = promote (\ s w a b -> IntValue (i a b) s w) (\ w a b -> FloatValue (f a b) w)

promoteBoolean
    :: (Rust.Expr -> Rust.Expr -> Rust.Expr)
    -> (Rust.Expr -> Rust.Expr -> Rust.Expr)
    -> Value -> Value -> Value
promoteBoolean i f a b = IntValue (promote (\ _ _ -> i) (\ _ -> f) a b) Signed (Just 32)

interpretExpr :: CExpression n -> EnvMonad Value
interpretExpr (CBinary op lhs rhs _) = do
    lhs' <- interpretExpr lhs
    rhs' <- interpretExpr rhs
    let noFloat = error ("interpretExpr: no floating-point definition for operator " ++ show op)
    return $ case op of
        CMulOp -> promoteArithmetic Rust.Mul Rust.Mul lhs' rhs'
        CDivOp -> promoteArithmetic Rust.Div Rust.Div lhs' rhs'
        CRmdOp -> promoteArithmetic Rust.Mod noFloat lhs' rhs'
        CAddOp -> promoteArithmetic Rust.Add Rust.Add lhs' rhs'
        CSubOp -> promoteArithmetic Rust.Sub Rust.Sub lhs' rhs'
        CShlOp -> promoteArithmetic Rust.ShiftL noFloat lhs' rhs'
        CShrOp -> promoteArithmetic Rust.ShiftR noFloat lhs' rhs'
        CLeOp -> promoteBoolean Rust.CmpLT Rust.CmpLT lhs' rhs'
        CGrOp -> promoteBoolean Rust.CmpGT Rust.CmpGT lhs' rhs'
        CLeqOp -> promoteBoolean Rust.CmpLE Rust.CmpLE lhs' rhs'
        CGeqOp -> promoteBoolean Rust.CmpGE Rust.CmpGE lhs' rhs'
        CEqOp -> promoteBoolean Rust.CmpEQ Rust.CmpEQ lhs' rhs'
        CNeqOp -> promoteBoolean Rust.CmpNE Rust.CmpNE lhs' rhs'
        CAndOp -> promoteArithmetic Rust.And noFloat lhs' rhs'
        CXorOp -> promoteArithmetic Rust.Xor noFloat lhs' rhs'
        COrOp -> promoteArithmetic Rust.Or noFloat lhs' rhs'
        CLndOp -> promoteBoolean Rust.LAnd noFloat lhs' rhs'
        CLorOp -> promoteBoolean Rust.LOr noFloat lhs' rhs'
interpretExpr (CUnary op expr _) = do
    expr' <- interpretExpr expr
    let noFloat = error ("interpretExpr: no floating-point definition for operator " ++ show op)
    return $ case op of
        CPlusOp -> expr'
        CMinOp -> case expr' of
            IntValue v s w -> IntValue (Rust.Neg v) s w
            FloatValue v w -> FloatValue (Rust.Neg v) w
        CCompOp -> case expr' of
            IntValue v s w -> IntValue (Rust.Not v) s w
            FloatValue _ _ -> noFloat
        CNegOp -> case expr' of
            IntValue v _ _ -> IntValue (Rust.Not v) Signed (Just 32)
            FloatValue _ _ -> noFloat
        _ -> error ("interpretExpr: unsupported unary operator " ++ show op)
interpretExpr (CVar ident _) = do
    env <- get
    -- Take the definition from the first scope where it's found.
    case msum (map (lookup ident) env) of
        Just v -> return v
        Nothing -> error ("interpretExpr: reference to undefined variable " ++ identToString ident)
interpretExpr (CConst c) = return $ case c of
    CIntConst (CInteger v _repr _flags) _ -> IntValue (fromInteger v) Signed (Just 32)
    CFloatConst (CFloat str) _ -> case span (`notElem` "fF") str of
        (v, "") -> FloatValue (Rust.Lit (Rust.LitRep v)) 64
        (v, [_]) -> FloatValue (Rust.Lit (Rust.LitRep (v ++ "f32"))) 32
        _ -> error ("interpretExpr: failed to parse float " ++ show str)
    _ -> error "interpretExpr: non-integer literals not implemented yet"
interpretExpr _ = error "interpretExpr: unsupported expression"
