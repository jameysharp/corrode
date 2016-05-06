module Language.C.Interpret where

import Control.Monad
import Control.Monad.Trans.State.Lazy
import Language.C
import Language.C.Interpret.Class

data Signed = Signed | Unsigned
    deriving Eq

data Value int float
    = IntValue int Signed (Maybe Int)
    | FloatValue float Int

type Environment int float = [[(Ident, Value int float)]]
type EnvMonad int float = State (Environment int float)

toFloat :: Interpretation int float => Value int float -> Value int float
toFloat (IntValue v _s _w) = FloatValue (intToFloat v) 64
toFloat (FloatValue v w) = FloatValue v w

promote :: Interpretation int float
    => (Signed -> Maybe Int -> int -> int -> r)
    -> (Int -> float -> float -> r)
    -> Value int float
    -> Value int float
    -> r
-- TODO: fix sign and width of the representation of the integers
promote i _ (IntValue av as aw) (IntValue bv bs bw) = i s w av bv
    where
    s = if (as, bs) == (Unsigned, Unsigned) then Unsigned else Signed
    w = max 32 <$> (max <$> aw <*> bw)
promote _ f (FloatValue av aw) b = let FloatValue bv bw = toFloat b in f (max aw bw) av bv
promote _ f a (FloatValue bv bw) = let FloatValue av aw = toFloat a in f (max aw bw) av bv

promoteArithmetic :: Interpretation int float
    => (int -> int -> int)
    -> (float -> float -> float)
    -> Value int float
    -> Value int float
    -> Value int float
promoteArithmetic i f = promote (\ s w a b -> IntValue (i a b) s w) (\ w a b -> FloatValue (f a b) w)

promoteBoolean :: Interpretation int float
    => (int -> int -> int)
    -> (float -> float -> int)
    -> Value int float
    -> Value int float
    -> Value int float
promoteBoolean i f a b = IntValue (promote (\ _ _ -> i) (\ _ -> f) a b) Signed (Just 32)

interpretExpr :: Interpretation int float => CExpression n -> EnvMonad int float (Value int float)
interpretExpr (CBinary op lhs rhs _) = do
    lhs' <- interpretExpr lhs
    rhs' <- interpretExpr rhs
    let noFloat = error ("interpretExpr: no floating-point definition for operator " ++ show op)
    return $ case op of
        CMulOp -> promoteArithmetic (*) (*) lhs' rhs'
        CDivOp -> promoteArithmetic (./) (/) lhs' rhs'
        CRmdOp -> promoteArithmetic (.%) noFloat lhs' rhs'
        CAddOp -> promoteArithmetic (+) (+) lhs' rhs'
        CSubOp -> promoteArithmetic (-) (-) lhs' rhs'
        CShlOp -> promoteArithmetic (.<<) noFloat lhs' rhs'
        CShrOp -> promoteArithmetic (.>>) noFloat lhs' rhs'
        CLeOp -> promoteBoolean (.<) (.<) lhs' rhs'
        CGrOp -> promoteBoolean (.>) (.>) lhs' rhs'
        CLeqOp -> promoteBoolean (.<=) (.<=) lhs' rhs'
        CGeqOp -> promoteBoolean (.>=) (.>=) lhs' rhs'
        CEqOp -> promoteBoolean (.==) (.==) lhs' rhs'
        CNeqOp -> promoteBoolean (./=) (./=) lhs' rhs'
        CAndOp -> promoteArithmetic (.&) noFloat lhs' rhs'
        CXorOp -> promoteArithmetic (.^) noFloat lhs' rhs'
        COrOp -> promoteArithmetic (.|) noFloat lhs' rhs'
        -- TODO: short-circuit when rhs is unnecessary
        CLndOp -> promoteBoolean (.&&) noFloat lhs' rhs'
        CLorOp -> promoteBoolean (.||) noFloat lhs' rhs'
interpretExpr (CUnary op expr _) = do
    expr' <- interpretExpr expr
    let noFloat = error ("interpretExpr: no floating-point definition for operator " ++ show op)
    return $ case op of
        CPlusOp -> expr'
        CMinOp -> case expr' of
            IntValue v s w -> IntValue (negate v) s w
            FloatValue v w -> FloatValue (negate v) w
        CCompOp -> case expr' of
            IntValue v s w -> IntValue ((.~) v) s w
            FloatValue _ _ -> noFloat
        CNegOp -> case expr' of
            IntValue v _ _ -> IntValue ((.!) v) Signed (Just 32)
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
    CFloatConst (CFloat str) _ -> case reads str of
        -- TODO: handle hex float literals
        [(v, "")] -> FloatValue v 64
        [(v, [s])] | s `elem` "fF" -> FloatValue v 32
        _ -> error ("interpretExpr: failed to parse float " ++ show str)
    _ -> error "interpretExpr: non-integer literals not implemented yet"
interpretExpr _ = error "interpretExpr: unsupported expression"
