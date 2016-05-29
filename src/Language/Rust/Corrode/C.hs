module Language.Rust.Corrode.C where

import Control.Monad
import Control.Monad.Trans.State.Lazy
import Language.C
import Language.C.Data.Ident
import qualified Language.Rust.AST as Rust

data Signed = Signed | Unsigned
    deriving (Eq, Ord)

data IntWidth = BitWidth Int | WordWidth
    deriving (Eq, Ord)

data CType
    = IsInt Signed IntWidth
    | IsFloat Int
    | IsVoid
    deriving (Eq, Ord)

cTypeOf :: Show a => [CDeclarationSpecifier a] -> CType
cTypeOf = foldr go (IsInt Signed (BitWidth 32))
    where
    go (CTypeSpec (CSignedType _)) (IsInt _ width) = IsInt Signed width
    go (CTypeSpec (CUnsigType _)) (IsInt _ width) = IsInt Unsigned width
    go (CTypeSpec (CCharType _)) (IsInt s _) = IsInt s (BitWidth 8)
    go (CTypeSpec (CShortType _)) (IsInt s _) = IsInt s (BitWidth 16)
    go (CTypeSpec (CIntType _)) (IsInt s _) = IsInt s (BitWidth 32)
    go (CTypeSpec (CLongType _)) (IsInt s _) = IsInt s WordWidth
    go (CTypeSpec (CFloatType _)) _ = IsFloat 32
    go (CTypeSpec (CDoubleType _)) _ = IsFloat 64
    go (CTypeSpec (CVoidType _)) _ = IsVoid
    go spec _ = error ("cTypeOf: unsupported declaration specifier " ++ show spec)

toRustType :: CType -> Rust.Type
toRustType (IsInt s w) = Rust.TypeName ((case s of Signed -> 'i'; Unsigned -> 'u') : (case w of BitWidth b -> show b; WordWidth -> "size"))
toRustType (IsFloat w) = Rust.TypeName ('f' : show w)
toRustType IsVoid = Rust.TypeName "()"

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
fromBool (_, v) = (IsInt Signed (BitWidth 32), Rust.IfThenElse v (Rust.Block [] (Just 1)) (Rust.Block [] (Just 0)))

toBool :: Result -> Result
toBool (_, v) = (IsInt Signed (BitWidth 32),
    case v of
        Rust.IfThenElse v' (Rust.Block [] (Just (Rust.Lit (Rust.LitRep "1")))) (Rust.Block [] (Just (Rust.Lit (Rust.LitRep "0")))) -> v'
        _ -> Rust.CmpNE v 0
    )

type Environment = [[(Ident, CType)]]
type EnvMonad = State Environment

interpretExpr :: Show n => CExpression n -> EnvMonad Result
interpretExpr (CComma exprs _) = do
    exprs' <- mapM interpretExpr exprs
    let effects = map (Rust.Stmt . snd) (init exprs')
    let (ty, final) = last exprs'
    return (ty, Rust.BlockExpr (Rust.Block effects (Just final)))
interpretExpr (CAssign op lhs rhs _) = do
    lhs' <- interpretExpr lhs
    rhs' <- interpretExpr rhs
    let op' = case op of
            CAssignOp -> (Rust.:=)
            CMulAssOp -> (Rust.:*=)
            CDivAssOp -> (Rust.:/=)
            CRmdAssOp -> (Rust.:%=)
            CAddAssOp -> (Rust.:+=)
            CSubAssOp -> (Rust.:-=)
            CShlAssOp -> (Rust.:<<=)
            CShrAssOp -> (Rust.:>>=)
            CAndAssOp -> (Rust.:&=)
            CXorAssOp -> (Rust.:^=)
            COrAssOp  -> (Rust.:|=)
    return (fst lhs', Rust.Assign (snd lhs') op' (snd rhs'))
interpretExpr (CCond c (Just t) f _) = do
    c' <- interpretExpr c
    t' <- interpretExpr t
    f' <- interpretExpr f
    return (promote (\ t'' f'' -> Rust.IfThenElse (snd (toBool c')) (Rust.Block [] (Just t'')) (Rust.Block [] (Just f''))) t' f')
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
interpretExpr (CCast (CDecl spec [] _) expr _) = do
    let ty = cTypeOf spec
    (_, expr') <- interpretExpr expr
    return (ty, Rust.Cast expr' (toRustType ty))
interpretExpr (CUnary op expr _) = do
    expr' <- interpretExpr expr
    return $ case op of
        CPreIncOp -> preop (Rust.:+=) expr'
        CPreDecOp -> preop (Rust.:-=) expr'
        CPlusOp -> expr'
        CMinOp -> fmap Rust.Neg expr'
        CCompOp -> fmap Rust.Not expr'
        CNegOp -> fromBool $ fmap Rust.Not $ toBool expr'
        _ -> error ("interpretExpr: unsupported unary operator " ++ show op)
    where
    tmp = Rust.VarName "_tmp"
    dereftmp = Rust.Deref (Rust.Var tmp)
    preop op' (ty, lvalue) = (ty, Rust.BlockExpr (Rust.Block [Rust.Let Rust.Immutable tmp Nothing (Just (Rust.MutBorrow lvalue)), Rust.Stmt (Rust.Assign dereftmp op' 1)] (Just dereftmp)))
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

toBlock :: Rust.Expr -> Rust.Block
toBlock (Rust.BlockExpr b) = b
toBlock e = Rust.Block [] (Just e)

interpretStatement :: Show a => CStatement a -> EnvMonad Rust.Expr
interpretStatement (CExpr (Just expr) _) = fmap snd (interpretExpr expr)
interpretStatement (CCompound [] items _) = do
    -- Push a new declaration scope for this block.
    modify ([] :)
    stmts <- forM items $ \ item -> case item of
        CBlockStmt stmt -> fmap (return . Rust.Stmt) (interpretStatement stmt)
        CBlockDecl (CDecl spec decls _) -> do
            let ty = cTypeOf spec
            forM decls $ \ (Just (CDeclr (Just ident) [] Nothing [] _), minit, Nothing) -> do
                mexpr <- mapM (fmap snd . interpretExpr . (\ (CInitExpr initial _) -> initial)) minit
                modify (\ (scope : env) -> ((ident, ty) : scope) : env)
                return (Rust.Let Rust.Mutable (Rust.VarName (identToString ident)) (Just (toRustType ty)) mexpr)
        _ -> error ("interpretStatement: unsupported statement " ++ show item)
    -- Pop this block's declaration scope.
    modify tail
    return (Rust.BlockExpr (Rust.Block (concat stmts) Nothing))
interpretStatement (CIf c t mf _) = do
    (_, c') <- fmap toBool (interpretExpr c)
    t' <- fmap toBlock (interpretStatement t)
    f' <- maybe (return (Rust.Block [] Nothing)) (fmap toBlock . interpretStatement) mf
    return (Rust.IfThenElse c' t' f')
interpretStatement (CWhile c b False _) = do
    (_, c') <- fmap toBool (interpretExpr c)
    b' <- fmap toBlock (interpretStatement b)
    return (Rust.While c' b')
interpretStatement (CReturn expr _) = do
    expr' <- mapM (fmap snd . interpretExpr) expr
    return (Rust.Return expr')
interpretStatement stmt = error ("interpretStatement: unsupported statement " ++ show stmt)

interpretFunction :: Show a => CFunctionDef a -> Rust.Item
interpretFunction (CFunDef specs (CDeclr (Just (Ident name _ _)) [CFunDeclr (Right (args, False)) _ _] _asm _attrs _) _ body _) =
    let (formals, env) = unzip
            [ ((Rust.VarName nm, toRustType ty), (argname, ty))
            | (CDecl argspecs [(Just (CDeclr (Just argname) [] _ _ _), Nothing, Nothing)] _) <- args
            , let ty = cTypeOf argspecs
            , let nm = identToString argname
            ]
        body' = evalState (interpretStatement body) [env]
    in Rust.Function name formals (toRustType (cTypeOf specs)) (toBlock body')
