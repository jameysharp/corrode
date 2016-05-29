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

interpretExpr :: Show n => Bool -> CExpression n -> EnvMonad Result
interpretExpr demand (CComma exprs _) = do
    let (effects, mfinal) = if demand then (init exprs, Just (last exprs)) else (exprs, Nothing)
    effects' <- mapM (fmap (Rust.Stmt . snd) . interpretExpr False) effects
    mfinal' <- mapM (interpretExpr True) mfinal
    return (maybe IsVoid fst mfinal', Rust.BlockExpr (Rust.Block effects' (fmap snd mfinal')))
interpretExpr demand (CAssign op lhs rhs _) = do
    lhs' <- interpretExpr True lhs
    rhs' <- interpretExpr True rhs
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
        tmp = Rust.VarName "_tmp"
        dereftmp = Rust.Deref (Rust.Var tmp)
    return $ if demand
        then (fst lhs', Rust.BlockExpr (Rust.Block
            [ Rust.Let Rust.Immutable tmp Nothing (Just (Rust.MutBorrow (snd lhs')))
            , Rust.Stmt (Rust.Assign dereftmp op' (snd rhs'))
            ] (Just dereftmp)))
        else (IsVoid, Rust.Assign (snd lhs') op' (snd rhs'))
interpretExpr demand (CCond c (Just t) f _) = do
    c' <- interpretExpr True c
    t' <- interpretExpr demand t
    f' <- interpretExpr demand f
    return (promote (\ t'' f'' -> Rust.IfThenElse (snd (toBool c')) (Rust.Block [] (Just t'')) (Rust.Block [] (Just f''))) t' f')
interpretExpr _ (CBinary op lhs rhs _) = do
    lhs' <- interpretExpr True lhs
    rhs' <- interpretExpr True rhs
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
interpretExpr _ (CCast (CDecl spec [] _) expr _) = do
    let ty = cTypeOf spec
    (_, expr') <- interpretExpr True expr
    return (ty, Rust.Cast expr' (toRustType ty))
interpretExpr demand (CUnary op expr n) = case op of
    CPreIncOp -> interpretExpr demand (CAssign CAddAssOp expr (CConst (CIntConst (CInteger 1 DecRepr noFlags) n)) n)
    CPreDecOp -> interpretExpr demand (CAssign CSubAssOp expr (CConst (CIntConst (CInteger 1 DecRepr noFlags) n)) n)
    CPlusOp -> interpretExpr demand expr
    CMinOp -> simple (fmap Rust.Neg)
    CCompOp -> simple (fmap Rust.Not)
    CNegOp -> simple (fromBool . fmap Rust.Not . toBool)
    _ -> error ("interpretExpr: unsupported unary operator " ++ show op)
    where
    simple f = fmap f (interpretExpr True expr)
interpretExpr _ (CVar ident _) = do
    env <- get
    -- Take the definition from the first scope where it's found.
    case msum (map (lookup ident) env) of
        Just ty -> return (ty, Rust.Var (Rust.VarName (identToString ident)))
        Nothing -> error ("interpretExpr: reference to undefined variable " ++ identToString ident)
interpretExpr _ (CConst c) = return $ case c of
    CIntConst (CInteger v _repr _flags) _ -> (IsInt Signed (BitWidth 32), fromInteger v)
    CFloatConst (CFloat str) _ -> case span (`notElem` "fF") str of
        (v, "") -> (IsFloat 64, Rust.Lit (Rust.LitRep v))
        (v, [_]) -> (IsFloat 32, Rust.Lit (Rust.LitRep (v ++ "f32")))
        _ -> error ("interpretExpr: failed to parse float " ++ show str)
    _ -> error "interpretExpr: non-integer literals not implemented yet"
interpretExpr _ _ = error "interpretExpr: unsupported expression"

toBlock :: Rust.Expr -> Rust.Block
toBlock (Rust.BlockExpr b) = b
toBlock e = Rust.Block [] (Just e)

interpretStatement :: Show a => CStatement a -> EnvMonad Rust.Expr
interpretStatement (CExpr (Just expr) _) = fmap snd (interpretExpr False expr)
interpretStatement (CCompound [] items _) = do
    -- Push a new declaration scope for this block.
    modify ([] :)
    stmts <- forM items $ \ item -> case item of
        CBlockStmt stmt -> fmap (return . Rust.Stmt) (interpretStatement stmt)
        CBlockDecl (CDecl spec decls _) -> do
            let ty = cTypeOf spec
            forM decls $ \ (Just (CDeclr (Just ident) [] Nothing [] _), minit, Nothing) -> do
                mexpr <- mapM (fmap snd . interpretExpr True . (\ (CInitExpr initial _) -> initial)) minit
                modify (\ (scope : env) -> ((ident, ty) : scope) : env)
                return (Rust.Let Rust.Mutable (Rust.VarName (identToString ident)) (Just (toRustType ty)) mexpr)
        _ -> error ("interpretStatement: unsupported statement " ++ show item)
    -- Pop this block's declaration scope.
    modify tail
    return (Rust.BlockExpr (Rust.Block (concat stmts) Nothing))
interpretStatement (CIf c t mf _) = do
    (_, c') <- fmap toBool (interpretExpr True c)
    t' <- fmap toBlock (interpretStatement t)
    f' <- maybe (return (Rust.Block [] Nothing)) (fmap toBlock . interpretStatement) mf
    return (Rust.IfThenElse c' t' f')
interpretStatement (CWhile c b False _) = do
    (_, c') <- fmap toBool (interpretExpr True c)
    b' <- fmap toBlock (interpretStatement b)
    return (Rust.While c' b')
interpretStatement (CReturn expr _) = do
    expr' <- mapM (fmap snd . interpretExpr True) expr
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
