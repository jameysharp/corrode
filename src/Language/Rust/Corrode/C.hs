module Language.Rust.Corrode.C where

import Control.Monad
import Control.Monad.Trans.State.Lazy
import Data.Maybe
import Language.C
import Language.C.Data.Ident
import qualified Language.Rust.AST as Rust

data Signed = Signed | Unsigned
    deriving (Eq, Ord)

data IntWidth = BitWidth Int | WordWidth
    deriving (Eq, Ord)

data CType
    = IsBool
    | IsInt Signed IntWidth
    | IsFloat Int
    | IsVoid
    | IsFunc CType
    deriving (Eq, Ord)

cTypeOf :: Show a => [CTypeSpecifier a] -> CType
cTypeOf = foldr go (IsInt Signed (BitWidth 32))
    where
    go (CSignedType _) (IsInt _ width) = IsInt Signed width
    go (CUnsigType _) (IsInt _ width) = IsInt Unsigned width
    go (CCharType _) (IsInt s _) = IsInt s (BitWidth 8)
    go (CShortType _) (IsInt s _) = IsInt s (BitWidth 16)
    go (CIntType _) (IsInt s _) = IsInt s (BitWidth 32)
    go (CLongType _) (IsInt s _) = IsInt s WordWidth
    go (CFloatType _) _ = IsFloat 32
    go (CDoubleType _) _ = IsFloat 64
    go (CVoidType _) _ = IsVoid
    go (CBoolType _) _ = IsBool
    go spec _ = error ("cTypeOf: unsupported type specifier " ++ show spec)

toRustType :: CType -> Rust.Type
toRustType IsBool = Rust.TypeName "bool"
toRustType (IsInt s w) = Rust.TypeName ((case s of Signed -> 'i'; Unsigned -> 'u') : (case w of BitWidth b -> show b; WordWidth -> "size"))
toRustType (IsFloat w) = Rust.TypeName ('f' : show w)
toRustType IsVoid = Rust.TypeName "()"
toRustType (IsFunc _) = error "toRustType: not implemented for IsFunc"

-- * The "integer promotions" (C99 section 6.3.1.1 paragraph 2)
intPromote :: CType -> CType
-- "If an int can represent all values of the original type, the value is
-- converted to an int,"
intPromote IsBool = IsInt Signed (BitWidth 32)
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

castTo :: CType -> Result -> Rust.Expr
castTo target (source, v) | source == target = v
castTo target (_, v) = Rust.Cast v (toRustType target)

promote :: (Rust.Expr -> Rust.Expr -> Rust.Expr) -> Result -> Result -> Result
promote op (at, av) (bt, bv) = (rt, rv)
    where
    rt = usual at bt
    rv = op (castTo rt (at, av)) (castTo rt (bt, bv))

toBool :: Result -> Result
toBool (t, v) = (IsBool, case t of IsBool -> v; _ -> Rust.CmpNE v 0)

type Environment = [(Ident, CType)]
type EnvMonad = State Environment

addVar :: Ident -> CType -> EnvMonad ()
addVar ident ty = modify ((ident, ty) :)

scope :: EnvMonad a -> EnvMonad a
scope m = do
    -- Save the current environment.
    old <- get
    a <- m
    -- Restore the environment to its state before running m.
    put old
    return a

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
            CAssignOp -> Nothing
            CMulAssOp -> Just Rust.Mul
            CDivAssOp -> Just Rust.Div
            CRmdAssOp -> Just Rust.Mod
            CAddAssOp -> Just Rust.Add
            CSubAssOp -> Just Rust.Sub
            CShlAssOp -> Just Rust.ShiftL
            CShrAssOp -> Just Rust.ShiftR
            CAndAssOp -> Just Rust.And
            CXorAssOp -> Just Rust.Xor
            COrAssOp  -> Just Rust.Or
        tmp = Rust.VarName "_tmp"
        dereftmp = Rust.Deref (Rust.Var tmp)
    return $ case op' of
        Nothing | not demand -> (IsVoid, Rust.Assign (snd lhs') (Rust.:=) (castTo (fst lhs') rhs'))
        _ -> (fst lhs', Rust.BlockExpr (Rust.Block
            [ Rust.Let Rust.Immutable tmp Nothing (Just (Rust.MutBorrow (snd lhs')))
            , Rust.Stmt (Rust.Assign dereftmp (Rust.:=) (castTo (fst lhs') (case op' of Just o -> promote o (fst lhs', dereftmp) rhs'; Nothing -> rhs')))
            ] (if demand then Just dereftmp else Nothing)))
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
        CLeOp -> boolResult $ promote Rust.CmpLT lhs' rhs'
        CGrOp -> boolResult $ promote Rust.CmpGT lhs' rhs'
        CLeqOp -> boolResult $ promote Rust.CmpLE lhs' rhs'
        CGeqOp -> boolResult $ promote Rust.CmpGE lhs' rhs'
        CEqOp -> boolResult $ promote Rust.CmpEQ lhs' rhs'
        CNeqOp -> boolResult $ promote Rust.CmpNE lhs' rhs'
        CAndOp -> promote Rust.And lhs' rhs'
        CXorOp -> promote Rust.Xor lhs' rhs'
        COrOp -> promote Rust.Or lhs' rhs'
        CLndOp -> (IsBool, Rust.LAnd (snd (toBool lhs')) (snd (toBool rhs')))
        CLorOp -> (IsBool, Rust.LOr (snd (toBool lhs')) (snd (toBool rhs')))
    where
    boolResult (_, v) = (IsBool, v)
interpretExpr _ (CCast (CDecl spec [] _) expr _) = do
    let ([], [], [], typespecs, False) = partitionDeclSpecs spec
    let ty = cTypeOf typespecs
    (_, expr') <- interpretExpr True expr
    return (ty, Rust.Cast expr' (toRustType ty))
interpretExpr demand (CUnary op expr n) = case op of
    CPreIncOp -> interpretExpr demand (CAssign CAddAssOp expr (CConst (CIntConst (CInteger 1 DecRepr noFlags) n)) n)
    CPreDecOp -> interpretExpr demand (CAssign CSubAssOp expr (CConst (CIntConst (CInteger 1 DecRepr noFlags) n)) n)
    CPlusOp -> interpretExpr demand expr
    CMinOp -> simple (fmap Rust.Neg)
    CCompOp -> simple (fmap Rust.Not)
    CNegOp -> simple (fmap Rust.Not . toBool)
    _ -> error ("interpretExpr: unsupported unary operator " ++ show op)
    where
    simple f = fmap f (interpretExpr True expr)
interpretExpr _ (CCall func args _) = do
    (IsFunc retTy, func') <- interpretExpr True func
    args' <- mapM (fmap snd . interpretExpr True) args
    return (retTy, Rust.Call func' args')
interpretExpr _ (CVar ident _) = do
    env <- get
    case lookup ident env of
        Just ty -> return (ty, Rust.Var (Rust.VarName (identToString ident)))
        Nothing -> error ("interpretExpr: reference to undefined variable " ++ identToString ident)
interpretExpr _ (CConst c) = return $ case c of
    CIntConst (CInteger v _repr _flags) _ -> (IsInt Signed (BitWidth 32), fromInteger v)
    CFloatConst (CFloat str) _ -> case span (`notElem` "fF") str of
        (v, "") -> (IsFloat 64, Rust.Lit (Rust.LitRep v))
        (v, [_]) -> (IsFloat 32, Rust.Lit (Rust.LitRep (v ++ "f32")))
        _ -> error ("interpretExpr: failed to parse float " ++ show str)
    _ -> error "interpretExpr: non-integer literals not implemented yet"
interpretExpr _ e = error ("interpretExpr: unsupported expression " ++ show e)

localDecls :: Show a => CDeclaration a -> EnvMonad [Rust.Stmt]
localDecls (CDecl spec decls _) = do
    let ([], [], [], typespecs, False) = partitionDeclSpecs spec
    let ty = cTypeOf typespecs
    forM decls $ \ (Just (CDeclr (Just ident) [] Nothing [] _), minit, Nothing) -> do
        mexpr <- mapM (fmap snd . interpretExpr True . (\ (CInitExpr initial _) -> initial)) minit
        addVar ident ty
        return (Rust.Let Rust.Mutable (Rust.VarName (identToString ident)) (Just (toRustType ty)) mexpr)

toBlock :: Rust.Expr -> [Rust.Stmt]
toBlock (Rust.BlockExpr (Rust.Block stmts Nothing)) = stmts
toBlock e = [Rust.Stmt e]

interpretStatement :: Show a => CType -> Rust.Expr -> Rust.Expr -> CStatement a -> EnvMonad Rust.Expr
interpretStatement _ _ _ (CExpr (Just expr) _) = fmap snd (interpretExpr False expr)
interpretStatement retTy onBreak onContinue (CCompound [] items _) = scope $ do
    stmts <- forM items $ \ item -> case item of
        CBlockStmt stmt -> fmap (return . Rust.Stmt) (interpretStatement retTy onBreak onContinue stmt)
        CBlockDecl decl -> localDecls decl
        _ -> error ("interpretStatement: unsupported statement " ++ show item)
    return (Rust.BlockExpr (Rust.Block (concat stmts) Nothing))
interpretStatement retTy onBreak onContinue (CIf c t mf _) = do
    (_, c') <- fmap toBool (interpretExpr True c)
    t' <- fmap toBlock (interpretStatement retTy onBreak onContinue t)
    f' <- maybe (return []) (fmap toBlock . interpretStatement retTy onBreak onContinue) mf
    return (Rust.IfThenElse c' (Rust.Block t' Nothing) (Rust.Block f' Nothing))
interpretStatement retTy _ _ (CWhile c b False _) = do
    (_, c') <- fmap toBool (interpretExpr True c)
    b' <- fmap toBlock (interpretStatement retTy (Rust.Break Nothing) (Rust.Continue Nothing) b)
    return (Rust.While Nothing c' (Rust.Block b' Nothing))
interpretStatement retTy _ _ (CFor initial cond mincr b _) = scope $ do
    pre <- either (maybe (return []) (fmap (toBlock . snd) . interpretExpr False)) localDecls initial

    (lt, b') <- case mincr of
        Nothing -> do
            b' <- interpretStatement retTy (Rust.Break Nothing) (Rust.Continue Nothing) b
            return (Nothing, b')
        Just incr -> do
            -- Rust doesn't have a loop form that updates variables
            -- when an iteration ends and the loop condition is about to
            -- run. In the presence of 'continue' statements, this is a
            -- peculiar kind of non-local control flow. To avoid
            -- duplicating code, we wrap the loop body in
            --   'continue: loop { ...; break; }
            -- which, although it's syntactically an infinite loop, will
            -- only run once; and transform any continue statements into
            --   break 'continue;
            -- We then give the outer loop a 'break: label and transform
            -- break statements into
            --   break 'break;
            -- so that they refer to the outer loop, not the one we
            -- inserted.

            -- FIXME: allocate function-unique lifetimes
            let continueTo = Just (Rust.Lifetime "continueTo")
            let breakTo = Just (Rust.Lifetime "breakTo")

            b' <- interpretStatement retTy (Rust.Break breakTo) (Rust.Break continueTo) b
            (_, incr') <- interpretExpr False incr
            let inner = Rust.Loop continueTo (Rust.Block (toBlock b' ++ [Rust.Stmt (Rust.Break Nothing)]) Nothing)
            return (breakTo, Rust.BlockExpr (Rust.Block [Rust.Stmt inner, Rust.Stmt incr'] Nothing))

    mkLoop <- maybe (return (Rust.Loop lt)) (fmap (Rust.While lt . snd . toBool) . interpretExpr True) cond
    return (Rust.BlockExpr (Rust.Block pre (Just (mkLoop (Rust.Block (toBlock b') Nothing)))))
interpretStatement _ _ onContinue (CCont _) = return onContinue
interpretStatement _ onBreak _ (CBreak _) = return onBreak
interpretStatement retTy _ _ (CReturn expr _) = do
    expr' <- mapM (fmap (castTo retTy) . interpretExpr True) expr
    return (Rust.Return expr')
interpretStatement _ _ _ stmt = error ("interpretStatement: unsupported statement " ++ show stmt)

interpretFunction :: Show a => CFunctionDef a -> EnvMonad Rust.Item
interpretFunction (CFunDef specs (CDeclr (Just ident@(Ident name _ _)) [CFunDeclr (Right (args, False)) _ _] _asm _attrs _) _ body _) = do
    let (storage, [], [], typespecs, _inline) = partitionDeclSpecs specs
        vis = case storage of
            [CStatic _] -> Rust.Private
            [] -> Rust.Public
            _ -> error ("interpretFunction: unsupported storage specifiers " ++ show storage)
        retTy = cTypeOf typespecs

    -- Add this function to the globals before evaluating its body so
    -- recursive calls work.
    addVar ident (IsFunc retTy)

    -- Open a new scope for the formal parameters.
    scope $ do
        -- Treat argument lists `(void)` and `()` the same: we'll
        -- pretend that both mean the function takes no arguments.
        let args' = case args of
                [CDecl [CTypeSpec (CVoidType _)] [] _] -> []
                _ -> args

        formals <- forM args' $ \ (CDecl argspecs [(Just (CDeclr (Just argname) [] _ _ _), Nothing, Nothing)] _) -> do
            let ([], [], [], argtypespecs, False) = partitionDeclSpecs argspecs
            let ty = cTypeOf argtypespecs
            let nm = identToString argname
            addVar argname ty
            return (Rust.VarName nm, toRustType ty)

        let noLoop = error ("interpretFunction: break or continue statement outside any loop in " ++ name)
        body' <- interpretStatement retTy noLoop noLoop body
        return (Rust.Function vis name formals (toRustType retTy) (Rust.Block (toBlock body') Nothing))

interpretTranslationUnit :: Show a => CTranslationUnit a -> [Rust.Item]
interpretTranslationUnit (CTranslUnit decls _) = catMaybes $ flip evalState [] $ do
    forM decls $ \ decl -> case decl of
        CFDefExt f -> fmap Just (interpretFunction f)
        CDeclExt (CDecl specs [(Just (CDeclr (Just ident) [CFunDeclr{}] _ _ _), Nothing, Nothing)] _) -> do
            let (_, [], [], typespecs, _inline) = partitionDeclSpecs specs
            addVar ident (IsFunc (cTypeOf typespecs))
            return Nothing
        _ -> return Nothing -- FIXME: ignore everything but function declarations for now
