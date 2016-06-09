{-# LANGUAGE ViewPatterns #-}

module Language.Rust.Corrode.C where

import Control.Monad
import Control.Monad.Trans.State.Lazy
import Data.Foldable
import Data.Maybe
import Language.C
import qualified Language.Rust.AST as Rust

data Signed = Signed | Unsigned
    deriving (Show, Eq)

data IntWidth = BitWidth Int | WordWidth
    deriving (Show, Eq, Ord)

data CType
    = IsBool
    | IsInt Signed IntWidth
    | IsFloat Int
    | IsVoid
    | IsFunc CType [CType]
    | IsPtr Rust.Mutable CType
    deriving (Show, Eq)

cTypeOf :: Show a => [CTypeQualifier a] -> [CTypeSpecifier a] -> [CDerivedDeclarator a] -> EnvMonad (Rust.Mutable, CType)
cTypeOf basequals base derived = do
    base' <- foldrM go (mutable basequals, IsInt Signed (BitWidth 32)) base
    foldrM derive base' derived
    where
    mutable quals = if any (\ q -> case q of CConstQual _ -> True; _ -> False) quals then Rust.Immutable else Rust.Mutable

    derive (CFunDeclr args _ _) (c, retTy) = (,) c . IsFunc retTy . map snd <$> functionArgs args
    derive (CPtrDeclr quals _) (c, to) = return (mutable quals, IsPtr c to)
    derive d _ = error ("cTypeOf: derived declarator not yet implemented " ++ show d)

    go (CSignedType _) (mut, IsInt _ width) = return (mut, IsInt Signed width)
    go (CUnsigType _) (mut, IsInt _ width) = return (mut, IsInt Unsigned width)
    go (CCharType _) (mut, IsInt s _) = return (mut, IsInt s (BitWidth 8))
    go (CShortType _) (mut, IsInt s _) = return (mut, IsInt s (BitWidth 16))
    go (CIntType _) (mut, IsInt s _) = return (mut, IsInt s (BitWidth 32))
    go (CLongType _) (mut, IsInt s _) = return (mut, IsInt s WordWidth)
    go (CFloatType _) (mut, _) = return (mut, IsFloat 32)
    go (CDoubleType _) (mut, _) = return (mut, IsFloat 64)
    go (CVoidType _) (mut, _) = return (mut, IsVoid)
    go (CBoolType _) (mut, _) = return (mut, IsBool)
    go (CTypeDef ident _) (mut1, _) = do
        env <- get
        case lookup (Left ident) env of
            Just (mut2, ty) -> return (if mut1 == mut2 then mut1 else Rust.Immutable, ty)
            Nothing -> error ("cTypeOf: reference to undefined type " ++ identToString ident)
    go spec _ = error ("cTypeOf: unsupported type specifier " ++ show spec)

toRustType :: CType -> Rust.Type
toRustType IsBool = Rust.TypeName "bool"
toRustType (IsInt s w) = Rust.TypeName ((case s of Signed -> 'i'; Unsigned -> 'u') : (case w of BitWidth b -> show b; WordWidth -> "size"))
toRustType (IsFloat w) = Rust.TypeName ('f' : show w)
toRustType IsVoid = Rust.TypeName "()"
toRustType (IsFunc _ _) = error "toRustType: not implemented for IsFunc"
toRustType (IsPtr mut to) = let Rust.TypeName to' = toRustType to in Rust.TypeName (rustMut mut ++ to')
    where
    rustMut Rust.Mutable = "*mut "
    rustMut Rust.Immutable = "*const "

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
usual (IsFloat aw) (IsFloat bw) = IsFloat (max aw bw)
usual a@(IsFloat _) _ = a
usual _ b@(IsFloat _) = b
usual a@(intPromote -> IsInt as aw) b@(intPromote -> IsInt bs bw)
    | a == b = a
    | as == bs = IsInt as (max aw bw)
    | as == Unsigned = if aw >= bw then a else b
    | otherwise      = if bw >= aw then b else a
usual a b = error ("attempt to apply arithmetic conversions to " ++ show a ++ " and " ++ show b)

compatiblePtr :: CType -> CType -> CType
compatiblePtr (IsPtr _ IsVoid) b = b
compatiblePtr a (IsPtr _ IsVoid) = a
compatiblePtr (IsPtr m1 a) (IsPtr m2 b) = IsPtr (leastMutable m1 m2) (compatiblePtr a b)
    where
    leastMutable Rust.Mutable Rust.Mutable = Rust.Mutable
    leastMutable _ _ = Rust.Immutable
compatiblePtr a b | a == b = a
-- Types are not compatible, which as far as I can tell is not allowed
-- by C99. But GCC only treats it as a warning, so we cast both sides
-- to a void pointer, which should work on the usual architectures.
compatiblePtr _ _ = IsVoid

data Result = Result
    { resultType :: CType
    , isMutable :: Rust.Mutable
    , result :: Rust.Expr
    }

castTo :: CType -> Result -> Rust.Expr
castTo target source | resultType source == target = result source
castTo target source = Rust.Cast (result source) (toRustType target)

promote :: (Rust.Expr -> Rust.Expr -> Rust.Expr) -> Result -> Result -> Result
promote op a b = Result { resultType = rt, isMutable = Rust.Immutable, result = rv }
    where
    rt = usual (resultType a) (resultType b)
    rv = op (castTo rt a) (castTo rt b)

promotePtr :: (Rust.Expr -> Rust.Expr -> Rust.Expr) -> Result -> Result -> Result
promotePtr op a b = Result
    { resultType = IsBool
    , isMutable = Rust.Immutable
    , result = let ty = compatiblePtr (resultType a) (resultType b) in op (castTo ty a) (castTo ty b)
    }

toBool :: Result -> Result
toBool (Result { resultType = t, result = v }) = Result { resultType = IsBool, isMutable = Rust.Immutable, result = case t of
    IsBool -> v
    IsPtr _ _ -> Rust.Not (Rust.MethodCall v (Rust.VarName "is_null") [])
    _ -> Rust.CmpNE v 0
    }

type Environment = [(Either Ident Ident, (Rust.Mutable, CType))]
type EnvMonad = State Environment

addVar :: Ident -> (Rust.Mutable, CType) -> EnvMonad ()
addVar ident ty = modify ((Right ident, ty) :)

addType :: Ident -> (Rust.Mutable, CType) -> EnvMonad ()
addType ident ty = modify ((Left ident, ty) :)

scope :: EnvMonad a -> EnvMonad a
scope m = do
    -- Save the current environment.
    old <- get
    a <- m
    -- Restore the environment to its state before running m.
    put old
    return a

wrapping :: Result -> Result
wrapping r@(Result { resultType = IsInt Unsigned _ }) = case result r of
    Rust.Add lhs rhs -> r { result = Rust.MethodCall lhs (Rust.VarName "wrapping_add") [rhs] }
    Rust.Sub lhs rhs -> r { result = Rust.MethodCall lhs (Rust.VarName "wrapping_sub") [rhs] }
    Rust.Mul lhs rhs -> r { result = Rust.MethodCall lhs (Rust.VarName "wrapping_mul") [rhs] }
    Rust.Div lhs rhs -> r { result = Rust.MethodCall lhs (Rust.VarName "wrapping_div") [rhs] }
    Rust.Mod lhs rhs -> r { result = Rust.MethodCall lhs (Rust.VarName "wrapping_rem") [rhs] }
    Rust.Neg e -> r { result = Rust.MethodCall e (Rust.VarName "wrapping_neg") [] }
    _ -> r
wrapping r = r

isSimple :: Rust.Expr -> Bool
isSimple (Rust.Var{}) = True
isSimple (Rust.Deref p) = isSimple p
isSimple _ = False

interpretExpr :: Show n => Bool -> CExpression n -> EnvMonad Result
interpretExpr demand (CComma exprs _) = do
    let (effects, mfinal) = if demand then (init exprs, Just (last exprs)) else (exprs, Nothing)
    effects' <- mapM (fmap (Rust.Stmt . result) . interpretExpr False) effects
    mfinal' <- mapM (interpretExpr True) mfinal
    return Result
        { resultType = maybe IsVoid resultType mfinal'
        , isMutable = maybe Rust.Immutable isMutable mfinal'
        , result = Rust.BlockExpr (Rust.Block effects' (fmap result mfinal'))
        }
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
        (bindings, dereflhs, boundrhs) = if isSimple (result lhs')
            then ([], lhs', rhs')
            else
                let lhsvar = Rust.VarName "_lhs"
                    rhsvar = Rust.VarName "_rhs"
                in ([ Rust.Let Rust.Immutable rhsvar Nothing (Just (result rhs'))
                    , Rust.Let Rust.Immutable lhsvar Nothing (Just (Rust.Borrow Rust.Mutable (result lhs')))
                    ], lhs' { result = Rust.Deref (Rust.Var lhsvar) }, rhs' { result = Rust.Var rhsvar })
        assignment = Rust.Assign (result dereflhs) (Rust.:=) (castTo (resultType lhs') (case op' of Just o -> wrapping (promote o dereflhs boundrhs); Nothing -> boundrhs))
        b = if not demand && null bindings
            then assignment
            else Rust.BlockExpr (Rust.Block (bindings ++ [Rust.Stmt assignment]) (if demand then Just (result dereflhs) else Nothing))
    return $ if not demand
        then Result
            { resultType = IsVoid
            , isMutable = Rust.Immutable
            , result = b
            }
        else lhs' { result = b }
interpretExpr demand (CCond c (Just t) f _) = do
    c' <- interpretExpr True c
    t' <- interpretExpr demand t
    f' <- interpretExpr demand f
    return (promote (\ t'' f'' -> Rust.IfThenElse (result (toBool c')) (Rust.Block [] (Just t'')) (Rust.Block [] (Just f''))) t' f')
interpretExpr _ (CBinary op lhs rhs _) = do
    lhs' <- interpretExpr True lhs
    rhs' <- interpretExpr True rhs
    return $ wrapping $ case op of
        CMulOp -> promote Rust.Mul lhs' rhs'
        CDivOp -> promote Rust.Div lhs' rhs'
        CRmdOp -> promote Rust.Mod lhs' rhs'
        CAddOp -> case (resultType lhs', resultType rhs') of
            (IsPtr _ _, _) -> lhs' { result = Rust.MethodCall (result lhs') (Rust.VarName "offset") [castTo (IsInt Signed WordWidth) rhs'] }
            (_, IsPtr _ _) -> rhs' { result = Rust.MethodCall (result rhs') (Rust.VarName "offset") [castTo (IsInt Signed WordWidth) lhs'] }
            _ -> promote Rust.Add lhs' rhs'
        CSubOp -> case (resultType lhs', resultType rhs') of
            (IsPtr _ _, IsPtr _ _) -> error "not sure how to translate pointer difference to Rust"
            (IsPtr _ _, _) -> lhs' { result = Rust.MethodCall (result lhs') (Rust.VarName "offset") [Rust.Neg (castTo (IsInt Signed WordWidth) rhs')] }
            _ -> promote Rust.Sub lhs' rhs'
        CShlOp -> promote Rust.ShiftL lhs' rhs'
        CShrOp -> promote Rust.ShiftR lhs' rhs'
        CLeOp -> comparison Rust.CmpLT lhs' rhs'
        CGrOp -> comparison Rust.CmpGT lhs' rhs'
        CLeqOp -> comparison Rust.CmpLE lhs' rhs'
        CGeqOp -> comparison Rust.CmpGE lhs' rhs'
        CEqOp -> comparison Rust.CmpEQ lhs' rhs'
        CNeqOp -> comparison Rust.CmpNE lhs' rhs'
        CAndOp -> promote Rust.And lhs' rhs'
        CXorOp -> promote Rust.Xor lhs' rhs'
        COrOp -> promote Rust.Or lhs' rhs'
        CLndOp -> Result { resultType = IsBool, isMutable = Rust.Immutable, result = Rust.LAnd (result (toBool lhs')) (result (toBool rhs')) }
        CLorOp -> Result { resultType = IsBool, isMutable = Rust.Immutable, result = Rust.LOr (result (toBool lhs')) (result (toBool rhs')) }
    where
    comparison op' lhs' rhs' = case (resultType lhs', resultType rhs') of
        (IsPtr _ _, IsPtr _ _) -> promotePtr op' lhs' rhs'
        _ -> (promote op' lhs' rhs') { resultType = IsBool }
interpretExpr _ (CCast (CDecl spec declarators _) expr _) = do
    let ([], [], typequals, typespecs, False) = partitionDeclSpecs spec
    -- Declaration mutability has no effect in casts.
    (_mut, ty) <- cTypeOf typequals typespecs $ case declarators of
        [] -> []
        [(Just (CDeclr Nothing derived _ _ _), Nothing, Nothing)] -> derived
        _ -> error ("interpretExpr: invalid cast " ++ show declarators)
    expr' <- interpretExpr True expr
    return Result
        { resultType = ty
        , isMutable = Rust.Immutable
        , result = Rust.Cast (result expr') (toRustType ty)
        }
interpretExpr demand (CUnary op expr n) = case op of
    CPreIncOp -> interpretExpr demand (CAssign CAddAssOp expr (CConst (CIntConst (CInteger 1 DecRepr noFlags) n)) n)
    CPreDecOp -> interpretExpr demand (CAssign CSubAssOp expr (CConst (CIntConst (CInteger 1 DecRepr noFlags) n)) n)
    CAdrOp -> do
        expr' <- interpretExpr True expr
        let ty' = IsPtr (isMutable expr') (resultType expr')
        return Result
            { resultType = ty'
            , isMutable = Rust.Immutable
            , result = Rust.Cast (Rust.Borrow (isMutable expr') (result expr')) (toRustType ty')
            }
    CIndOp -> do
        expr' <- interpretExpr True expr
        let IsPtr mut' ty' = resultType expr'
        return Result
            { resultType = ty'
            , isMutable = mut'
            , result = Rust.Deref (result expr')
            }
    CPlusOp -> simple id
    CMinOp -> fmap wrapping $ simple Rust.Neg
    CCompOp -> simple Rust.Not
    CNegOp -> do
        expr' <- fmap toBool (interpretExpr True expr)
        return expr' { result = Rust.Not (result expr') }
    _ -> error ("interpretExpr: unsupported unary operator " ++ show op)
    where
    simple f = do
        expr' <- interpretExpr True expr
        let ty' = intPromote (resultType expr')
        return Result
            { resultType = ty'
            , isMutable = Rust.Immutable
            , result = f (castTo ty' expr')
            }
interpretExpr _ (CCall func args _) = do
    Result { resultType = IsFunc retTy argTys, result = func' } <- interpretExpr True func
    args' <- zipWithM (\ ty arg -> fmap (castTo ty) (interpretExpr True arg)) argTys args
    return Result { resultType = retTy, isMutable = Rust.Immutable, result = Rust.Call func' args' }
interpretExpr _ (CVar ident _) = do
    env <- get
    case lookup (Right ident) env of
        Just (mut, ty) -> return Result
            { resultType = ty
            , isMutable = mut
            , result = Rust.Var (Rust.VarName (identToString ident))
            }
        Nothing -> error ("interpretExpr: reference to undefined variable " ++ identToString ident)
interpretExpr _ (CConst c) = return $ case c of
    CIntConst (CInteger v _repr flags) _ ->
        let s = if testFlag FlagUnsigned flags then Unsigned else Signed
            w = if testFlag FlagLongLong flags || testFlag FlagLong flags then WordWidth else BitWidth 32
        in litResult (IsInt s w) (show v)
    CFloatConst (CFloat str) _ -> case span (`notElem` "fF") str of
        (v, "") -> litResult (IsFloat 64) v
        (v, [_]) -> litResult (IsFloat 32) v
        _ -> error ("interpretExpr: failed to parse float " ++ show str)
    _ -> error "interpretExpr: non-integer literals not implemented yet"
    where
    litResult ty v =
        let Rust.TypeName suffix = toRustType ty
        in Result { resultType = ty, isMutable = Rust.Immutable, result = Rust.Lit (Rust.LitRep (v ++ suffix)) }
interpretExpr _ e = error ("interpretExpr: unsupported expression " ++ show e)

localDecls :: Show a => CDeclaration a -> EnvMonad [Rust.Stmt]
localDecls (CDecl spec decls _) = do
    let ([], [], typequals, typespecs, False) = partitionDeclSpecs spec
    forM decls $ \ (Just (CDeclr (Just ident) derived Nothing [] _), minit, Nothing) -> do
        (mut, ty) <- cTypeOf typequals typespecs derived
        mexpr <- mapM (fmap (castTo ty) . interpretExpr True . (\ (CInitExpr initial _) -> initial)) minit
        addVar ident (mut, ty)
        return (Rust.Let mut (Rust.VarName (identToString ident)) (Just (toRustType ty)) mexpr)

toBlock :: Rust.Expr -> [Rust.Stmt]
toBlock (Rust.BlockExpr (Rust.Block stmts Nothing)) = stmts
toBlock e = [Rust.Stmt e]

interpretStatement :: Show a => CType -> Rust.Expr -> Rust.Expr -> CStatement a -> EnvMonad Rust.Expr
interpretStatement _ _ _ (CExpr (Just expr) _) = fmap result (interpretExpr False expr)
interpretStatement retTy onBreak onContinue (CCompound [] items _) = scope $ do
    stmts <- forM items $ \ item -> case item of
        CBlockStmt stmt -> fmap (return . Rust.Stmt) (interpretStatement retTy onBreak onContinue stmt)
        CBlockDecl decl -> localDecls decl
        _ -> error ("interpretStatement: unsupported statement " ++ show item)
    return (Rust.BlockExpr (Rust.Block (concat stmts) Nothing))
interpretStatement retTy onBreak onContinue (CIf c t mf _) = do
    c' <- fmap toBool (interpretExpr True c)
    t' <- fmap toBlock (interpretStatement retTy onBreak onContinue t)
    f' <- maybe (return []) (fmap toBlock . interpretStatement retTy onBreak onContinue) mf
    return (Rust.IfThenElse (result c') (Rust.Block t' Nothing) (Rust.Block f' Nothing))
interpretStatement retTy _ _ (CWhile c b False _) = do
    c' <- fmap toBool (interpretExpr True c)
    b' <- fmap toBlock (interpretStatement retTy (Rust.Break Nothing) (Rust.Continue Nothing) b)
    return (Rust.While Nothing (result c') (Rust.Block b' Nothing))
interpretStatement retTy _ _ (CFor initial cond mincr b _) = scope $ do
    pre <- either (maybe (return []) (fmap (toBlock . result) . interpretExpr False)) localDecls initial

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
            incr' <- interpretExpr False incr
            let inner = Rust.Loop continueTo (Rust.Block (toBlock b' ++ [Rust.Stmt (Rust.Break Nothing)]) Nothing)
            return (breakTo, Rust.BlockExpr (Rust.Block [Rust.Stmt inner, Rust.Stmt (result incr')] Nothing))

    mkLoop <- maybe (return (Rust.Loop lt)) (fmap (Rust.While lt . result . toBool) . interpretExpr True) cond
    return (Rust.BlockExpr (Rust.Block pre (Just (mkLoop (Rust.Block (toBlock b') Nothing)))))
interpretStatement _ _ onContinue (CCont _) = return onContinue
interpretStatement _ onBreak _ (CBreak _) = return onBreak
interpretStatement retTy _ _ (CReturn expr _) = do
    expr' <- mapM (fmap (castTo retTy) . interpretExpr True) expr
    return (Rust.Return expr')
interpretStatement _ _ _ stmt = error ("interpretStatement: unsupported statement " ++ show stmt)

functionArgs :: Show a => Either [Ident] ([CDeclaration a], Bool) -> EnvMonad [(Maybe (Rust.Mutable, Ident), CType)]
functionArgs (Left _) = error "old-style function declarations not supported"
functionArgs (Right (_, True)) = error "variadic functions not supported"
functionArgs (Right (args, False)) = sequence
    [ do
        (mut, ty) <- cTypeOf argtypequals argtypespecs derived
        return (fmap ((,) mut) argname, ty)
    | CDecl argspecs [(Just (CDeclr argname derived _ _ _), Nothing, Nothing)] _ <-
        -- Treat argument lists `(void)` and `()` the same: we'll
        -- pretend that both mean the function takes no arguments.
        case args of
        [CDecl [CTypeSpec (CVoidType _)] [] _] -> []
        _ -> args
    , let ([], [], argtypequals, argtypespecs, False) = partitionDeclSpecs argspecs
    ]

interpretFunction :: Show a => CFunctionDef a -> EnvMonad Rust.Item
-- Note that function definitions can't be anonymous and their derived
-- declarators must begin with CFunDeclr.
interpretFunction (CFunDef specs (CDeclr ~(Just ident) ~declarators@(CFunDeclr args _ _ : _) _ _ _) _ body _) = do
    args' <- functionArgs args

    let (storage, [], typequals, typespecs, _inline) = partitionDeclSpecs specs
        vis = case storage of
            [CStatic _] -> Rust.Private
            [] -> Rust.Public
            _ -> error ("interpretFunction: unsupported storage specifiers " ++ show storage)
        name = identToString ident

    -- Mutability is meaningless on function definitions.
    (_mut, funTy@(IsFunc retTy _)) <- cTypeOf typequals typespecs declarators

    -- Add this function to the globals before evaluating its body so
    -- recursive calls work.
    addVar ident (Rust.Mutable, funTy)

    -- Open a new scope for the formal parameters.
    scope $ do
        formals <- sequence
            [ do
                addVar argname (mut, ty)
                return (mut, Rust.VarName (identToString argname), toRustType ty)
            | ~(Just (mut, argname), ty) <- args'
            ]
        let noLoop = error ("interpretFunction: break or continue statement outside any loop in " ++ name)
        body' <- interpretStatement retTy noLoop noLoop body
        return (Rust.Function vis name formals (toRustType retTy) (Rust.Block (toBlock body') Nothing))

interpretTranslationUnit :: Show a => CTranslationUnit a -> [Rust.Item]
interpretTranslationUnit (CTranslUnit decls _) = catMaybes $ flip evalState [] $ do
    forM decls $ \ decl -> case decl of
        CFDefExt f -> fmap Just (interpretFunction f)
        CDeclExt (CDecl specs declarators _) -> do
            let (storagespecs, [], typequals, typespecs, _inline) = partitionDeclSpecs specs
            sequence_ $ case storagespecs of
                [CTypedef _] ->
                    [ addType ident =<< cTypeOf typequals typespecs derived
                    -- Typedefs must have a declarator which must not be
                    -- abstract, and must not have an initializer or size.
                    | ~(Just (CDeclr (Just ident) derived _ _ _), Nothing, Nothing) <- declarators
                    ]
                _ ->
                    [ addVar ident =<< cTypeOf typequals typespecs derived
                    -- Top-level declarations must have a declarator
                    -- which must not be abstract, and must not have a
                    -- size. They may have an initializer.
                    -- TODO: emit declarations with optional
                    -- initializers for non-functions.
                    | ~(Just (CDeclr (Just ident) derived _ _ _), _, Nothing) <- declarators
                    ]
            return Nothing
        _ -> return Nothing -- FIXME: ignore everything but function declarations for now
