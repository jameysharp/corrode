This is a "Literate Haskell" source file. It is meant to be read as
documentation but it's also compilable source code. The text is
formatted using Markdown so GitHub can render it nicely.

This module translates source code written in C into source code written
in Rust. Well, that's a small lie. For both C and Rust source we use an
abstract representation rather than the raw source text. The C
representation comes from the
[language-c](http://hackage.haskell.org/package/language-c) package, and
the Rust representation is in Corrode's `Language.Rust.AST` module.

I've tried to stick to the standard features of the Haskell2010
language, but GHC's `ViewPatterns` extension is too useful for this kind
of code.

```haskell
{-# LANGUAGE ViewPatterns #-}
```

This module exports a single function which transforms a C "translation
unit" (terminology from the C standard and reused in language-c) into a
collection of Rust "items" (terminology from the Rust language
specification). It imports the C and Rust ASTs, plus a handful of other
useful data structures and control flow abstractions.

```haskell
module Language.Rust.Corrode.C (interpretTranslationUnit) where

import Control.Monad
import Control.Monad.Trans.RWS.Strict
import Data.Char
import Data.Foldable
import Data.Maybe
import Data.List
import Language.C
import qualified Language.Rust.AST as Rust
import Text.PrettyPrint
```

This translation proceeds in a syntax-directed way. That is, we just
walk down the C abstract syntax tree, and for each piece of syntax we
find, we decide what the equivalent Rust should be.

A tool like this could use a more sophisticated strategy than the purely
syntax-directed approach. We could construct intermediate data
structures like most modern compilers do, such as a control flow graph,
and do fancy analysis passes over those data structures.

However, purely syntax-directed translation has two advantages:

1. The implementation is simpler,
2. and it's easier to preserve as much structure as possible from the
   source program, which is one of Corrode's design goals.

So far, we haven't needed more sophisticated approaches, and we'll stick
with syntax-directed style for as long as possible.

That said, we do need to maintain some data structures with intermediate
results as we go through the translation.


Intermediate data structures
============================

One of the biggest challenges in correctly translating C to Rust is that
we need to know what type C would give every expression, so we can
ensure that the Rust equivalent uses the same types. To do that, we need
to maintain a list of all the names that are currently in scope, along
with their type information. This is called an `Environment` and we'll
give it a handy type alias to use later.

```haskell
type Environment = [(IdentKind, (Rust.Mutable, CType))]
```

We'll come back to our internal representation of C types at the end of
this module.

C has several different namespaces for different kinds of names. For
example, here is a legal snippet of C source, using the name `foo` in
several different ways:

```c
typedef struct foo { struct foo *foo; } foo;
foo foo;
```

Fortunately, language-c does the hard work for us of disambiguating
these different uses of identical-looking names. As we'll see later,
whenever an identifier occurs, we can tell which namespace to use for it
from the AST context in which it appeared. However, we still need to
keep these names separate in the environment, so we define a simple type
to label identifiers with their namespace.

```haskell
data IdentKind
    = SymbolIdent Ident
    | TypedefIdent Ident
    | StructIdent Ident
    deriving Eq
```

Sometimes we need to construct a unique name, because the Rust pattern
we want to generate requires a name someplace where C did not require
one. We'll follow a standard pattern for this and just generate a unique
number each time we need a new name.

```haskell
data EnvState = EnvState
    { environment :: Environment
    , unique :: Int
    }
```

The C language is defined such that a compiler can generate code in a
single top-to-bottom pass through a translation unit. That is, any uses
of a name must come after the point in the translation unit where that
name is first declared.

That's convenient for us, because it means we can easily keep the
environment in a "state monad", and emit the translated Rust items using
a "writer monad". These are fancy terms for objects that have some
simple operations.

- The state monad has `get`, `put`, and `modify` operations that we use
  to query or update the current enviroment.
- The writer monad has a `tell` operation we use to add new Rust items
  to the output.

Actually, we use a combined type, `RWS`, which supports the operations
of reader, writer, and state monads all in one. We use the reader monad
for control flow context, which is covered in more detail in the section
on statements, below.

You probably don't need to read any of the awful monad tutorials out
there just to use these! The important point is that we have this type
alias, `EnvMonad`, which you'll see throughout this module. It marks
pieces of code which have access to the environment and the output.

```haskell
type EnvMonad = RWS ControlFlow ([Rust.Item], [Rust.ExternItem]) EnvState
```

In fact, we're going to wrap up the monad operations in some helper
functions, and then only use these helpers everywhere else.

`getIdent` looks up a name from the given namespace in the environment,
and returns the type information we have for it, or `Nothing` if we
haven't seen a declaration for that name yet.

```haskell
getIdent :: IdentKind -> EnvMonad (Maybe (Rust.Mutable, CType))
getIdent ident = do
    env <- gets environment
    return (lookup ident env)
```

`addIdent` saves type information into the environment.

```haskell
addIdent :: IdentKind -> (Rust.Mutable, CType) -> EnvMonad ()
addIdent ident ty = modify $ \ st ->
    st { environment = (ident, ty) : environment st }
```

`uniqueName` generates a new name with the given base and a new unique
number:

```haskell
uniqueName :: String -> EnvMonad String
uniqueName base = do
    st <- get
    put (st { unique = unique st + 1 })
    return (base ++ show (unique st))
```

`emitItems` adds a list of Rust items to the output.

```haskell
emitItems :: [Rust.Item] -> EnvMonad ()
emitItems items = tell (items, [])
```

`emitExterns` adds to the output a list of functions or global variables
which _may_ be declared in some other translation unit. (We can't tell
when we see a C extern declaration whether it's just the prototype for a
definition that we'll find later in the current translation unit, so
there's a de-duplication pass at the end of `interpretTranslationUnit`.)

```haskell
emitExterns :: [Rust.ExternItem] -> EnvMonad ()
emitExterns items = tell ([], items)
```


Reporting errors
================

There will always be C source code that language-c parses happily but
Corrode can't translate to Rust, and we should report as much helpful
explanation as possible when that happens.

```haskell
noTranslation :: (Pretty node, Pos node) => node -> String -> EnvMonad a
noTranslation node msg = fail $ concat
    [ show (posOf node)
    , ": "
    , msg
    , ":\n"
    , render (nest 4 (pretty node))
    ]
```

In some cases, we should be able to translate the given input, but the
translation just hasn't been implemented yet.

```haskell
unimplemented :: (Pretty node, Pos node) => node -> EnvMonad a
unimplemented node = noTranslation node "Corrode doesn't handle this yet"
```

Some C source is illegal according to the C standard but is nonetheless
syntactically valid. Corrode does not promise to detect all of these
cases, but we can call `badSource` when we do detect such an error.

```haskell
badSource :: (Pretty node, Pos node) => node -> String -> EnvMonad a
badSource node msg = noTranslation node
    ("illegal " ++ msg ++ "; check whether a real C compiler accepts this")
```


Top-level translation
=====================

Since we're taking the syntax-directed approach, let's start by looking
at how we handle the root of the C AST: the "translation unit". This is
C's term for a single source file (`*.c`), but since this code operates
on already pre-processed source, the translation unit includes any code
that was `#include`d from header files as well.

(It would be nice to be able to translate macros and
conditionally-compiled code to similar constructs in Rust, but it's much
more difficult to write a reasonable C parser for source code that
hasn't been run through the C pre-processor yet. And that's saying
something, as parsing even pre-processed C is hard. So language-c runs
the pre-processor from either `gcc` or `clang` before parsing the source
file you hand it. See Corrode's `Main.hs` for the driver code.)

`interpretTranslationUnit` takes a language-c AST representation of a
translation unit, and returns a list of Rust AST top-level declaration
items.

```haskell
interpretTranslationUnit :: CTranslUnit -> [Rust.Item]
interpretTranslationUnit (CTranslUnit decls _) = items'
    where
```

Here at the top level of the translation unit, we need to extract the
translation results from the writer and state monads described above.
Specifically, we:

- set the environment to be initially empty;
- discard the final environment as we don't need any of the intermediate
  type information once translation is done;
- and get the final lists of items and externs that were emitted during
  translation.

```haskell
    initFlow = ControlFlow
        { functionReturnType = flip badSource "return statement outside function"
        , onBreak = flip badSource "break outside loop"
        , onContinue = flip badSource "continue outside loop"
        }
    initState = EnvState
        { environment = []
        , unique = 1
        }
    (_, _, (items, externs)) = runRWS (mapM_ perDecl decls) initFlow initState
```

With the initial environment set up, we can descend to the next level of
the abstract syntax tree, where the language-c types tell us there are
three possible kinds for each declaration:

```haskell
    perDecl (CFDefExt f) = do
        f' <- interpretFunction f
        emitItems [f']
    perDecl (CDeclExt decl') = do
        binds <- interpretDeclarations makeStaticBinding decl'
        emitItems binds
    perDecl decl = unimplemented decl
```

Next we remove any locally-defined names from the list of external
declarations. We can't tell whether something is actually external when
we encounter its declaration, but once we've collected all the symbols
for this translation unit it becomes clear.

```haskell
    itemNames = catMaybes
        [ case item of
            Rust.Item _ (Rust.Function name _ _ _) -> Just name
            Rust.Item _ (Rust.Static _ (Rust.VarName name) _ _) -> Just name
            _ -> Nothing
        | item <- items
        ]

    externName (Rust.ExternFn name _ _ _) = name
    externName (Rust.ExternStatic _ (Rust.VarName name) _) = name
    externs' = filter (\ item -> externName item `notElem` itemNames) externs
```

If there are any external declarations after filtering, then we need to
wrap them in an `extern { }` block. We place that before the other
items, by convention.

```haskell
    items' = if null externs'
        then items
        else Rust.Item Rust.Private (Rust.Extern externs') : items
```


Declarations
============

C declarations appear the same, syntactically, whether they're at
top-level or local to a function. `interpretDeclarations` handles both
cases.

However, Rust has a different set of cases which we need to map onto:
variables with `'static` lifetime are declared using `static` items,
regardless of whether they're local or at top-level; while local
variables are declared using `let`-binding statements.

So `interpretDeclarations` is parameterized by a function,
`makeBinding`, which can construct a `static` item or a `let`-binding
from non-static C variable declarations. In either case, the binding

- may be mutable or immutable (`const`);
- has a variable name;
- has a type (which we choose to be explicit about even for
  `let`-bindings where the type could generally be inferred);
- and may have an initializer expression.

The return type of the function depends on which kind of binding it's
constructing.

```haskell
type MakeBinding a = Rust.Mutable -> Rust.Var -> Rust.Type -> Maybe Rust.Expr -> a
```

It's up to the caller to provide an appropriate implementation of
`makeBinding`, but there are only two sensible choices, which we'll
define here for convenient use elsewhere.

> **TODO**: `makeBinding` should only be used for non-`static` C
> variable declarations, since declarations with the `static` storage
> class should be translated to Rust static items regardless of whether
> they're local or global. Then, since `makeStaticBinding` is used for
> top-level declarations and will only be called for non-`static`
> declarations, the static items it constructs should be public.

> **FIXME**: Construct a correct default value for non-scalar static
> variables.

```haskell
makeStaticBinding :: MakeBinding Rust.Item
makeStaticBinding mut var ty mexpr = Rust.Item Rust.Private
    (Rust.Static mut var ty (fromMaybe 0 mexpr))

makeLetBinding :: MakeBinding Rust.Stmt
makeLetBinding mut var ty mexpr = Rust.Let mut var (Just ty) mexpr
```

Now that we know how to translate variable declarations, everything else
works the same regardless of where the declaration appears. Here are a
sample of the simplest cases we have to handle at this point:

```c
// variable definition, with initial value
int x = 42;

// variable declaration, which might refer to another module
extern int y;

// type alias
typedef int my_int;

// struct definition
struct my_struct {
    // using the type alias
    my_int field;
};

// variable definition using previously-defined struct
struct my_struct s;

// function prototypes, which might refer to another module
int f(struct my_struct *);
extern int g(my_int i);

// function prototype for a definitely-local function
static int h(void);
```

Some key things to note:

- C allows as few as **zero** "declarators" in a declaration. In the
  above examples, the definition of `struct my_struct` has zero
  declarators, while all the other declarations have one declarator
  each.

- `struct`/`union`/`enum` definitions are a kind of declaration
  specifier, like `int` or `const` or `static`, so we have to dig them
  out of the declarations where they appear&mdash;possibly nested inside
  other `struct` definitions, and possibly with variables immediately
  declared as having the new type. In Rust, each `struct` definition
  must be a separate item, and then after that any variables can be
  declared using the new types.

- Syntactically, `typedef` is a storage class specifier just like
  `static` or `extern`. But semantically, they couldn't be more
  different!

And here are some legal declarations which illustrate how weirdly
complicated C's declaration syntax is.

- These have no effect because they only have declaration specifiers, no
  declarators:

    ```c
    int;
    const typedef volatile void;
    ```

- Declare both a variable of type `int`, and a function prototype for a
  function returning `int`:

    ```c
    int i, fun(void);
    ```

- Declare variables of type `int`, pointer to `int`, function returning
  pointer to `int`, and pointer to function returning `int`,
  respectively:

    ```c
    int j, *p, *fip(void), (*fp)(void);
    ```

- Declare type aliases for both `int` and `int *`:

    ```c
    typedef int new_int, *int_ptr;
    ```

OK, let's see how `interpretDeclarations` handles all these cases. It
takes one of the `MakeBinding` implementations and a single C
declaration. It returns a list of bindings constructed using
`MakeBinding`, and also updates the environment and output as needed.

```haskell
interpretDeclarations :: MakeBinding b -> CDecl -> EnvMonad [b]
interpretDeclarations makeBinding (CDecl specs decls _) = do
```

First, we call `baseTypeOf` to get our internal representation of the
type described by the declaration specifiers. That function will also
add any `struct`s defined in this declaration to the environment so we
can look them up if they're referred to again, and emit those structs as
items in the output.

If there are no declarators, then `baseTypeOf`'s side effects are the
only output from this function.

```haskell
    (storagespecs, baseTy) <- baseTypeOf specs
```

If there are any declarators, we need to figure out which kind of Rust
declaration to emit for each one, if any.

```haskell
    mbinds <- forM decls $ \ (Just decl@(CDeclr (Just ident) derived _ _ _), minit, Nothing) -> do
        (mut, ty) <- derivedTypeOf baseTy decl
        let name = identToString ident
        case (derived, storagespecs) of
```

Typedefs must have a declarator which must not be abstract, and must not
have an initializer or size. Each declarator is added to the
environment, tagged as a `TypedefIdent`. They do not return any
declarations, so the only effect of a `typedef` is to update the
environment.

> **TODO**: It would be nice to emit a type-alias item for each
> `typedef` and use the alias names anywhere we can, instead of
> replacing the aliases with the underlying type everywhere. That way we
> preserve more of the structure of the input program. But it isn't
> always possible, so this requires careful thought.

```haskell
            (_, Just (CTypedef _)) -> do
                addIdent (TypedefIdent ident) (mut, ty)
                return Nothing
```

Non-typedef declarations must have a declarator which must not be
abstract, and must not have a size. They may have an initializer. Each
declarator is added to the environment, tagged as a `SymbolIdent`.

Static function prototypes don't need to be translated because the
function definition must be in the same translation unit. We still need
to have the function's type signature in the environment though.

```haskell
            (CFunDeclr {} : _, Just (CStatic _)) -> do
                addIdent (SymbolIdent ident) (mut, ty)
                return Nothing
```

Other function prototypes need to be translated unless the function
definition appears in the same translation unit; do it and prune
duplicates later.

```haskell
            (CFunDeclr args _ _ : _, _) -> do
                (args', variadic) <- functionArgs decl args
                let (IsFunc retTy _ _) = ty
                    formals =
                        [ (Rust.VarName argName, toRustType argTy)
                        | (idx, (mname, argTy)) <- zip [1 :: Int ..] args'
                        , let argName = maybe ("arg" ++ show idx) (identToString . snd) mname
                        ]
                addIdent (SymbolIdent ident) (mut, ty)
                emitExterns [Rust.ExternFn name formals variadic (toRustType retTy)]
                return Nothing
```

Non-function externs need to be translated unless an identical
non-extern declaration appears in the same translation unit; do it and
prune duplicates later.

```haskell
            (_, Just (CExtern _)) -> do
                addIdent (SymbolIdent ident) (mut, ty)
                emitExterns [Rust.ExternStatic mut (Rust.VarName name) (toRustType ty)]
                return Nothing
```

Anything else is a variable declaration to translate. This is the only
case where we use `makeBinding`. If there's an initializer, we also need
to translate that; see below.

```haskell
            _ -> do
                addIdent (SymbolIdent ident) (mut, ty)
                mexpr <- mapM (interpretInitializer ty) minit
                return (Just (makeBinding mut (Rust.VarName name) (toRustType ty) mexpr))
```

Return the bindings produced for any declarator that did not return
`Nothing`.

```haskell
    return (catMaybes mbinds)
```

If a declarator had an initializer, we need to translate that to an
equivalent Rust expression. `interpretInitializer` needs to know the
type of the variable we're initializing in order to figure out how to
interpret the initializer.

```haskell
interpretInitializer :: CType -> CInit -> EnvMonad Rust.Expr
```

Initializers for compound types must be surrounded by braces. If we're
initializing a compound type and see an initializer expression instead,
that's a syntax error.

> **FIXME**: This is particularly hard due to C99's semantics around
> partial initialization! And the current implementation is woefully
> incomplete. This version will throw a runtime exception if any labeled
> initializers (e.g. `.field = 12`) are used, and it will generate
> invalid Rust if there are fewer initializers than there are fields in
> the `struct` type.

```haskell
interpretInitializer (IsStruct str fields) initial = case initial of
    CInitList binds _ -> Rust.StructExpr str <$> sequence
        [ case bind of
            ([], v) -> (,) field <$> interpretInitializer ty v
            _ -> unimplemented initial
        | ((field, ty), bind) <- zip fields binds
        ]
    _ -> badSource initial "struct initializer"
```

Initializers for scalar types must either be a bare expression or the
same surrounded by braces. Anything else is a syntax error.

```haskell
interpretInitializer ty (CInitExpr initial _)
    = fmap (castTo ty) (interpretExpr True initial)
interpretInitializer ty (CInitList [([], CInitExpr initial _)] _)
    = fmap (castTo ty) (interpretExpr True initial)
interpretInitializer _ initial = badSource initial "scalar initializer"
```


Function definitions
====================

A C function definition translates to a single Rust item.

```haskell
interpretFunction :: CFunDef -> EnvMonad Rust.Item
```

Function definitions can't be anonymous and their derived declarators
must begin with CFunDeclr. Anything else is a syntax error.

```haskell
interpretFunction (CFunDef specs
        declr@(CDeclr (Just ident) (CFunDeclr args _ _ : _) _ _ _)
    _ body _) = do
```

Translate into our internal representation the function's name, formal
parameters, and return type. Determine whether the function should be
visible outside this module based on whether it is declared `static`.

Definitions of variadic functions are not allowed because Rust does not
support them.

Note that `const` is legal but meaningless on the return type of a
function in C. We just ignore whether it was present; there's no place
we can put a `mut` keyword in the generated Rust.

```haskell
    (args', False) <- functionArgs declr args
    (storage, baseTy) <- baseTypeOf specs
    vis <- case storage of
        Nothing -> return Rust.Public
        Just (CStatic _) -> return Rust.Private
        Just s -> badSource s "storage class specifier for function"
    let name = identToString ident
    (_mut, funTy@(IsFunc retTy _ _)) <- derivedTypeOf baseTy declr
```

Add this function to the globals before evaluating its body so recursive
calls work.

```haskell
    addIdent (SymbolIdent ident) (Rust.Mutable, funTy)
```

Open a new scope for the body of this function, while making the return
type available so we can correctly translate `return` statements.

```haskell
    let setRetTy flow = flow { functionReturnType = const (return retTy) }
    local setRetTy $ scope $ do
```

Add each formal parameter into the new environment, tagged as
`SymbolIdent`.

> **XXX**: We currently require that every parameter have a name, but
> I'm not sure that C actually requires that. If it doesn't, we should
> create dummy names for any anonymous parameters because Rust requires
> everything be named, but we should not add the dummy names to the
> environment because those parameters were not accessible in the
> original program.

```haskell
        formals <- sequence
            [ case arg of
                Just (mut, argname) -> do
                    addIdent (SymbolIdent argname) (mut, ty)
                    return (mut, Rust.VarName (identToString argname), toRustType ty)
                Nothing -> badSource declr "anonymous parameter"
            | (arg, ty) <- args'
            ]
```

Interpret the body of the function.

```haskell
        body' <- interpretStatement body
```

The body's Haskell type is `CStatement`, but language-c guarantees that
it is specifically a compound statement (the `CCompound` constructor).
Rather than relying on that, we allow it to be any kind of statement and
use `toBlock` to coerce the resulting Rust expression into a list of
Rust statements, and wrap that up in a Rust block.

Since C doesn't have Rust's syntax allowing the last expression to be
the result of the function, this generated block never has a final
expression.

```haskell
        let block = Rust.Block (toBlock body') Nothing
        return (Rust.Item vis (Rust.Function name formals (toRustType retTy) block))
```

Report a syntax error if the above pattern didn't match.

```haskell
interpretFunction (CFunDef _ decl _ _ _) = badSource decl "function definition"
```

There are several places we need to process function argument lists.
`functionArgs` distils language-c's represention of the gory details of
C syntax down to just the information we need. Specifically, we return a
list of the arguments and a flag indicating whether the function is
"variadic", meaning that any number of additional arguments are allowed.

```haskell
functionArgs
    :: CDeclr
    -> Either [Ident] ([CDecl], Bool)
    -> EnvMonad ([(Maybe (Rust.Mutable, Ident), CType)], Bool)
```

> **TODO**: Handling old-style function declarations is probably not
> _too_ difficult...

```haskell
functionArgs decl (Left _) = unimplemented decl
functionArgs _ (Right (args, variadic)) = do
    args' <- sequence
        [ do
            (storage, base) <- baseTypeOf argspecs
            case storage of
                Nothing -> return ()
                Just (CRegister _) -> return ()
                Just s -> badSource s "storage class specifier on argument"
            case declr of
                [] -> return (Nothing, snd base)
                [(Just argdeclr@(CDeclr argname _ _ _ _), Nothing, Nothing)] -> do
                    (mut, ty) <- derivedTypeOf base argdeclr
                    return (fmap ((,) mut) argname, ty)
                _ -> badSource arg "function argument"
        | arg@(CDecl argspecs declr _) <-
```

Treat argument lists `(void)` and `()` the same: we'll pretend that both
mean the function takes no arguments.

```haskell
            case args of
            [CDecl [CTypeSpec (CVoidType _)] [] _] -> []
            _ -> args
        ]
    return (args', variadic)
```


Statements
==========

In order to interpret `return`, `break`, and `continue` statements, we
need a bit of extra context, which we'll discuss as we go. Let's wrap
that context up in a simple data type.

```haskell
data ControlFlow = ControlFlow
    { functionReturnType :: CStat -> EnvMonad CType
    , onBreak :: CStat -> EnvMonad Rust.Expr
    , onContinue :: CStat -> EnvMonad Rust.Expr
    }
```

Inside a function, we find C statements. Interestingly, syntax which is
a statement in C is almost always an expression instead in Rust. So
`interpretStatement` transforms one `CStatement` into one Rust
expression.

```haskell
interpretStatement :: CStat -> EnvMonad Rust.Expr
```

A C statement might be as simple as a "statement expression", which
amounts to a C expression followed by a semicolon. In that case we can
translate the statement by just translating the expression.

The first argument to `interpretExpr` indicates whether the expression
appears in a context where its result matters. In a statement
expression, the result is discarded, so we pass `False`.

```haskell
interpretStatement (CExpr (Just expr) _) = do
    expr' <- interpretExpr False expr
    return (result expr')
```

We could have a "compound statement", also known as a "block". A
compound statement contains a sequence of zero or more statements or
declarations; see `interpretBlockItem` below for details.

```haskell
interpretStatement (CCompound [] items _) = scope $ do
    stmts <- mapM interpretBlockItem items
    return (Rust.BlockExpr (Rust.Block (concat stmts) Nothing))
```

This statement could be an `if` statement, with its conditional
expression and "then" branch, and maybe an "else" branch.

The conditional expression is numeric in C, but must have type `bool` in
Rust. We use the `toBool` helper defined below to convert the expression
if necessary.

In C, the "then" and "else" branches are each statements (which may be
compound statements, if they're surrounded by curly braces), but in Rust
they must each be blocks (so they're always surrounded by curly braces).
Here we use `toBlock` to coerce both branches into lists of statements,
and wrap those lists up into blocks, so we don't care whether the
original program used a compound statement in that branch or not.

```haskell
interpretStatement (CIf c t mf _) = do
    c' <- interpretExpr True c
    t' <- fmap toBlock (interpretStatement t)
    f' <- maybe (return []) (fmap toBlock . interpretStatement) mf
    return (Rust.IfThenElse (toBool c') (Rust.Block t' Nothing) (Rust.Block f' Nothing))
```

`while` loops are easy to translate from C to Rust. They have identical
semantics in both languages, aside from differences analagous to the
`if` statement, where the loop condition must have type `bool` and the
loop body must be a block.

```haskell
interpretStatement (CWhile c b False _) = do
    c' <- interpretExpr True c
    b' <- loopScope (Rust.Break Nothing) (Rust.Continue Nothing) (interpretStatement b)
    return (Rust.While Nothing (toBool c') (Rust.Block (toBlock b') Nothing))
```

C's `for` loops can be tricky to translate to Rust, which doesn't have
anything quite like them.

Oh, the initialization/declaration part of the loop is easy enough. Open
a new scope, insert any assignments and `let`-bindings at the beginning
of it, and we're good to go.

```haskell
interpretStatement (CFor initial mcond mincr b _) = scope $ do
    pre <- case initial of
        Left Nothing -> return []
        Left (Just expr) -> do
            expr' <- interpretExpr False expr
            return [Rust.Stmt (result expr')]
        Right decls -> interpretDeclarations makeLetBinding decls
```

The challenge is that Rust doesn't have a loop form that updates
variables when an iteration ends and the loop condition is about to run.
In the presence of `continue` statements, this is a peculiar kind of
non-local control flow. To avoid duplicating code, we wrap the loop body
in

```rust
    'continueTo: loop { ...; break; }
```

which, although it's syntactically an infinite loop, will only run once;
and transform any continue statements into

```rust
    break 'continueTo;
```

We then give the outer loop a `'breakTo:` label and transform break
statements into

```rust
    break 'breakTo;
```

so that they refer to the outer loop, not the one we inserted.

```haskell
    (lt, b') <- case mincr of
        Just incr -> do
            breakName <- uniqueName "break"
            continueName <- uniqueName "continue"
            let breakTo = Just (Rust.Lifetime breakName)
            let continueTo = Just (Rust.Lifetime continueName)

            b' <- loopScope (Rust.Break breakTo) (Rust.Break continueTo) (interpretStatement b)
            let end = Rust.Stmt (Rust.Break Nothing)
            let innerBlock = Rust.Block (toBlock b' ++ [end]) Nothing
            let inner = Rust.Stmt (Rust.Loop continueTo innerBlock)

            incr' <- interpretExpr False incr
            let outerBlock = Rust.Block [inner, Rust.Stmt (result incr')] Nothing
            return (breakTo, Rust.BlockExpr outerBlock)
```

We can generate simpler code in the special case that this `for` loop
has an empty increment expression. In that case, we can translate
`break`/`continue` statements into simple `break`/`continue`
expressions, with no magic loops inserted into the body.

```haskell
        Nothing -> do
            b' <- loopScope (Rust.Break Nothing) (Rust.Continue Nothing) (interpretStatement b)
            return (Nothing, b')
    let block = Rust.Block (toBlock b') Nothing
```

If the condition is empty, the loop should translate to Rust's infinite
`loop` expression. Otherwise it translates to a `while` loop with the
given condition. In either case, we apply the label selected previously
to this loop.

```haskell
    loop <- case mcond of
        Nothing -> return (Rust.Loop lt block)
        Just cond -> do
            cond' <- interpretExpr True cond
            return (Rust.While lt (toBool cond') block)
```

Now we have all the pieces to assemble a Rust equivalent to the original
`for` loop. Create a block, beginning with any initialization and ending
with the selected variety of loop.

```haskell
    return (Rust.BlockExpr (Rust.Block pre (Just loop)))
```

`continue` and `break` statements translate to whatever expression we
decided on in the surrounding context. For example, `continue` might
translate to `break 'continueTo` if our nearest enclosing loop is a
`for` loop.

```haskell
interpretStatement stmt@(CCont _) = getFlow stmt onContinue
interpretStatement stmt@(CBreak _) = getFlow stmt onBreak
```

`return` statements are pretty straightforward&mdash;translate the
expression we're supposed to return, if there is one, and return the
Rust equivalent&mdash;except that Rust is more strict about types than C
is. So if the return expression has a different type than the function's
declared return type, then we need to insert a type-cast to the correct
type.

```haskell
interpretStatement stmt@(CReturn expr _) = do
    retTy <- getFlow stmt functionReturnType
    expr' <- mapM (fmap (castTo retTy) . interpretExpr True) expr
    return (Rust.Return expr')
```

Otherwise, this is a type of statement we haven't implemented a
translation for yet.

> **TODO**: Translate more kinds of statements. `:-)`

```haskell
interpretStatement stmt = unimplemented stmt
```

The fields in `ControlFlow` are monadic actions which take a C statement
as an argument, so that if there's an error we can report which
statement was at fault. `getFlow` is a helper function to thread
everything through correctly.

```haskell
getFlow :: CStat -> (ControlFlow -> CStat -> EnvMonad a) -> EnvMonad a
getFlow stmt kind = do
    val <- asks kind
    val stmt
```

Inside loops above, we needed to update the translation to use if either
`break` or `continue` statements show up. `loopScope` runs the provided
translation action using an updated pair of `break`/`continue`
expressions.

```haskell
loopScope :: Rust.Expr -> Rust.Expr -> EnvMonad a -> EnvMonad a
loopScope b c = local $ \ flow ->
    flow { onBreak = const (return b), onContinue = const (return c) }
```


Blocks and scopes
=================

In compound statements (see above), we may encounter local declarations
as well as nested statements. `interpretBlockItem` produces a sequence
of zero or more Rust statements for each compound block item.

```haskell
interpretBlockItem :: CBlockItem -> EnvMonad [Rust.Stmt]
interpretBlockItem (CBlockStmt stmt) = do
    stmt' <- interpretStatement stmt
    return [Rust.Stmt stmt']
interpretBlockItem (CBlockDecl decl) = interpretDeclarations makeLetBinding decl
interpretBlockItem item = unimplemented item
```

`toBlock` is a helper function which turns a Rust expression into a list
of Rust statements. It's always possible to do this by wrapping the
expression in the `Rust.Stmt` constructor, but there are a bunch of
places in this translation where we don't want to have to think about
whether the expression is already a block expression to avoid inserting
excess pairs of curly braces everywhere.

```haskell
toBlock :: Rust.Expr -> [Rust.Stmt]
toBlock (Rust.BlockExpr (Rust.Block stmts Nothing)) = stmts
toBlock e = [Rust.Stmt e]
```

`scope` runs the translation steps in `m`, but then throws away any
changes that `m` made to the environment. Any items added to the output
are kept, though.

```haskell
scope :: EnvMonad a -> EnvMonad a
scope m = do
    -- Save the current environment.
    old <- gets environment
    a <- m
    -- Restore the environment to its state before running m.
    modify (\ st -> st { environment = old })
    return a
```


Expressions
===========

Translating expressions works by a bottom-up traversal of the expression
tree: we compute the type of a sub-expression, then use that to
determine what the surrounding expression means.

We also need to record whether the expression is a legitimate "l-value",
which determines whether we can assign to it or take mutable borrows of
it. Here we abuse the `Rust.Mutable` type: If it is `Mutable`, then it's
a legal l-value, and if it's `Immutable` then it is not.

Finally, of course, we record the Rust AST for the sub-expression so it
can be combined into the larger expression that we're building up.

```haskell
data Result = Result
    { resultType :: CType
    , isMutable :: Rust.Mutable
    , result :: Rust.Expr
    }
```

`interpretExpr` translates a `CExpression` into a Rust expression, along
with the other metadata in `Result`.

It also takes a boolean parameter, `demand`, indicating whether the
caller intends to use the result of this expression. For some C
expressions, we have to generate extra Rust code if the result is
needed.

```haskell
interpretExpr :: Bool -> CExpr -> EnvMonad Result
```

C's comma operator evaluates its left-hand expressions for their side
effects, throwing away their results, and then evaluates to the result
of its right-hand expression.

Rust doesn't have a dedicated operator for this, but it works out the
same as Rust's block expressions: `(e1, e2, e3)` can be translated to
`{ e1; e2; e3 }`. If the result is not going to be used, we can
translate it instead as `{ e1; e2; e3; }`, where the expressions are
semicolon-terminated instead of semicolon-separated.

```haskell
interpretExpr demand (CComma exprs _) = do
    let (effects, mfinal) = if demand then (init exprs, Just (last exprs)) else (exprs, Nothing)
    effects' <- mapM (fmap (Rust.Stmt . result) . interpretExpr False) effects
    mfinal' <- mapM (interpretExpr True) mfinal
    return Result
        { resultType = maybe IsVoid resultType mfinal'
        , isMutable = maybe Rust.Immutable isMutable mfinal'
        , result = Rust.BlockExpr (Rust.Block effects' (fmap result mfinal'))
        }
```

C's assignment operator is complicated enough that, after translating
the left-hand and right-hand sides recursively, we just delegate to the
`compound` helper function defined below.

```haskell
interpretExpr demand expr@(CAssign op lhs rhs _) = do
    lhs' <- interpretExpr True lhs
    rhs' <- interpretExpr True rhs
    compound expr False demand op lhs' rhs'
```

C's ternary conditional operator (`c ? t : f`) translates fairly
directly to Rust's `if`/`else` expression.

But we have to be particularly careful about how we generate `if`
expressions when the result is not used. When most expressions are used
as statements, it doesn't matter what type the expression has, because
the result is ignored. But when a Rust `if`-expression is used as a
statement, its type is required to be `()`. We can ensure the type is
correct by wrapping the true and false branches in statements rather
than placing them as block-final expressions.

```haskell
interpretExpr demand expr@(CCond c (Just t) f _) = do
    c' <- fmap toBool (interpretExpr True c)
    t' <- interpretExpr demand t
    f' <- interpretExpr demand f
    if demand
        then promote expr (\ t'' f'' -> Rust.IfThenElse c' (Rust.Block [] (Just t'')) (Rust.Block [] (Just f''))) t' f'
        else return Result
            { resultType = IsVoid
            , isMutable = Rust.Immutable
            , result = Rust.IfThenElse c' (Rust.Block (toBlock (result t')) Nothing) (Rust.Block (toBlock (result f')) Nothing)
            }
```

C's binary operators are complicated enough that, after translating the
left-hand and right-hand sides recursively, we just delegate to the
`binop` helper function defined below.

```haskell
interpretExpr _ expr@(CBinary op lhs rhs _) = do
    lhs' <- interpretExpr True lhs
    rhs' <- interpretExpr True rhs
    binop expr op lhs' rhs'
```

C's cast operator corresponds exactly to Rust's cast operator. The
syntax is quite different but the semantics are the same. Note that the
result of a cast is never a legal l-value.

```haskell
interpretExpr _ (CCast decl expr _) = do
    ty <- typeName decl
    expr' <- interpretExpr True expr
    return Result
        { resultType = ty
        , isMutable = Rust.Immutable
        , result = Rust.Cast (result expr') (toRustType ty)
        }
```

We de-sugar the pre/post-increment/decrement operators into compound
assignment operators and call the common assignment helper.

```haskell
interpretExpr demand node@(CUnary op expr _) = case op of
    CPreIncOp -> incdec False CAddAssOp
    CPreDecOp -> incdec False CSubAssOp
    CPostIncOp -> incdec True CAddAssOp
    CPostDecOp -> incdec True CSubAssOp
```

We translate C's address-of operator (unary prefix `&`) to either a
mutable or immutable borrow operator, followed by a cast to the
corresponding Rust raw-pointer type.

We re-use the l-value flag to decide whether this is a mutable or
immutable borrow. If the sub-expression is a valid l-value, then it's
always safe to take a mutable pointer to it. Otherwise, it may be OK to
take an immutable pointer, or it may be nonsense.

This implementation does not check for the nonsense case. If you get
weird results, make sure your input C compiles without errors using a
real C compiler.

```haskell
    CAdrOp -> do
        expr' <- interpretExpr True expr
        let ty' = IsPtr (isMutable expr') (resultType expr')
        return Result
            { resultType = ty'
            , isMutable = Rust.Immutable
            , result = Rust.Cast (Rust.Borrow (isMutable expr') (result expr')) (toRustType ty')
            }
```

C's indirection or dereferencing operator (unary prefix `*`) translates
to the same operator in Rust. Whether the result is an l-value depends
on whether the pointer was to a mutable value.

```haskell
    CIndOp -> do
        expr' <- interpretExpr True expr
        case resultType expr' of
            IsPtr mut' ty' -> return Result
                { resultType = ty'
                , isMutable = mut'
                , result = Rust.Deref (result expr')
                }
            _ -> badSource node "dereference of non-pointer"
```

Ah, unary plus. My favorite. Rust does not have a unary plus operator,
because this operator is almost entirely useless. It's the arithmetic
opposite of unary minus: where that operator negates its argument, this
operator returns its argument unchanged. ...except that the "integer
promotion" rules apply, so this operator may perform an implicit cast.

Translating `+(c ? t : f);` is a particularly tricky corner case. The
result is not demanded, and the unary plus operator doesn't generate
any code, so the ternary conditional translates to an `if` expression in
statement position, which means that its type is required to be `()`.
(See the description for ternary conditional expressions, above.)

This implementation handles that case by forwarding the value of
`demand` to the recursive call that translates the ternary conditional.
That call yields a `resultType` of `IsVoid` in response. `intPromote` is
not actually supposed to be used on the `void` type, but since it
doesn't know what to do with it it returns it unchanged, which makes
`castTo` a no-op. End result: this corner case is translated exactly as
if there had been no unary plus operator in the expression at all.

```haskell
    CPlusOp -> do
        expr' <- interpretExpr demand expr
        let ty' = intPromote (resultType expr')
        return Result
            { resultType = ty'
            , isMutable = Rust.Immutable
            , result = castTo ty' expr'
            }
```

C's unary minus operator translates to Rust's unary minus operator,
after applying the integer promotions... except that if it's negating an
unsigned type, then C defines integer overflow to wrap.

```haskell
    CMinOp -> fmap wrapping $ simple Rust.Neg
```

Bitwise complement translates to Rust's `!` operator.

```haskell
    CCompOp -> simple Rust.Not
```

Logical "not" also translates to Rust's `!` operator, but we have to
force the operand to `bool` type first.

```haskell
    CNegOp -> do
        expr' <- interpretExpr True expr
        return Result
            { resultType = IsBool
            , isMutable = Rust.Immutable
            , result = Rust.Not (toBool expr')
            }
```

Common helpers for the unary operators:

```haskell
    where
    incdec returnOld assignop = do
        expr' <- interpretExpr True expr
        compound node returnOld demand assignop expr' Result
            { resultType = IsInt Signed (BitWidth 32)
            , isMutable = Rust.Immutable
            , result = 1
            }
    simple f = do
        expr' <- interpretExpr True expr
        let ty' = intPromote (resultType expr')
        return Result
            { resultType = ty'
            , isMutable = Rust.Immutable
            , result = f (castTo ty' expr')
            }
```

C's `sizeof` and `alignof` operators translate to calls to Rust's
`size_of` and `align_of` functions in `std::mem`, respectively.

> **TODO**: Translate `sizeof`/`alignof` when applied to expressions,
> not just types. Just need to check first whether side effects in the
> expressions are supposed to be evaluated or not.

```haskell
interpretExpr _ (CSizeofType decl _) = do
    ty <- typeName decl
    let Rust.TypeName ty' = toRustType ty
    return Result
        { resultType = IsInt Unsigned WordWidth
        , isMutable = Rust.Immutable
        , result = Rust.Call (Rust.Var (Rust.VarName ("std::mem::size_of::<" ++ ty' ++ ">"))) []
        }
interpretExpr _ (CAlignofType decl _) = do
    ty <- typeName decl
    let Rust.TypeName ty' = toRustType ty
    return Result
        { resultType = IsInt Unsigned WordWidth
        , isMutable = Rust.Immutable
        , result = Rust.Call (Rust.Var (Rust.VarName ("std::mem::align_of::<" ++ ty' ++ ">"))) []
        }
```

Function calls first translate the expression which identifies which
function to call, and any argument expressions.

```haskell
interpretExpr _ expr@(CCall func args _) = do
    func' <- interpretExpr True func
    case resultType func' of
        IsFunc retTy argTys variadic -> do
            args' <- castArgs variadic argTys args
            return Result
                { resultType = retTy
                , isMutable = Rust.Immutable
                , result = Rust.Call (result func') args'
                }
        _ -> badSource expr "function call to non-function"
    where
```

For each actual parameter, the expression given for that parameter is
translated and then cast (if necessary) to the type of the corresponding
formal parameter.

If we're calling a variadic function, then there can be any number of
arguments after the ones explicitly given in the function's type, and
those extra arguments can be of any type.

Otherwise, there must be exactly as many arguments as the function's
type specified, or it's a syntax error.

```haskell
    castArgs _ [] [] = return []
    castArgs variadic (ty : tys) (arg : rest) = do
        arg' <- interpretExpr True arg
        args' <- castArgs variadic tys rest
        return (castTo ty arg' : args')
    castArgs True [] rest = mapM (fmap result . interpretExpr True) rest
    castArgs False [] _ = badSource expr "arguments (too many)"
    castArgs _ _ [] = badSource expr "arguments (too few)"
```

Structure member access has two forms in C (`.` and `->`), which only
differ in whether the left-hand side is dereferenced first. We desugar
`p->f` into `(*p).f`, then translate `o.f` into the same thing in Rust.
The result's type is the type of the named field within the struct, and
the result is a legal l-value if and only if the larger object was a
legal l-value.

```haskell
interpretExpr _ expr@(CMember obj ident deref node) = do
    obj' <- interpretExpr True $ if deref then CUnary CIndOp obj node else obj
    fields <- case resultType obj' of
        IsStruct _ fields -> return fields
        _ -> badSource expr "member access of non-struct"
    let field = identToString ident
    ty <- case lookup field fields of
        Just ty -> return ty
        Nothing -> badSource expr "request for non-existent field"
    return Result
        { resultType = ty
        , isMutable = isMutable obj'
        , result = Rust.Member (result obj') (Rust.VarName field)
        }
```

We preserve variable names during translation, so a C variable reference
translates to an identical Rust variable reference. However, we do have
to look up the variable in the environment in order to report its type
and whether taking its address should produce a mutable or immutable
pointer.

```haskell
interpretExpr _ expr@(CVar ident _) = do
    sym <- getIdent (SymbolIdent ident)
    case sym of
        Just (mut, ty) -> return Result
            { resultType = ty
            , isMutable = mut
            , result = Rust.Var (Rust.VarName (identToString ident))
            }
        Nothing -> badSource expr "undefined variable"
```

C literals (integer, floating-point, character, and string) translate to
similar tokens in Rust.

> **TODO**: If the integer literal was written in hex or octal, emit a
> hex or octal literal in the generated Rust.

> **TODO**: Figure out what to do about floating-point hex literals,
> which as far as I can tell Rust doesn't support (yet?).

> **TODO**: Translate wide character and string literals.

```haskell
interpretExpr _ expr@(CConst c) = case c of
    CIntConst (CInteger v _repr flags) _ ->
        let s = if testFlag FlagUnsigned flags then Unsigned else Signed
            w = if testFlag FlagLongLong flags || testFlag FlagLong flags
                then WordWidth
                else BitWidth 32
        in return (literalNumber (IsInt s w) (show v))
    CFloatConst (CFloat str) _ -> case span (`notElem` "fF") str of
        (v, "") -> return (literalNumber (IsFloat 64) v)
        (v, [_]) -> return (literalNumber (IsFloat 32) v)
        _ -> badSource expr "float"
```

Rust's `char` type is for Unicode characters, so it's quite different
from C's 8-bit `char` type. As a result, C character literals and
strings need to be translated to Rust's "byte literals" (`b'?'`,
`b"..."`) rather than the more familiar character and string literal
syntax.

```haskell
    CCharConst (CChar ch False) _ -> return Result
        { resultType = charType
        , isMutable = Rust.Immutable
        , result = Rust.Lit (Rust.LitRep ("b'" ++ rustByteLit ch ++ "'"))
        }
```

In C, string literals get a terminating NUL character added at the end.
Rust byte string literals do not, so we need to append one in the
translation.

In Rust, the type of a byte string literal of length `n` is `&'static
[u8; n]`. We need a raw pointer instead to match C's semantics.
Conveniently, Rust slices have an `.as_ptr()` method which extracts a
raw pointer for us. Note that since string literals have `'static`
lifetime, the resulting raw pointer is always safe to use.

```haskell
    CStrConst (CString str False) _ -> return Result
        { resultType = IsPtr Rust.Immutable charType
        , isMutable = Rust.Immutable
        , result = Rust.MethodCall (Rust.Lit (
                Rust.LitRep ("b\"" ++ concatMap rustByteLit str ++ "\\0\"")
            )) (Rust.VarName "as_ptr") []
        }
    _ -> unimplemented expr
    where
```

A number like `42` gives no information about which type it should be.
In Rust, we can suffix a numeric literal with its type name, so `42i8`
has type `i8`, while `42f32` has type `f32`. `literalNumber` abuses the
fact that our Rust AST representation of a type is just a string to get
the right suffix for these literals.

Rust allows unsuffixed numeric literals, in which case it will try to
infer from the surrounding context what type the number should have.
However, we don't want to rely on Rust's inference rules here because we
need to match C's rules instead.

```haskell
    literalNumber ty v =
        let Rust.TypeName suffix = toRustType ty
        in Result
            { resultType = ty
            , isMutable = Rust.Immutable
            , result = Rust.Lit (Rust.LitRep (v ++ suffix))
            }
```

Rust character and string literals have only a few special escape
sequences, so we can't reuse any functions for escaping Haskell or C
strings.

```haskell
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
```

GCC's "statement expression" extension translates pretty directly to
Rust block expressions.

```haskell
interpretExpr demand (CStatExpr (CCompound [] stmts _) _) = scope $ do
    let (effects, final) = case last stmts of
            CBlockStmt (CExpr expr _) | demand -> (init stmts, expr)
            _ -> (stmts, Nothing)
    effects' <- mapM interpretBlockItem effects
    final' <- mapM (interpretExpr True) final
    return Result
        { resultType = maybe IsVoid resultType final'
        , isMutable = maybe Rust.Immutable isMutable final'
        , result = Rust.BlockExpr (Rust.Block (concat effects') (fmap result final'))
        }
```

Otherwise, we have not yet implemented this kind of expression.

```haskell
interpretExpr _ expr = unimplemented expr
```

> **TODO**: Document these expression helper functions.

```haskell
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

binop :: CExpr -> CBinaryOp -> Result -> Result -> EnvMonad Result
binop expr op lhs rhs = fmap wrapping $ case op of
    CMulOp -> promote expr Rust.Mul lhs rhs
    CDivOp -> promote expr Rust.Div lhs rhs
    CRmdOp -> promote expr Rust.Mod lhs rhs
    CAddOp -> case (resultType lhs, resultType rhs) of
        (IsPtr _ _, _) -> return lhs { result = Rust.MethodCall (result lhs) (Rust.VarName "offset") [castTo (IsInt Signed WordWidth) rhs] }
        (_, IsPtr _ _) -> return rhs { result = Rust.MethodCall (result rhs) (Rust.VarName "offset") [castTo (IsInt Signed WordWidth) lhs] }
        _ -> promote expr Rust.Add lhs rhs
    CSubOp -> case (resultType lhs, resultType rhs) of
        (IsPtr _ _, IsPtr _ _) -> unimplemented expr
        (IsPtr _ _, _) -> return lhs { result = Rust.MethodCall (result lhs) (Rust.VarName "offset") [Rust.Neg (castTo (IsInt Signed WordWidth) rhs)] }
        _ -> promote expr Rust.Sub lhs rhs
    CShlOp -> promote expr Rust.ShiftL lhs rhs
    CShrOp -> promote expr Rust.ShiftR lhs rhs
    CLeOp -> comparison Rust.CmpLT
    CGrOp -> comparison Rust.CmpGT
    CLeqOp -> comparison Rust.CmpLE
    CGeqOp -> comparison Rust.CmpGE
    CEqOp -> comparison Rust.CmpEQ
    CNeqOp -> comparison Rust.CmpNE
    CAndOp -> promote expr Rust.And lhs rhs
    CXorOp -> promote expr Rust.Xor lhs rhs
    COrOp -> promote expr Rust.Or lhs rhs
    CLndOp -> return Result { resultType = IsBool, isMutable = Rust.Immutable, result = Rust.LAnd (toBool lhs) (toBool rhs) }
    CLorOp -> return Result { resultType = IsBool, isMutable = Rust.Immutable, result = Rust.LOr (toBool lhs) (toBool rhs) }
    where
    comparison op' = case (resultType lhs, resultType rhs) of
        (IsPtr _ _, IsPtr _ _) -> return (promotePtr op' lhs rhs)
        _ -> do
            res <- promote expr op' lhs rhs
            return res { resultType = IsBool }

isSimple :: Rust.Expr -> Bool
isSimple (Rust.Var{}) = True
isSimple (Rust.Deref p) = isSimple p
isSimple _ = False

compound :: CExpr -> Bool -> Bool -> CAssignOp -> Result -> Result -> EnvMonad Result
compound expr returnOld demand op lhs rhs = do
    let op' = case op of
            CAssignOp -> Nothing
            CMulAssOp -> Just CMulOp
            CDivAssOp -> Just CDivOp
            CRmdAssOp -> Just CRmdOp
            CAddAssOp -> Just CAddOp
            CSubAssOp -> Just CSubOp
            CShlAssOp -> Just CShlOp
            CShrAssOp -> Just CShrOp
            CAndAssOp -> Just CAndOp
            CXorAssOp -> Just CXorOp
            COrAssOp  -> Just COrOp
        (bindings1, dereflhs, boundrhs) = if isSimple (result lhs)
            then ([], lhs, rhs)
            else
                let lhsvar = Rust.VarName "_lhs"
                    rhsvar = Rust.VarName "_rhs"
                in ([ Rust.Let Rust.Immutable rhsvar Nothing (Just (result rhs))
                    , Rust.Let Rust.Immutable lhsvar Nothing (Just (Rust.Borrow Rust.Mutable (result lhs)))
                    ], lhs { result = Rust.Deref (Rust.Var lhsvar) }, rhs { result = Rust.Var rhsvar })
        (bindings2, ret) = if not demand
            then ([], Nothing)
            else if not returnOld
            then ([], Just (result dereflhs))
            else
                let oldvar = Rust.VarName "_old"
                in ([Rust.Let Rust.Immutable oldvar Nothing (Just (result dereflhs))], Just (Rust.Var oldvar))
    assignment <- Rust.Assign (result dereflhs) (Rust.:=) <$> fmap (castTo (resultType lhs)) (
            case op' of
            Just o -> binop expr o dereflhs boundrhs
            Nothing -> return boundrhs
        )
    return $ case Rust.Block (bindings1 ++ bindings2 ++ [Rust.Stmt assignment]) ret of
        b@(Rust.Block body Nothing) -> Result
            { resultType = IsVoid
            , isMutable = Rust.Immutable
            , result = case body of
                [Rust.Stmt e] -> e
                _ -> Rust.BlockExpr b
            }
        b -> lhs { result = Rust.BlockExpr b }
```

Implicit type coercions
=======================

C implicitly performs a variety of type conversions. Rust has far fewer
cases where it will convert between types without you telling it to. So
we have to encode C's implicit coercions as explicit casts in Rust.

On the other hand, if it happens that a translated expression already
has the desired type, we don't want to emit a cast expression that will
just clutter up the generated source. So `castTo` is a smart constructor
that inserts a cast if and only if we need one.

```haskell
castTo :: CType -> Result -> Rust.Expr
castTo target source | resultType source == target = result source
castTo target source = Rust.Cast (result source) (toRustType target)
```

Similarly, when Rust requires an expression of type `bool`, or C
requires an expression to be interpreted as either "0" or "not 0"
representing "false" and "true", respectively, then we need to figure
out how to turn the arbitrary scalar expression we have into a `bool`.

```haskell
toBool :: Result -> Rust.Expr
toBool (Result { resultType = t, result = v }) = case t of
```

The expression may already have boolean type, in which case we can
return it unchanged.

```haskell
    IsBool -> v
```

Or it may be a pointer, in which case we need to generate a test for
whether it is not a null pointer.

```haskell
    IsPtr _ _ -> Rust.Not (Rust.MethodCall v (Rust.VarName "is_null") [])
```

Otherwise, it should be numeric and we just need to test that it is not
equal to 0.

```haskell
    _ -> Rust.CmpNE v 0
```

C defines a set of rules called the "integer promotions" (C99 section
6.3.1.1 paragraph 2). `intPromote` encodes those rules as a type-to-type
transformation. To convert an expression to its integer-promoted type,
use with `castTo`.

```haskell
intPromote :: CType -> CType
```

From the spec: "If an int can represent all values of the original type,
the value is converted to an int,"

Here we pretend that `int` is 32-bits wide. This assumption is true on
the major modern CPU architectures. Also, we're trying to create a
standard-conforming implementation of C, not clone the behavior of a
particular compiler, and the C standard allows us to define `int` to be
whatever size we like. That said, this assumption may break non-portable
C programs.

Conveniently, Rust allows `bool` expressions to be cast to any integer
type, and it converts `true` to 1 and `false` to 0 just like C requires,
so we don't need any special magic to handle booleans here.

```haskell
intPromote IsBool = IsInt Signed (BitWidth 32)
intPromote (IsInt _ (BitWidth w)) | w < 32 = IsInt Signed (BitWidth 32)
```

"otherwise, it is converted to an unsigned int. ... All other types are
unchanged by the integer promotions."

```haskell
intPromote x = x
```

C also defines a set of rules called the "usual arithmetic conversions"
(C99 section 6.3.1.8) to determine what type binary operators should be
evaluated at.

> **XXX**: I'm not sure this correctly implements the standard. It
> should get checked.

```haskell
usual :: CType -> CType -> Maybe CType
usual (IsFloat aw) (IsFloat bw) = Just (IsFloat (max aw bw))
usual a@(IsFloat _) _ = Just a
usual _ b@(IsFloat _) = Just b
usual a@(intPromote -> IsInt as aw) b@(intPromote -> IsInt bs bw)
    | a == b = Just a
    | as == bs = Just (IsInt as (max aw bw))
    | as == Unsigned = Just (if aw >= bw then a else b)
    | otherwise      = Just (if bw >= aw then b else a)
usual _ _ = Nothing
```

Here's a helper function to apply the usual arithmetic conversions to
both operands of a binary operator, cast as needed, and then combine the
operands using an arbitrary Rust binary operator.

```haskell
promote
    :: (Pretty node, Pos node)
    => node
    -> (Rust.Expr -> Rust.Expr -> Rust.Expr)
    -> Result -> Result -> EnvMonad Result
promote node op a b = case usual (resultType a) (resultType b) of
    Just rt -> return Result
        { resultType = rt
        , isMutable = Rust.Immutable
        , result = op (castTo rt a) (castTo rt b)
        }
    Nothing -> badSource node $ concat
        [ "arithmetic combination for "
        , show (resultType a)
        , " and "
        , show (resultType b)
        ]
```

`compatiblePtr` implements the equivalent of the "usual arithmetic
conversions" but for pointer types.

> **FIXME**: Citation to C99 needed.

```haskell
compatiblePtr :: CType -> CType -> CType
compatiblePtr (IsPtr _ IsVoid) b = b
compatiblePtr a (IsPtr _ IsVoid) = a
compatiblePtr (IsPtr m1 a) (IsPtr m2 b) = IsPtr (leastMutable m1 m2) (compatiblePtr a b)
    where
    leastMutable Rust.Mutable Rust.Mutable = Rust.Mutable
    leastMutable _ _ = Rust.Immutable
compatiblePtr a b | a == b = a
```

If we got here, the pointer types are not compatible, which as far as I
can tell is not allowed by C99. But GCC only treats it as a warning, so
we cast both sides to a void pointer, which should work on the usual
architectures.

```haskell
compatiblePtr _ _ = IsVoid
```

Finally, `promotePtr` is like `promote` but for pointer types instead of
arithmetic types. This function is only used for boolean-valued
operators such as `==` or `<`, so it's specialized to mark the result
type as boolean for convenience.

```haskell
promotePtr :: (Rust.Expr -> Rust.Expr -> Rust.Expr) -> Result -> Result -> Result
promotePtr op a b = Result
    { resultType = IsBool
    , isMutable = Rust.Immutable
    , result =
        let ty = compatiblePtr (resultType a) (resultType b)
        in op (castTo ty a) (castTo ty b)
    }
```


Internal representation of C types
==================================

> **TODO**: Document the type representation we use here.

```haskell
data Signed = Signed | Unsigned
    deriving (Show, Eq)

data IntWidth = BitWidth Int | WordWidth
    deriving (Show, Eq, Ord)

data CType
    = IsBool
    | IsInt Signed IntWidth
    | IsFloat Int
    | IsVoid
    | IsFunc CType [CType] Bool
    | IsPtr Rust.Mutable CType
    | IsStruct String [(String, CType)]
    deriving (Show, Eq)

toRustType :: CType -> Rust.Type
toRustType IsBool = Rust.TypeName "bool"
toRustType (IsInt s w) = Rust.TypeName ((case s of Signed -> 'i'; Unsigned -> 'u') : (case w of BitWidth b -> show b; WordWidth -> "size"))
toRustType (IsFloat w) = Rust.TypeName ('f' : show w)
toRustType IsVoid = Rust.TypeName "()"
toRustType (IsFunc retTy args variadic) = Rust.TypeName $ concat
    [ "unsafe extern fn("
    , args'
    , ")"
    , if retTy /= IsVoid then " -> " ++ typename retTy else ""
    ]
    where
    typename (toRustType -> Rust.TypeName t) = t
    args' = intercalate ", " (
            map typename args ++ if variadic then ["..."] else []
        )
toRustType (IsPtr mut to) = let Rust.TypeName to' = toRustType to in Rust.TypeName (rustMut mut ++ to')
    where
    rustMut Rust.Mutable = "*mut "
    rustMut Rust.Immutable = "*const "
toRustType (IsStruct name _fields) = Rust.TypeName name
```

C leaves it up to the implementation to decide whether the base `char`
type is signed or unsigned. We choose unsigned, because that's the type
of Rust's byte literals.

```haskell
charType :: CType
charType = IsInt Unsigned (BitWidth 8)

baseTypeOf :: [CDeclSpec] -> EnvMonad (Maybe CStorageSpec, (Rust.Mutable, CType))
baseTypeOf specs = do
    -- TODO: process attributes and the `inline` keyword
    let (storage, _attributes, basequals, basespecs, _inline) = partitionDeclSpecs specs
    mstorage <- case storage of
        [] -> return Nothing
        [spec] -> return (Just spec)
        _ : excess : _ -> badSource excess "extra storage class specifier"
    base <- foldrM go (mutable basequals, IsInt Signed (BitWidth 32)) basespecs
    return (mstorage, base)
    where
    go (CSignedType _) (mut, IsInt _ width) = return (mut, IsInt Signed width)
    go (CUnsigType _) (mut, IsInt _ width) = return (mut, IsInt Unsigned width)
    go (CCharType _) (mut, _) = return (mut, charType)
    go (CShortType _) (mut, IsInt s _) = return (mut, IsInt s (BitWidth 16))
    go (CIntType _) (mut, IsInt s _) = return (mut, IsInt s (BitWidth 32))
    go (CLongType _) (mut, IsInt s _) = return (mut, IsInt s WordWidth)
    go (CLongType _) (mut, IsFloat w) = return (mut, IsFloat w)
    go (CFloatType _) (mut, _) = return (mut, IsFloat 32)
    go (CDoubleType _) (mut, _) = return (mut, IsFloat 64)
    go (CVoidType _) (mut, _) = return (mut, IsVoid)
    go (CBoolType _) (mut, _) = return (mut, IsBool)
    go (CSUType (CStruct CStructTag (Just ident) Nothing _ _) _) (mut, _) = do
        mty <- getIdent (StructIdent ident)
        return $ (,) mut $ case mty of
            Just (_, ty) -> ty
            -- FIXME: treating incomplete types as having no fields, but that's probably wrong
            Nothing -> IsStruct (identToString ident) []
    go (CSUType (CStruct CStructTag mident (Just declarations) _ _) _) (mut, _) = do
        fields <- fmap concat $ forM declarations $ \ declaration@(CDecl spec decls _) -> do
            (storage, base) <- baseTypeOf spec
            case storage of
                Just s -> badSource s "storage class specifier in struct"
                Nothing -> return ()
            forM decls $ \ decl -> case decl of
                (Just declr@(CDeclr (Just field) _ _ _ _), Nothing, Nothing) -> do
                    (_mut, ty) <- derivedTypeOf base declr
                    return (identToString field, ty)
                (_, Nothing, Just _size) -> unimplemented declaration
                _ -> badSource declaration "field in struct"
        name <- case mident of
            Just ident -> do
                let name = identToString ident
                addIdent (StructIdent ident) (Rust.Immutable, IsStruct name fields)
                return name
            Nothing -> uniqueName "Struct"
        emitItems [Rust.Item Rust.Public (Rust.Struct name [ (field, toRustType fieldTy) | (field, fieldTy) <- fields ])]
        return (mut, IsStruct name fields)
    go spec@(CTypeDef ident _) (mut1, _) = do
        mty <- getIdent (TypedefIdent ident)
        case mty of
            Just (mut2, ty) -> return (if mut1 == mut2 then mut1 else Rust.Immutable, ty)
            Nothing -> badSource spec "undefined type"
    go spec _ = unimplemented spec

derivedTypeOf :: (Rust.Mutable, CType) -> CDeclr -> EnvMonad (Rust.Mutable, CType)
derivedTypeOf base declr@(CDeclr _ derived _ _ _) = foldrM derive base derived
    where
    derive (CFunDeclr args _ _) (c, retTy) = do
        (args', variadic) <- functionArgs declr args
        return (c, IsFunc retTy (map snd args') variadic)
    derive (CPtrDeclr quals _) (c, to) = return (mutable quals, IsPtr c to)
    derive (CArrDeclr quals _ _) (c, to) = return (mutable quals, IsPtr c to)

mutable :: [CTypeQualifier a] -> Rust.Mutable
mutable quals = if any (\ q -> case q of CConstQual _ -> True; _ -> False) quals then Rust.Immutable else Rust.Mutable

typeName :: CDecl -> EnvMonad CType
typeName decl@(CDecl spec declarators _) = do
    (storage, base) <- baseTypeOf spec
    case storage of
        Just s -> badSource s "storage class specifier in type name"
        Nothing -> return ()
    -- Declaration mutability has no effect in type names.
    (_mut, ty) <- case declarators of
        [] -> return base
        [(Just declr@(CDeclr Nothing _ _ _ _), Nothing, Nothing)] ->
            derivedTypeOf base declr
        _ -> badSource decl "type name"
    return ty
```
