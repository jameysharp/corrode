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
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS.Strict
import Data.Char
import Data.Foldable
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe
import Data.Monoid
import Data.List
import qualified Data.Set as Set
import Language.C
import Language.C.Data.Ident
import qualified Language.Rust.AST as Rust
import Numeric
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
    = SymbolIdent { identOfKind :: Ident }
    | TypedefIdent { identOfKind :: Ident }
    | StructIdent { identOfKind :: Ident }
    | EnumIdent { identOfKind :: Ident }
    deriving Eq
```

Sometimes we need to construct a unique name, because the Rust pattern
we want to generate requires a name someplace where C did not require
one. We'll follow a standard pattern for this and just generate a unique
number each time we need a new name.

Then, we can package together all of the state we'd like to thread around
our program while translating.

```haskell
data EnvState = EnvState
    { environment :: Environment
    , unique :: Int
    }
```

As we proceed through the C source, we'll accumulate Rust definitions
that we want to include in the final output. This type simply holds any
data that we want to have bubble up from further down the parse tree.
For example, a `struct` might be defined inside a declaration that's
inside a loop that's inside a function. We need to get that struct out
to its own item in Rust.

Similarly, when inside of a loop, we'd like to keep track of whether a
break or continue statement was used so we can avoid generating
unnecessary code to deal with edge cases&mdash;see the case of
`interpretStatement (CFor ..)`.

```haskell
data Output = Output
    { outputItems :: [Rust.Item]
    , outputExterns :: [(Rust.ExternItem, CType)]
    , outputIncomplete :: Set.Set String
    , usesSymbols :: Set.Set String
    , usesTypes :: Set.Set String
    , usesBreak :: Any
    , usesContinue :: Any
    }
```

As we generate output from translating each piece of C syntax, we need a
way to combine the output from different pieces. There's a standard
Haskell typeclass (which is like a Rust trait) called
[`Monoid`](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html)
which encapsulates this idea of combining pieces of output.

```haskell
instance Monoid Output where
```

For our output to be a monoid, it needs to specify

- what empty output looks like (which is just output where every field
  is empty),

    ```haskell
        mempty = Output
            { outputItems = mempty
            , outputExterns = mempty
            , outputIncomplete = mempty
            , usesSymbols = mempty
            , usesTypes = mempty
            , usesBreak = mempty
            , usesContinue = mempty
            }
    ```

- and how to combine two different pieces of output (which we do by
  pairwise combining each field).

    ```haskell
        mappend a b = Output
            { outputItems = outputItems a `mappend` outputItems b
            , outputExterns = outputExterns a `mappend` outputExterns b
            , outputIncomplete = outputIncomplete a `mappend` outputIncomplete b
            , usesSymbols = usesSymbols a `mappend` usesSymbols b
            , usesTypes = usesTypes a `mappend` usesTypes b
            , usesBreak = usesBreak a `mappend` usesBreak b
            , usesContinue = usesContinue a `mappend` usesContinue b
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
type EnvMonad = ExceptT String (RWS ControlFlow Output EnvState)
```

In fact, we're going to wrap up the monad operations in some helper
functions, and then only use these helpers everywhere else.

Some names are special in C or special in Rust, or both. We rename those
as we encounter them. At the moment, only `main` gets this special
treatment.

```haskell
applyRenames :: IdentKind -> String
applyRenames (SymbolIdent (identToString -> "main")) = "_c_main"
applyRenames ident = identToString (identOfKind ident)
```

`getIdent` looks up a name from the given namespace in the environment,
and returns the type information we have for it, or `Nothing` if we
haven't seen a declaration for that name yet.

```haskell
getIdent :: IdentKind -> EnvMonad (String, Maybe (Rust.Mutable, CType))
getIdent ident = lift $ do
    env <- gets environment
    let name = applyRenames ident
    return $ case lookup ident env of
        Just ty -> (name, Just ty)
        Nothing -> fromMaybe (name, Nothing) $ case ident of
            SymbolIdent ident' -> lookup (identToString ident') builtinSymbols
            _ -> Nothing
    where
    builtinSymbols =
        [ ("__builtin_bswap" ++ show w,
            ("u" ++ show w ++ "::swap_bytes",
                Just (Rust.Immutable,
                    IsFunc (IsInt Unsigned (BitWidth w))
                        [(Nothing, IsInt Unsigned (BitWidth w))] False
            )))
        | w <- [16, 32, 64]
        ]
```

`addIdent` saves type information into the environment.

```haskell
addIdent :: IdentKind -> (Rust.Mutable, CType) -> EnvMonad String
addIdent ident ty = lift $ do
    modify $ \ st -> st { environment = (ident, ty) : environment st }
    return (applyRenames ident)
```

`uniqueName` generates a new name with the given base and a new unique
number:

```haskell
uniqueName :: String -> EnvMonad String
uniqueName base = lift $ do
    st <- get
    put (st { unique = unique st + 1 })
    return (base ++ show (unique st))
```

`emitItems` adds a list of Rust items to the output.

```haskell
emitItems :: [Rust.Item] -> EnvMonad ()
emitItems items = lift $ tell mempty { outputItems = items }
```

```haskell
useType :: CType -> EnvMonad ()
useType ty = lift $ tell mempty { usesTypes = declaredNames ty }
```

`addExternIdent` saves type information into the environment like
`addIdent`, unless the ident is already there, in which case it verifies
that the types are the same.

It also adds to the output a list of functions or global variables which
_may_ be declared in some other translation unit. (We can't tell when we
see a C extern declaration whether it's just the prototype for a
definition that we'll find later in the current translation unit, so
there's a de-duplication pass at the end of `interpretTranslationUnit`.)

```haskell
addExternIdent
    :: (Pretty node, Pos node)
    => node
    -> IdentKind
    -> (Rust.Mutable, CType)
    -> (String -> Rust.ExternItem)
    -> EnvMonad ()
addExternIdent node ident ty mkItem = do
    (_, mty) <- getIdent ident
    case mty of
        Just oldTy -> when (ty /= oldTy) $ badSource node
            ("redefinition, previously defined as " ++ show oldTy)
        Nothing -> do
            name <- addIdent ident ty
            lift $ tell mempty { outputExterns = [(mkItem name, snd ty)] }
```

`emitIncomplete` records that we saw an incomplete type. For our
purposes, an incomplete type is anything with a definition we can't
translate, but we can still allow pointers to values of this type as
long as nobody tries dereferencing those pointers.

```haskell
emitIncomplete :: Ident -> EnvMonad CType
emitIncomplete ident = do
    lift $ tell mempty { outputIncomplete = Set.singleton (identToString ident) }
    return (IsIncomplete ident)
```

`recordBreak`/`recordContinue` take note of the presence of a `break`/
`continue`:

```haskell
recordBreak :: EnvMonad ()
recordBreak = lift $ tell mempty { usesBreak = Any True }

recordContinue :: EnvMonad ()
recordContinue = lift $ tell mempty { usesContinue = Any True }
```


Reporting errors
================

There will always be C source code that language-c parses happily but
Corrode can't translate to Rust, and we should report as much helpful
explanation as possible when that happens.

```haskell
noTranslation :: (Pretty node, Pos node) => node -> String -> EnvMonad a
noTranslation node msg = throwE $ concat
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
interpretTranslationUnit :: CTranslUnit -> Either String [Rust.Item]
interpretTranslationUnit (CTranslUnit decls _) = case err of
    Left msg -> Left msg
    Right _ -> Right items'
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
    (err, _, output) = runRWS (runExceptT (mapM_ perDecl decls)) initFlow initState
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

Incomplete types (see `emitIncomplete` above) may be referenced early
and then completed later. In that case we need to only emit the complete
definition.

If they are never completed, however, then we need to emit some Rust
type that can only be passed around by reference. We can't allow the
Rust compiler to construct, copy, or consume values of the incomplete
type, because we don't know how big it is. We also want each incomplete
type to be distinct from all other incomplete types.

We meet those requirements by, for each incomplete type, creating a
private `enum` type. We don't give the type any constructors, so new
values can't be constructed and it can't be `match`ed on. Unlike the
translation of other types, we don't declare this enum's `repr`, and we
don't derive `Copy` or `Clone` for it.

```haskell
    completeTypes = Set.fromList $ catMaybes
        [ case item of
            Rust.Item _ _ (Rust.Struct name _) -> Just name
            _ -> Nothing
        | item <- outputItems output
        ]
    incompleteTypes = outputIncomplete output `Set.difference` completeTypes
    incompleteItems =
        [ Rust.Item [] Rust.Private (Rust.Enum name [])
        | name <- Set.toList incompleteTypes
        ]
```

Next we remove any locally-defined names from the list of external
declarations. We can't tell whether something is actually external when
we encounter its declaration, but once we've collected all the symbols
for this translation unit it becomes clear.

```haskell
    itemNames = catMaybes
        [ case item of
            Rust.Item _ _ (Rust.Function _ name _ _ _) -> Just name
            Rust.Item _ _ (Rust.Static _ (Rust.VarName name) _ _) -> Just name
            _ -> Nothing
        | item <- outputItems output
        ]

    externName (Rust.ExternFn name _ _ _) = name
    externName (Rust.ExternStatic _ (Rust.VarName name) _) = name
    keepExtern name = name `Set.member` usesSymbols output && name `notElem` itemNames
    externs = filter (keepExtern . externName . fst) (outputExterns output)
    (externs', externTypes) = unzip externs
```

If a type declaration isn't actually used by any of the other
declarations that we're keeping, then drop it. C headers declare lots of
types, and most of them don't get used in any given source file.

This is not just a nice cleanup of the output. It also allows us to
translate headers containing types we can't yet translate, as long as
those types aren't actually used.

```haskell
    neededTypes = Set.unions (usesTypes output : map declaredNames externTypes)
    keepItem (Rust.Item _ _ (Rust.Struct name _)) = name `Set.member` neededTypes
    keepItem (Rust.Item _ _ (Rust.Enum name _)) = name `Set.member` neededTypes
    keepItem _ = True

    items = filter keepItem (incompleteItems ++ outputItems output)
```

If there are any external declarations after filtering, then we need to
wrap them in an `extern { }` block. We place that before the other
items, by convention.

```haskell
    items' = if null externs'
        then items
        else Rust.Item [] Rust.Private (Rust.Extern externs') : items
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
type MakeBinding a = (Rust.ItemKind -> a, Rust.Mutable -> Rust.Var -> Rust.Type -> Maybe Rust.Expr -> a)
```

It's up to the caller to provide an appropriate implementation of
`makeBinding`, but there are only two sensible choices, which we'll
define here for convenient use elsewhere.

> **FIXME**: Construct a correct default value for non-scalar static
> variables.

```haskell
makeStaticBinding :: MakeBinding Rust.Item
makeStaticBinding = (Rust.Item [] Rust.Private, makeBinding)
    where
    makeBinding mut var ty mexpr = Rust.Item attrs Rust.Public
        (Rust.Static mut var ty (fromMaybe 0 mexpr))
    attrs = [Rust.Attribute "no_mangle"]

makeLetBinding :: MakeBinding Rust.Stmt
makeLetBinding = (Rust.StmtItem [], makeBinding)
    where
    makeBinding mut var ty mexpr = Rust.Let mut var (Just ty) mexpr
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
interpretDeclarations (fromItem, makeBinding) declaration@(CDecl specs decls _) = do
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
    mbinds <- forM decls $ \ declarator -> do
```

This function is only used for what `language-c` calls "toplevel
declarations", and as such, "the elements of the non-empty
`init-declarator-list` are of the form `(Just declr, init?, Nothing)`.
The declarator `declr` has to be present and non-abstract and the
initialization expression is optional."

```haskell
        (decl, minit) <- case declarator of
            (Just decl, minit, Nothing) -> return (decl, minit)
            (Nothing, _, _) -> badSource declaration "absent declarator"
            (_, _, Just _) -> badSource declaration "bitfield declarator"

        ident <- case decl of
            CDeclr (Just ident) _ _ _ _ -> return ident
            _ -> badSource decl "abstract declarator"

        (mut, isFunc, ty) <- derivedTypeOf baseTy decl
        case (storagespecs, isFunc, ty) of
```

Each `typedef` declarator is added to the environment, tagged as a
`TypedefIdent`. They must not have an initializer and do not return any
declarations, so the only effect of a `typedef` is to update the
environment.

> **TODO**: It would be nice to emit a type-alias item for each
> `typedef` and use the alias names anywhere we can, instead of
> replacing the aliases with the underlying type everywhere. That way we
> preserve more of the structure of the input program. But it isn't
> always possible, so this requires careful thought.

```haskell
            (Just (CTypedef _), _, _) -> do
                when isFunc (unimplemented decl)
                when (isJust minit) (badSource decl "initializer on typedef")
                _ <- addIdent (TypedefIdent ident) (mut, ty)
                return Nothing
```

Non-`typedef` declarations may have an initializer. Each declarator is
added to the environment, tagged as a `SymbolIdent`.

Static function prototypes don't need to be translated because the
function definition must be in the same translation unit. We still need
to have the function's type signature in the environment though.

```haskell
            (Just (CStatic _), True, IsFunc{}) -> do
                _ <- addIdent (SymbolIdent ident) (mut, ty)
                return Nothing
```

Other function prototypes need to be translated unless the function
definition appears in the same translation unit; do it and prune
duplicates later.

```haskell
            (_, True, IsFunc retTy args variadic) -> do
                let formals =
                        [ (Rust.VarName argName, toRustType argTy)
                        | (idx, (mname, argTy)) <- zip [1 :: Int ..] args
                        , let argName = maybe ("arg" ++ show idx) (identToString . snd) mname
                        ]
                addExternIdent decl (SymbolIdent ident) (mut, ty) $ \ name ->
                    Rust.ExternFn name formals variadic (toRustRetType retTy)
                return Nothing
```

Non-function externs need to be translated unless an identical
non-extern declaration appears in the same translation unit; do it and
prune duplicates later.

```haskell
            (Just (CExtern _), _, _) -> do
                addExternIdent decl (SymbolIdent ident) (mut, ty) $ \ name ->
                    Rust.ExternStatic mut (Rust.VarName name) (toRustType ty)
                return Nothing
```

Declarations with storage class `static` always need to construct Rust
static items. These items always have an initializer, even if it's just
the zero-equivalent initializer. We use the caller's `fromItem` callback
to turn the item (actually an `ItemKind`) into the same type that we're
returning for other bindings.

```haskell
            (Just (CStatic _), _, _) -> do
                name <- addIdent (SymbolIdent ident) (mut, ty)
                useType ty
                expr <- interpretInitializer ty (fromMaybe (CInitList [] (nodeInfo decl)) minit)
                return (Just (fromItem
                    (Rust.Static mut (Rust.VarName name) (toRustType ty) expr)))
```

Anything else is a variable declaration to translate. This is the only
case where we use `makeBinding`. If there's an initializer, we also need
to translate that; see below.

```haskell
            _ -> do
                name <- addIdent (SymbolIdent ident) (mut, ty)
                useType ty
                mexpr <- mapM (interpretInitializer ty) minit
                return (Just (makeBinding mut (Rust.VarName name) (toRustType ty) mexpr))
```

Return the bindings produced for any declarator that did not return
`Nothing`.

```haskell
    return (catMaybes mbinds)
```


Initialization
==============

The general form of initialization, described in C99 section 6.7.8, involves
an initializer construct. The interface we want to expose for translating
C initializers is fairly simple: given the type of the thing we are trying
to initialize and the C initializer, produce a Rust expression that
corresponds to the C expression that would have been initialized:

```haskell
interpretInitializer :: CType -> CInit -> EnvMonad Rust.Expr
```

Unfortunately, we have to delay the actual implementation of this
function until the end of this section when we will have all the necessary
pieces.

The problem is that in C, there are just too many ways of expressing the
same initializations. Take, for example, the following struct definitions

```c
struct Foo { struct Bar b; int z; }
struct Bar { int x; int y; }
```

Then, the following are all equivalent

```c
struct Foo s = { 1, 2, 3 }
struct Foo s = { .b = { .x = 1, .y = 2 }, .z = 3 }
struct Foo s = { .b.y = 1, .b = { 1, 2 }, 3 }
struct Foo s = { (struct Bar) { 1, 2 }, 3 }
```

We need some canonical form for manipulating and composing initializer
expressions. Then, we can deal with C initialization expressions in
several steps: start by converting them to a canonical form, compose them
together accordingly, and finally convert them to Rust expressions.

Our canonical form may have a base expression, which (if we're
initializing an aggregate) may have some of its fields overridden. If a
base expression is present, it overrides all previous initializers for
this object. Otherwise, all fields not specified in the `IntMap` will
get initialized to their zero-equivalent values.

```haskell
data Initializer
    = Initializer (Maybe Rust.Expr) (IntMap.IntMap Initializer)
```

```haskell
scalar :: Rust.Expr -> Initializer
scalar expr = Initializer (Just expr) IntMap.empty
```

Notice that combining initializers is an associative binary operation.
This motivates us to use the `Monoid` typeclass again to represent the
operation for combining two initializers.

```haskell
instance Monoid Initializer where
```
- The identity element in this case will be the empty initializer. This is
  because whenever it is combined with another initializer (either from
  the left or the right), the result is just the other initializer.

    ```haskell
        mempty = Initializer Nothing IntMap.empty
    ```

- When combining two initializers, the one on the right overrides/shadows
  definitions made by the one on the left.

    ```haskell
        mappend _ b@(Initializer (Just _) _) = b
        mappend (Initializer m a) (Initializer Nothing b) =
            Initializer m (IntMap.unionWith mappend a b)
    ```

Now, we need to concern ourselves with constructing these initializers in
the first place. We will need to keep track of the current object (see
point 17 of section 6.7.8). A `Designator` describes a position inside a
type.

```haskell
type CurrentObject = Maybe Designator

data Designator
  = Base CType
```
* encodes the type of the base object pointed to

```haskell
  | From CType Int [CType] Designator
  deriving(Show)
```
* encodes the type of the object pointed to, its index in the parent,
  remaining fields in the parent, and the parent designator

In several places, we need to know the type of a designated object.

```haskell
designatorType :: Designator -> CType
designatorType (Base ty) = ty
designatorType (From ty _ _ _) = ty
```

Then, given a list of designators and the type we are currently in, we can
compute the most general possible current object.

```haskell
objectFromDesignators :: CType -> [CDesignator] -> EnvMonad CurrentObject
objectFromDesignators _ [] = pure Nothing
objectFromDesignators ty desigs = Just <$> go ty desigs (Base ty)
    where

    go :: CType -> [CDesignator] -> Designator -> EnvMonad Designator
    go _ [] obj = pure obj
    go (IsStruct name fields) (d@(CMemberDesig ident _) : ds) obj = do
        case span (\ (field, _) -> identToString ident /= field) fields of
            (_, []) -> badSource d ("designator for field not in struct " ++ name)
            (earlier, (_, ty') : rest) ->
                go ty' ds (From ty' (length earlier) (map snd rest) obj)
    go ty' (d : _) _ = badSource d ("designator for " ++ show ty')
```

However, since it is possible for some entries in an initializer to have
no designators (in which case the initializer implicitly applies to the
next object), we need a way to calculate the most general next object from
the current one (provided we haven't reached the end of the thing we are
initializing).

```haskell
nextObject :: Designator -> CurrentObject
nextObject Base{} = Nothing
nextObject (From _ i (ty : remaining) base) = Just (From ty (i+1) remaining base)
nextObject (From _ _ [] base) = nextObject base
```

The type of an initializer expression is compatible with the type of the
object it's initializing if either:

- Both have structure type and they're the same `struct`,
- Or neither have structure type.

In the latter case we don't check what type they are, because we can
cast any scalar type to any other as needed.

```haskell
compatibleInitializer :: CType -> CType -> Bool
compatibleInitializer (IsStruct name1 _) (IsStruct name2 _) = name1 == name2
compatibleInitializer IsStruct{} _ = False
compatibleInitializer _ IsStruct{} = False
compatibleInitializer _ _ = True
```

We've used the expression "the most general (object)" several times.
This is because designators alone aren't actually enough to determine
exactly what gets initialized&mdash;we also need to compare types.

An initializer expression initializes the current object, if the two
have compatible types. Otherwise, we extend the designator to refer to
the first sub-object of the current object and check whether _that_
object is compatible with the initializer. We keep descending through
first sub-objects until we run out of sub-objects without finding any
compatible objects.

```haskell
nestedObject :: CType -> Designator -> Maybe Designator
nestedObject ty desig = case designatorType desig of
    ty' | ty `compatibleInitializer` ty' -> Just desig
    IsStruct _ ((_ , ty') : fields) ->
        nestedObject ty (From ty' 0 (map snd fields) desig)
    _ -> Nothing
```

Given these helpers, we are now in a position to translate C initializers
to our initializers.

When we have a list of expressions, we start by parsing all of the
designators into our internal representation.

```haskell
translateInitList :: CType -> CInitList -> EnvMonad Initializer
translateInitList ty list = do

    objectsAndInitializers <- forM list $ \ (desigs, initial) -> do
        currObj <- objectFromDesignators ty desigs
        pure (currObj, initial)
```

Next, we have to choose the starting current object (`base`). For aggregate
types, the first current object points to their first field but for scalar
types it points to the primitive itself. For example

```c
struct point { int x, y };

int i = { 1, 3 };
struct point p = { 1, 3 };
```

In the first example, the whole of `i` gets initialized to `1` (and `3` is
ignored) since `i` is not a struct. On the other, in the second example,
it is the fields of `p` that get initialized to `1` and `3` since `p` is a
struct.

```haskell
    let base = case ty of
                    IsStruct _ ((_,ty'):fields) -> From ty' 0 (map snd fields) (Base ty)
                    _ -> Base ty
```

Finally, we are ready to calculate the initializer for the whole list. We
walk through the list of designators and their initializers from left to
right passing along the current object as we go (in case the initializer
that follows has no designator).

When we get to the end, we throw away the final current object as
initializer lists never affect the current object of their enclosing
initializer.

```haskell
    (_, initializer) <- foldM resolveCurrentObject (Just base, mempty) objectsAndInitializers
    return initializer
```

Resolution takes a current object to use if no designator is specified. It
returns the new current object for the next element to use, and the above
`Initializer` type representing the part of the object that this element
initialized.

```haskell
resolveCurrentObject
    :: (CurrentObject, Initializer)
    -> (CurrentObject, CInit)
    -> EnvMonad (CurrentObject, Initializer)
resolveCurrentObject (obj0, prior) (obj1, cinitial) = case obj1 `mplus` obj0 of
    Nothing -> return (Nothing, prior)
    Just obj -> do
```

If the initializer provided is another initializer list, then the
initializer has to be for the current object. If it is just an
initializer expression, however, we translate the expression to find out
what type it has, and find the corresponding sub-object to initialize
using `nestedObject`.

```haskell
        (obj', initial) <- case cinitial of
            CInitList list' _ -> do
                initial <- translateInitList (designatorType obj) list'
                return (obj, initial)
            CInitExpr expr _ -> do
                expr' <- interpretExpr True expr
                case nestedObject (resultType expr') obj of
                    Nothing -> badSource cinitial "type in initializer"
                    Just obj' -> do
                        let s = castTo (designatorType obj') expr'
                        return (obj', scalar s)
```

Now that we've settled on the right current object and constructed an
intermediate `Initializer` for it, we need to wrap the latter in a
minimal aggregate initializer for each designator in the former.

```haskell
        let indices = unfoldr (\o -> case o of
                                 Base{} -> Nothing
                                 From _ j _ p -> Just (j,p)) obj'
        let initializer = foldl (\a j -> Initializer Nothing (IntMap.singleton j a)) initial indices

        return (nextObject obj', prior `mappend` initializer)
```

Finally, we can implement the full `interpretInitializer` function we
declared near the beginning of this section.

Inside an initializer list, we used `nestedObject` above to search for
the right sub-object to apply an initializer expression to. But here,
outside an initializer list, C99 section 6.7.8 paragraph 13 seems to
disallow anything but immediately compatible types; and GCC, Clang, and
ICC all reject sub-object typed scalar initializers for structs.

```haskell
interpretInitializer ty initial = do
    initial' <- case initial of
        CInitExpr expr _ -> do
            expr' <- interpretExpr True expr
            if resultType expr' `compatibleInitializer` ty
                then pure $ scalar (castTo ty expr')
                else badSource initial "initializer for incompatible type"
        CInitList list _ -> translateInitList ty list

    zeroed <- zeroInitializer ty
    case helper ty (zeroed `mappend` initial') of
        Nothing -> badSource initial "initializer"
        Just expr -> pure expr

    where
```

The simplest type of initialization in C is zero-initialization. It
initializes in a way that the underlying memory of the target is just
zeroed out.

```haskell
    zeroInitializer IsBool{} = return $ scalar (Rust.Lit (Rust.LitRep "false"))
    zeroInitializer IsVoid{} = badSource initial "initializer for void"
    zeroInitializer t@IsInt{} = return $ scalar (Rust.Lit (Rust.LitRep ("0" ++ s)))
        where Rust.TypeName s = toRustType t
    zeroInitializer t@IsFloat{} = return $ scalar (Rust.Lit (Rust.LitRep ("0" ++ s)))
        where Rust.TypeName s = toRustType t
    zeroInitializer t@IsPtr{} = return $ scalar (Rust.Cast 0 (toRustType t))
    zeroInitializer t@IsFunc{} = return $ scalar (Rust.Cast 0 (toRustType t))
    zeroInitializer (IsStruct _ fields) = do
        fields' <- mapM (zeroInitializer . snd) fields
        return (Initializer Nothing (IntMap.fromList $ zip [0..] fields'))
    zeroInitializer IsEnum{} = unimplemented initial
    zeroInitializer (IsIncomplete ident) = do
        (_, struct) <- getIdent (StructIdent ident)
        case struct of
            Just (_, ty'@IsStruct{}) -> zeroInitializer ty'
            _ -> badSource initial "initialization of incomplete type"
```

```haskell
    helper :: CType -> Initializer -> Maybe Rust.Expr
    helper _ (Initializer (Just expr) initials) | IntMap.null initials = Just expr
    helper (IsStruct str fields) (Initializer expr initials) =
        Rust.StructExpr str <$> fields' <*> pure expr
        where
        fields' = forM (IntMap.toList initials) $ \ (idx, value) -> do
            (field, ty') <- listToMaybe (drop idx fields)
            value' <- helper ty' value
            Just (field, value')
    helper _ _ = Nothing
```


Function definitions
====================

A C function definition translates to a single Rust item.

```haskell
interpretFunction :: CFunDef -> EnvMonad Rust.Item
interpretFunction (CFunDef specs declr@(CDeclr mident _ _ _ _) _ body _) = do
```

Determine whether the function should be visible outside this module
based on whether it is declared `static`.

```haskell
    (storage, baseTy) <- baseTypeOf specs
    vis <- case storage of
        Nothing -> return Rust.Public
        Just (CStatic _) -> return Rust.Private
        Just s -> badSource s "storage class specifier for function"
```

Note that `const` is legal but meaningless on the return type of a
function in C. We just ignore whether it was present; there's no place
we can put a `mut` keyword in the generated Rust.

```haskell
    (_mut, isFunc, funTy) <- derivedTypeOf baseTy declr
```

This must be a function type, not a function pointer or a non-function.
Definitions of variadic functions are not allowed because Rust does not
support them.

```haskell
    unless isFunc (badSource declr "function definition")
    (retTy, args) <- case funTy of
        IsFunc _ _ True -> unimplemented declr
        IsFunc retTy args False -> return (retTy, args)
        _ -> badSource declr "function definition"
    useType funTy
```

Add this function to the globals before evaluating its body so recursive
calls work. (Note that function definitions can't be anonymous.)

```haskell
    name <- case mident of
        Nothing -> badSource declr "anonymous function definition"
        Just ident -> addIdent (SymbolIdent ident) (Rust.Mutable, funTy)
```

Translating `main` requires special care; see `wrapMain` below.

```haskell
    when (name == "_c_main") (wrapMain declr name (map snd args))
```

Open a new scope for the body of this function, while making the return
type available so we can correctly translate `return` statements.

```haskell
    let setRetTy flow = flow { functionReturnType = const (return retTy) }
    mapExceptT (local setRetTy) $ scope $ do
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
                Just (mut, argident) -> do
                    argname <- addIdent (SymbolIdent argident) (mut, ty)
                    return (mut, Rust.VarName argname, toRustType ty)
                Nothing -> badSource declr "anonymous parameter"
            | (arg, ty) <- args
            ]
```

Interpret the body of the function.

```haskell
        body' <- interpretStatement body
```

The body's Haskell type is `CStatement`, but language-c guarantees that
it is specifically a compound statement (the `CCompound` constructor).
Rather than relying on that, we allow it to be any kind of statement and
use `statementsToBlock` to coerce the resulting Rust statement into a Rust
block.

Since C doesn't have Rust's syntax allowing the last expression to be
the result of the function, this generated block never has a final
expression.

```haskell
        let attrs = [Rust.Attribute "no_mangle"]
        return (Rust.Item attrs vis
            (Rust.Function [Rust.UnsafeFn] name formals (toRustRetType retTy)
                (statementsToBlock body')))
```


Special-case translation for `main`
===================================

In C, `main` should be a function with one of these types:

```c
int main(void);
int main(int argc, char *argv[]);
int main(int argc, char *argv[], char *envp[]);
```

In Rust, `main` must be declared like this (though the return type
should usually be left off as it's implied):

```rust
fn main() -> () { }
```

So when we encounter a C function named `main`, we can't translate it
as-is or Rust will reject it. Instead we rename it (see `applyRenames`
above) and emit a wrapper function that gets the command line arguments
and environment and passes them to the renamed `main`.

```haskell
wrapMain :: CDeclr -> String -> [CType] -> EnvMonad ()
wrapMain declr realName argTypes = do
```

We decide what the wrapper should do based on what argument types the C
`main` expects. The code for different cases is divided into two parts:
some setup statements which `let`-bind some variables; and a list of
expressions to be passed as arguments to the real `main` function, which
presumably use those `let`-bound variables.

```haskell
    (setup, args) <- wrapArgv argTypes
```

The real `main` will have been translated as an `unsafe fn`, like every
function we translate, so we need to wrap the call to it in an `unsafe`
block. And we need to pass the exit status code that it returns to
Rust's `std::process::exit` function, because Rust programs don't return
exit status from `main`.

```haskell
    let ret = Rust.VarName "ret"
    emitItems [Rust.Item [] Rust.Private (
        Rust.Function [] "main" [] (Rust.TypeName "()") (Rust.Block (
            setup ++
            [ bind Rust.Immutable ret $
                Rust.UnsafeExpr $ Rust.Block [] $ Just $
                call realName args
            , Rust.Stmt (call "std::process::exit" [Rust.Var ret])
            ]
        ) Nothing))]
    where
```

Writing AST constructors by hand is tedious. Here are some helper
functions that allow us to write shorter code. Each one is specialized
for this function's needs.

- `bind` creates a `let`-binding with an inferred type and an initial
  value.

    ```haskell
        bind mut var val = Rust.Let mut var Nothing (Just val)
    ```

- `call` can only call statically-known functions, not function
  pointers.

    ```haskell
        call fn args = Rust.Call (Rust.Var (Rust.VarName fn)) args
    ```

- `chain` produces method calls, but takes the object as its last
  argument, so it reads in reverse.

    ```haskell
        chain method args obj = Rust.MethodCall obj (Rust.VarName method) args
    ```

    `a().b().c()` is written as:

    ``` { .haskell .ignore }
    chain "c" [] $ chain "b" [] $ call "a" []
    ```

Now let's examine the argument types. If `main` is declared `(void)`,
then we don't need to pass it any arguments or do any setup.

```haskell
    wrapArgv [] = return ([], [])
```

But if it's declared `(int, char *argv[])`, then we need to call
`std::env::args_os()` and convert the argument strings to C-style
strings.

```haskell
    wrapArgv (argcType@(IsInt Signed (BitWidth 32))
            : IsPtr Rust.Mutable (IsPtr Rust.Mutable ty)
            : rest) | ty == charType = do
        (envSetup, envArgs) <- wrapEnvp rest
        return (setup ++ envSetup, args ++ envArgs)
        where
        argv_storage = Rust.VarName "argv_storage"
        argv = Rust.VarName "argv"
        str = Rust.VarName "str"
        vec = Rust.VarName "vec"
        setup =
```

Convert each argument string to a vector of bytes, append a terminating
NUL character, and save a reference to the vector so it is not
deallocated until after the real `main` returns.

Converting an `OsString` to a `Vec<u8>` is only allowed if we bring the
Unix-specific `OsStringExt` trait into scope.

```haskell
            [ Rust.StmtItem [] (Rust.Use "std::os::unix::ffi::OsStringExt")
            , bind Rust.Mutable argv_storage $
                chain "collect::<Vec<_>>" [] $
                chain "map" [
                    Rust.Lambda [str] (Rust.BlockExpr (Rust.Block
                        [ bind Rust.Mutable vec (chain "into_vec" [] (Rust.Var str))
                        , Rust.Stmt (chain "push" [
                                Rust.Lit (Rust.LitRep "b'\\0'")
                            ] (Rust.Var vec))
                        ] (Just (Rust.Var vec))))
                ] $
                call "std::env::args_os" []
```

In C, `argv` is required to be a modifiable NULL-terminated array of
modifiable strings. We have modifiable strings as array-backed vectors
in `argv_storage`, so now we need to construct an array-backed vector of
pointers to those strings.

Once we save these pointers, we _must not_ do anything that might change
the length of the vectors we got them from, as that could re-allocate
the backing array and invalidate our pointer.

[`Iterator.chain`](https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html#method.chain)
produces a new iterator which yields all the elements of the original
iterator, followed by anything in the second iterable. We just want to
add one thing at the end of the array&mdash;namely, a NULL
pointer&mdash;and conveniently, the `Option` type is iterable.

```haskell
            , bind Rust.Mutable argv $
                chain "collect::<Vec<_>>" [] $
                chain "chain" [call "Some" [call "std::ptr::null_mut" []]] $
                chain "map" [
                    Rust.Lambda [vec] (chain "as_mut_ptr" [] (Rust.Var vec))
                ] $
                chain "iter_mut" [] $
                Rust.Var argv_storage
            ]
```

In C, `argc` is the number of elements in the `argv` array, but not
counting the terminating NULL pointer. So we pass the number of items
that are in `argv_storage` instead.

For `main`'s second argument, we pass a pointer to the array that backs
`argv`. After this we _must not_ do anything that might change the
length of `argv`, and we must ensure that `argv` is not deallocated
until after the real `main` returns.

```haskell
        args =
            [ Rust.Cast (chain "len" [] (Rust.Var argv_storage)) (toRustType argcType)
            , chain "as_mut_ptr" [] (Rust.Var argv)
            ]
```

We can't translate a program containing a `main` function unless we know
how to construct all of the arguments it expects.

```haskell
    wrapArgv _ = unimplemented declr
```

After handling `argc` and `argv`, we might see a third argument,
conventionally called `envp`. On POSIX systems, we can just pass the
pointer stored in a global variable named `environ` for this argument.

```haskell
    wrapEnvp [] = return ([], [])
    wrapEnvp [arg@(IsPtr Rust.Mutable (IsPtr Rust.Mutable ty))] | ty == charType
        = return (setup, args)
        where
        environ = Rust.VarName "environ"
        setup =
            [ Rust.StmtItem [] $
                Rust.Extern [Rust.ExternStatic Rust.Immutable environ (toRustType arg)]
            ]
        args = [Rust.Var environ]
    wrapEnvp _ = unimplemented declr
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

Inside a function, we find C statements. Unlike C syntax which is oriented
around statements, Rust syntax is mostly just expressions. Nonetheless, by
having `interpretStatement` return a list of Rust statements (instead of
just a Rust expression), we end up being able to get rid of superfluous
curly braces.

```haskell
interpretStatement :: CStat -> EnvMonad [Rust.Stmt]
```

A C statement might be as simple as a "statement expression", which
amounts to a C expression followed by a semicolon. In that case we can
translate the statement by just translating the expression.

If the statement is empty, as in just a semicolon, we don't need to
produce any statements.

```haskell
interpretStatement (CExpr Nothing _) = return []
```

Otherwise, the first argument to `interpretExpr` indicates whether the
expression appears in a context where its result matters. In a statement
expression, the result is discarded, so we pass `False`.

```haskell
interpretStatement (CExpr (Just expr) _) = do
    expr' <- interpretExpr False expr
    return [Rust.Stmt (result expr')]
```

We could have a "compound statement", also known as a "block". A
compound statement contains a sequence of zero or more statements or
declarations; see `interpretBlockItem` below for details.

In the case of an empty compound statement, we make an exception of our
usual rule of not simplifying the generated Rust and simply ignore the
"statement".

```haskell
interpretStatement (CCompound [] [] _) = return []
interpretStatement (CCompound [] items _) = scope $ do
    stmts <- concat <$> mapM interpretBlockItem items
    return [Rust.Stmt (Rust.BlockExpr (statementsToBlock stmts))]
```

This statement could be an `if` statement, with its conditional
expression and "then" branch, and maybe an "else" branch.

The conditional expression is numeric in C, but must have type `bool` in
Rust. We use the `toBool` helper defined below to convert the expression
if necessary.

In C, the "then" and "else" branches are each statements (which may be
compound statements, if they're surrounded by curly braces), but in Rust
they must each be blocks (so they're always surrounded by curly braces).

Here we use `statementsToBlock` to coerce both branches into blocks,
so we don't care whether the original program used a compound statement in
that branch or not.

```haskell
interpretStatement (CIf c t mf _) = do
    c' <- interpretExpr True c
    t' <- interpretStatement t
    f' <- maybe (return []) interpretStatement mf
    return [Rust.Stmt (Rust.IfThenElse (toBool c') (statementsToBlock t') (statementsToBlock f'))]
```

`while` loops are easy to translate from C to Rust. They have identical
semantics in both languages, aside from differences analagous to the
`if` statement, where the loop condition must have type `bool` and the
loop body must be a block.

```haskell
interpretStatement (CWhile c b False _) = do
    c' <- interpretExpr True c
    (b', _) <- loopScope
        (Rust.Break Nothing) (Rust.Continue Nothing)
        (interpretStatement b)
    return [Rust.Stmt (Rust.While Nothing (toBool c') (statementsToBlock b'))]
```

C's `for` loops can be tricky to translate to Rust, which doesn't have
anything quite like them.

Oh, the initialization/declaration part of the loop is easy enough. Open
a new scope, insert any assignments and `let`-bindings at the beginning
of it, and we're good to go. Note that we need to wrap everything in a
block if we have `let`-bindings, but not otherwise.

```haskell
interpretStatement (CFor initial mcond mincr b _) = scope $ case initial of
    Left Nothing -> generateLoop
    Left (Just expr) -> do
        expr' <- interpretExpr False expr
        loop <- generateLoop
        return (Rust.Stmt (result expr') : loop)
    Right decls -> do
        decls' <- interpretDeclarations makeLetBinding decls
        loop <- generateLoop
        return [Rust.Stmt (Rust.BlockExpr (Rust.Block (decls' ++ loop) Nothing))]
    where
```

If the condition is empty, the loop should translate to Rust's infinite
`loop` expression. Otherwise it translates to a `while` loop with the
given condition. In either case, we may apply a label to this loop.

```haskell
    loopHead lt b' = case mcond of
        Nothing -> return [Rust.Stmt (Rust.Loop lt (statementsToBlock b'))]
        Just cond -> do
            cond' <- interpretExpr True cond
            return [Rust.Stmt (Rust.While lt (toBool cond') (statementsToBlock b'))]
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
    generateLoop = case mincr of
        Just incr -> do
            breakName <- uniqueName "break"
            continueName <- uniqueName "continue"
            let breakTo = Just (Rust.Lifetime breakName)
            let continueTo = Just (Rust.Lifetime continueName)

            (b', (Any sawBreak, Any sawContinue)) <- loopScope
                (Rust.Break breakTo) (Rust.Break continueTo)
                (interpretStatement b)
            let inner = if sawContinue
                    then [Rust.Stmt (Rust.Loop continueTo (Rust.Block
                            (b' ++ [Rust.Stmt (Rust.Break Nothing)])
                        Nothing))]
                    else b'

            incr' <- interpretExpr False incr
            loopHead (if sawBreak then breakTo else Nothing)
                (inner ++ exprToStatements incr')
```

We can generate simpler code in the special case that this `for` loop
has an empty increment expression. In that case, we can translate
`break`/`continue` statements into simple `break`/`continue`
expressions, with no magic loops inserted into the body.

```haskell
        Nothing -> do
            (b', _) <- loopScope
                (Rust.Break Nothing) (Rust.Continue Nothing)
                (interpretStatement b)
            loopHead Nothing b'
```

`continue` and `break` statements translate to whatever expression we
decided on in the surrounding context. For example, `continue` might
translate to `break 'continueTo` if our nearest enclosing loop is a
`for` loop.

```haskell
interpretStatement stmt@(CCont _) = recordContinue >> pure . Rust.Stmt <$> getFlow stmt onContinue
interpretStatement stmt@(CBreak _) = recordBreak >> pure . Rust.Stmt <$> getFlow stmt onBreak
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
    return [Rust.Stmt (Rust.Return expr')]
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
    val <- lift (asks kind)
    val stmt
```

Inside loops above, we needed to update the translation to use if either
`break` or `continue` statements show up. `loopScope` runs the provided
translation action using an updated pair of `break`/`continue`
expressions. It also keeps track of whether those constructs ended up being
used.

```haskell
loopScope :: Rust.Expr -> Rust.Expr -> EnvMonad a -> EnvMonad (a, (Any, Any))
loopScope b c =
    mapExceptT (censor (\ output -> output { usesBreak = mempty, usesContinue = mempty })) .
    liftListen (listens (\ output -> (usesBreak output, usesContinue output))) .
    mapExceptT (local (\ flow ->
        flow { onBreak = const (return b), onContinue = const (return c) }))
```


Blocks and scopes
=================

In compound statements (see above), we may encounter local declarations
as well as nested statements. `interpretBlockItem` produces a sequence
of zero or more Rust statements for each compound block item.

```haskell
interpretBlockItem :: CBlockItem -> EnvMonad [Rust.Stmt]
interpretBlockItem (CBlockStmt stmt) = interpretStatement stmt
interpretBlockItem (CBlockDecl decl) = interpretDeclarations makeLetBinding decl
interpretBlockItem item = unimplemented item
```

`exprToStatements` is a helper function which turns a Rust expression
result into a list of Rust statements. It's always possible to do this by
extracting the expression and wrapping it in the `Rust.Stmt` constructor,
but there are a bunch of places in this translation where we don't want to
have to think about whether the expression is already a block expression to
avoid inserting excess pairs of curly braces everywhere.

```haskell
exprToStatements :: Result -> [Rust.Stmt]
exprToStatements Result{ result = Rust.BlockExpr (Rust.Block stmts Nothing) } = stmts
exprToStatements Result{ result = e } = [Rust.Stmt e]
```

`statementsToBlock` is a similar helper function which turns a list of
Rust statements into a block. As before, this can always be done with the
`Rust.Block` constructor, but again this is a convenient way to avoid
inserting excess pairs of curly braces everywhere.

```haskell
statementsToBlock :: [Rust.Stmt] -> Rust.Block
statementsToBlock [Rust.Stmt (Rust.BlockExpr block)] = block
statementsToBlock stmts = Rust.Block stmts Nothing
```

`scope` runs the translation steps in `m`, but then throws away any
changes that `m` made to the environment. Any items added to the output
are kept, though.

```haskell
scope :: EnvMonad a -> EnvMonad a
scope m = do
    -- Save the current environment.
    old <- lift (gets environment)
    a <- m
    -- Restore the environment to its state before running m.
    lift (modify (\ st -> st { environment = old }))
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
        then promotePtr expr (\ t'' f'' -> Rust.IfThenElse c' (Rust.Block [] (Just t'')) (Rust.Block [] (Just f''))) t' f'
        else return Result
            { resultType = IsVoid
            , isMutable = Rust.Immutable
            , result = Rust.IfThenElse c' (Rust.Block (exprToStatements t') Nothing) (Rust.Block (exprToStatements f') Nothing)
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
    (_mut, ty) <- typeName decl
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
force the operand to `bool` type first. We can avoid introducing silly
extra "not" operators by creating a special-case `toNotBool` variant of
`toBool` that returns the opposite value.

```haskell
    CNegOp -> do
        expr' <- interpretExpr True expr
        return Result
            { resultType = IsBool
            , isMutable = Rust.Immutable
            , result = toNotBool expr'
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
    (_mut, ty) <- typeName decl
    let Rust.TypeName ty' = toRustType ty
    return Result
        { resultType = IsInt Unsigned WordWidth
        , isMutable = Rust.Immutable
        , result = Rust.Call (Rust.Var (Rust.VarName ("std::mem::size_of::<" ++ ty' ++ ">"))) []
        }
interpretExpr _ (CAlignofType decl _) = do
    (_mut, ty) <- typeName decl
    let Rust.TypeName ty' = toRustType ty
    return Result
        { resultType = IsInt Unsigned WordWidth
        , isMutable = Rust.Immutable
        , result = Rust.Call (Rust.Var (Rust.VarName ("std::mem::align_of::<" ++ ty' ++ ">"))) []
        }
```

C's array index or array subscript operator, `e1[e2]`, works just like
adding the two expressions and dereferencing the result. Note that in
the C expression `e1[e2]`, although we usually expect `e1` to be a
pointer and `e2` to be an integer, C permits them to be the other way
around. Fortunately, C's pointer addition is also commutative so calling
our `binop` helper here does the right thing.

```haskell
interpretExpr _ expr@(CIndex lhs rhs _) = do
    lhs' <- interpretExpr True lhs
    rhs' <- interpretExpr True rhs
    ptr <- binop expr CAddOp lhs' rhs'
    case resultType ptr of
        IsPtr mut ty -> return Result
            { resultType = ty
            , isMutable = mut
            , result = Rust.Deref (result ptr)
            }
        _ -> badSource expr "array subscript of non-pointer"
```

Function calls first translate the expression which identifies which
function to call, and any argument expressions.

```haskell
interpretExpr _ expr@(CCall func args _) = do
    func' <- interpretExpr True func
    case resultType func' of
        IsFunc retTy argTys variadic -> do
            args' <- castArgs variadic (map snd argTys) args
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
    castArgs True [] rest = mapM (fmap promoteArg . interpretExpr True) rest
    castArgs False [] _ = badSource expr "arguments (too many)"
    castArgs _ _ [] = badSource expr "arguments (too few)"
```

In C, the "default argument promotions" (C99 6.5.2.2 paragraphs 6-7) are
applied to any variable parameters after the last declared parameter.
They would also be applied to arguments passed to a function declared
with an empty argument list (`foo()`) or implicitly declared due to a
lack of a prototype, except we don't allow either of those cases.

```haskell
    promoteArg :: Result -> Rust.Expr
    promoteArg r = case resultType r of
        IsFloat _ -> castTo (IsFloat 64) r
        ty -> castTo (intPromote ty) r
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
        IsIncomplete tyIdent -> do
            (_, struct) <- getIdent (StructIdent tyIdent)
            case struct of
                Just (_, IsStruct _ fields) -> return fields
                _ -> badSource expr "member access of incomplete type"
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
    (name, sym) <- getIdent (SymbolIdent ident)
    case sym of
        Just (mut, ty@(IsEnum enum)) -> do
            return Result
                { resultType = ty
                , isMutable = mut
                , result = Rust.Path (Rust.PathSegments [enum, name])
                }
        Just (mut, ty) -> do
            lift $ tell mempty { usesSymbols = Set.singleton name }
            return Result
                { resultType = ty
                , isMutable = mut
                , result = Rust.Var (Rust.VarName name)
                }
        Nothing -> badSource expr "undefined variable"
```

C literals (integer, floating-point, character, and string) translate to
similar tokens in Rust.

> **TODO**: Figure out what to do about floating-point hex literals,
> which as far as I can tell Rust doesn't support (yet?).

> **TODO**: Translate wide character and string literals.

```haskell
interpretExpr _ expr@(CConst c) = case c of
```

In C, the type of an integer literal depends on which types its value
will fit in, constrained by its suffixes (`U` or `L`) and whether its
representation is decimal or another base. See C99 6.4.4.1 paragraph 5
and its subsequent table.

For the purposes of deciding whether a literal will fit within the
bounds of a type, we choose to pretend that `long` is 32 bits, but the
Rust type we give it is `isize`. If a constant does not fit in 32 bits,
we always give it type `i64`.

```haskell
    CIntConst (CInteger v repr flags) _ ->
        let allow_signed = not (testFlag FlagUnsigned flags)
            allow_unsigned = not allow_signed || repr /= DecRepr
            widths =
                [ (32 :: Int,
                    if any (`testFlag` flags) [FlagLongLong, FlagLong]
                    then WordWidth else BitWidth 32)
                , (64, BitWidth 64)
                ]
            allowed_types =
                [ IsInt s w
                | (bits, w) <- widths
                , (True, s) <- [(allow_signed, Signed), (allow_unsigned, Unsigned)]
                , v < 2 ^ (bits - if s == Signed then 1 else 0)
                ]
            str = case repr of
                DecRepr -> show v
                OctalRepr -> "0o" ++ showOct v ""
                HexRepr -> "0x" ++ showHex v ""
        in case allowed_types of
        [] -> badSource expr "integer (too big)"
        ty : _ -> return (literalNumber ty str)
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

C99 compound literals are really not much different than an initializer
list with the type of the thing we are initializing included.

```haskell
interpretExpr _ (CCompoundLit decl initials info) = do
    (mut, ty) <- typeName decl
    final <- interpretInitializer ty (CInitList initials info)
    return Result
        { resultType = ty
        , isMutable = mut
        , result = final
        }
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
    CShlOp -> shift Rust.ShiftL
    CShrOp -> shift Rust.ShiftR
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
    shift op' = return Result
        { resultType = lhsTy
        , isMutable = Rust.Immutable
        , result = op' (castTo lhsTy lhs) (castTo rhsTy rhs)
        }
        where
        lhsTy = intPromote (resultType lhs)
        rhsTy = intPromote (resultType rhs)
    comparison op' = do
        res <- promotePtr expr op' lhs rhs
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

`toNotBool` works just like `Rust.Not . toBool`, except that it can
generate simpler expressions. Instead of `!!p.is_null()`, for example,
it simply generates `p.is_null()`. This approach satisfies our design
goal of generating Rust which is as structurally close to the input as
possible.

```haskell
toNotBool :: Result -> Rust.Expr
toNotBool (Result { resultType = t, result = v }) = case t of
    IsBool -> Rust.Not v
    IsPtr _ _ -> Rust.MethodCall v (Rust.VarName "is_null") []
    _ -> Rust.CmpEQ v 0
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

Conveniently, Rust allows `bool` and `enum` typed expressions to be cast
to any integer type, and it converts `true` to 1 and `false` to 0 just
like C requires, so we don't need any special magic to handle booleans
or enumerated types here.

```haskell
intPromote IsBool = IsInt Signed (BitWidth 32)
intPromote (IsEnum _) = enumReprType
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

```haskell
usual :: CType -> CType -> Maybe CType
usual (IsFloat aw) (IsFloat bw) = Just (IsFloat (max aw bw))
usual a@(IsFloat _) _ = Just a
usual _ b@(IsFloat _) = Just b
```

"Otherwise, the integer promotions are performed on both operands."

```haskell
usual origA origB = case (intPromote origA, intPromote origB) of
```

"Then the following rules are applied to the promoted operands:"

Note that we refuse to translate this expression if either promoted type
is not an integer type, or if the integer conversion ranks are
incomparable according to `integerConversionRank`. The latter is not due
to anything in the C standard, which describes a total order for integer
conversion ranks. Rather, we refuse to translate these programs due to
non-portable code complicating the translation.

- "If both operands have the same type, then no further conversion is
  needed."

    ```haskell
        (a, b) | a == b -> Just a
    ```

- "Otherwise, if both operands have signed integer types or both have
  unsigned integer types, the operand with the type of lesser integer
  conversion rank is converted to the type of the operand with greater
  rank."

    ```haskell
        (IsInt Signed sw, IsInt Unsigned uw) -> mixedSign sw uw
        (IsInt Unsigned uw, IsInt Signed sw) -> mixedSign sw uw
        (IsInt as aw, IsInt _bs bw) -> do
            rank <- integerConversionRank aw bw
            Just (IsInt as (if rank == GT then aw else bw))
        _ -> Nothing
        where
    ```

At this point we have one signed and one unsigned operand. The usual
arithmetic conversions don't care which order the operands are in, so
`mixedSign` is a helper function where the signed width is always the
first argument and the unsigned width is always the second.

- "Otherwise, if the operand that has unsigned integer type has rank
  greater or equal to the rank of the type of the other operand, then
  the operand with signed integer type is converted to the type of the
  operand with unsigned integer type."

    ```haskell
        mixedSign sw uw = do
            rank <- integerConversionRank uw sw
            Just $ case rank of
                GT -> IsInt Unsigned uw
                EQ -> IsInt Unsigned uw
    ```

- "Otherwise, if the type of the operand with signed integer type can
  represent all of the values of the type of the operand with unsigned
  integer type, then the operand with unsigned integer type is converted
  to the type of the operand with signed integer type."

    A signed type can represent all the values of an unsigned type if
    the unsigned type's bit-width is strictly smaller than the signed
    type's bit-width.

    For our purposes, `long` can only represent the values of `unsigned`
    types smaller than `int` (because `long` and `int` might be the same
    size). But `unsigned long` values can only be represented by signed
    types bigger than 64 bits (because `long` might be 64 bits instead).

    ```haskell
                _ | bitWidth 64 uw < bitWidth 32 sw -> IsInt Signed sw
    ```

- "Otherwise, both operands are converted to the unsigned integer type
  corresponding to the type of the operand with signed integer type."

    Given the above definitions, this only happens for `unsigned long`
    and `int64_t`, where we want to choose `uint64_t`.

    ```haskell
                _ -> IsInt Unsigned sw
    ```

The usual arithmetic conversions refer to a definition called "integer
conversion rank" from C99 6.3.1.1. We want these widths to have strictly
increasing integer conversion rank:

- `BitWidth 32` (our representation of `int`)
- `WordWidth` (our representation of `long`)
- `BitWidth 64`

The first two come from C99 6.3.1.1 which says `long` has a higher rank
than `int`. We add the last as an implementation choice. Since `isize`
could be either `i32` or `i64`, when combining `isize` with another type
we'll bump up to whichever type is definitely bigger.

We disallow comparing bit-widths between 32 and 64 bits, exclusive,
against word-size. Since word-size is platform-dependent, we can't be
sure which is larger.

```haskell
integerConversionRank :: IntWidth -> IntWidth -> Maybe Ordering
integerConversionRank (BitWidth a) (BitWidth b) = Just (compare a b)
integerConversionRank WordWidth WordWidth = Just EQ
integerConversionRank (BitWidth a) WordWidth
    | a <= 32 = Just LT
    | a >= 64 = Just GT
integerConversionRank WordWidth (BitWidth b)
    | b <= 32 = Just GT
    | b >= 64 = Just LT
integerConversionRank _ _ = Nothing
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

Finally, `promotePtr` is like `promote` but for operators that allow
pointers as operands, not just arithmetic types. Since integer literals
may be implicitly used as pointers, if either operand is a pointer, we
pretend the other one is a void pointer and let `compatiblePtr` figure
out what type it should really be converted to.

```haskell
promotePtr
    :: (Pretty node, Pos node)
    => node
    -> (Rust.Expr -> Rust.Expr -> Rust.Expr)
    -> Result -> Result -> EnvMonad Result
promotePtr node op a b = case (resultType a, resultType b) of
    (IsPtr _ _, _) -> ptrs
    (_, IsPtr _ _) -> ptrs
    _ -> promote node op a b
    where
    ptrOrVoid r = case resultType r of
        t@(IsPtr _ _) -> t
        _ -> IsPtr Rust.Mutable IsVoid
    ty = compatiblePtr (ptrOrVoid a) (ptrOrVoid b)
    ptrs = return Result
        { resultType = ty
        , isMutable = Rust.Immutable
        , result = op (castTo ty a) (castTo ty b)
        }
```


Internal representation of C types
==================================

> **TODO**: Document the type representation we use here.

```haskell
data Signed = Signed | Unsigned
    deriving (Show, Eq)

data IntWidth = BitWidth Int | WordWidth
    deriving (Show, Eq)
```

Sometimes we want to treat `WordWidth` as being equivalent to a
particular number of bits, but the choice depends on whether we want it
to be its smallest width or its largest. (We choose to define the
machine's word size as always either 32 or 64, because those are the
only sizes Rust currently targets.)

```haskell
bitWidth :: Int -> IntWidth -> Int
bitWidth wordWidth WordWidth = wordWidth
bitWidth _ (BitWidth w) = w
```

```haskell
data CType
    = IsBool
    | IsInt Signed IntWidth
    | IsFloat Int
    | IsVoid
    | IsFunc CType [(Maybe (Rust.Mutable, Ident), CType)] Bool
    | IsPtr Rust.Mutable CType
    | IsStruct String [(String, CType)]
    | IsEnum String
    | IsIncomplete Ident
    deriving Show
```

Deriving a default implementation of the `Eq` typeclass for equality
almost works, except for our representation of function types, where
argument names and `const`-ness may differ without the types being
different.

```haskell
instance Eq CType where
    IsBool == IsBool = True
    IsInt as aw == IsInt bs bw = as == bs && aw == bw
    IsFloat aw == IsFloat bw = aw == bw
    IsVoid == IsVoid = True
    IsFunc aRetTy aFormals aVariadic == IsFunc bRetTy bFormals bVariadic =
        aRetTy == bRetTy && aVariadic == bVariadic &&
        map snd aFormals == map snd bFormals
    IsPtr aMut aTy == IsPtr bMut bTy = aMut == bMut && aTy == bTy
    IsStruct aName aFields == IsStruct bName bFields =
        aName == bName && aFields == bFields
    IsEnum aName == IsEnum bName = aName == bName
    IsIncomplete aName == IsIncomplete bName = aName == bName
    _ == _ = False
```

To track which type declarations are actually used, at various points we
need to find out which type names are referenced in some `CType`.
`declaredNames` computes that set with a recursive walk down the type.

```haskell
declaredNames :: CType -> Set.Set String
declaredNames (IsFunc retTy args _) =
    Set.unions (map declaredNames (retTy : map snd args))
declaredNames (IsPtr _ ty) = declaredNames ty
declaredNames (IsStruct name fields) = Set.insert name
    (Set.unions (map (declaredNames . snd) fields))
declaredNames (IsEnum name) = Set.singleton name
declaredNames (IsIncomplete ident) = Set.singleton (identToString ident)
declaredNames _ = Set.empty
```

```haskell
toRustType :: CType -> Rust.Type
toRustType IsBool = Rust.TypeName "bool"
toRustType (IsInt s w) = Rust.TypeName ((case s of Signed -> 'i'; Unsigned -> 'u') : (case w of BitWidth b -> show b; WordWidth -> "size"))
toRustType (IsFloat w) = Rust.TypeName ('f' : show w)
toRustType IsVoid = Rust.TypeName "std::os::raw::c_void"
toRustType (IsFunc retTy args variadic) = Rust.TypeName $ concat
    [ "unsafe extern fn("
    , args'
    , ")"
    , if retTy /= IsVoid then " -> " ++ typename retTy else ""
    ]
    where
    typename (toRustType -> Rust.TypeName t) = t
    args' = intercalate ", " (
            map (typename . snd) args ++ if variadic then ["..."] else []
        )
toRustType (IsPtr mut to) = let Rust.TypeName to' = toRustType to in Rust.TypeName (rustMut mut ++ to')
    where
    rustMut Rust.Mutable = "*mut "
    rustMut Rust.Immutable = "*const "
toRustType (IsStruct name _fields) = Rust.TypeName name
toRustType (IsEnum name) = Rust.TypeName name
toRustType (IsIncomplete ident) = Rust.TypeName (identToString ident)
```

Functions that don't return anything have a return type in Rust that is
different than the representation of C's `void` type elsewhere.

```haskell
toRustRetType :: CType -> Rust.Type
toRustRetType IsVoid = Rust.TypeName "()"
toRustRetType ty = toRustType ty
```

C leaves it up to the implementation to decide whether the base `char`
type is signed or unsigned. We choose unsigned, because that's the type
of Rust's byte literals.

```haskell
charType :: CType
charType = IsInt Unsigned (BitWidth 8)
```

C permits implementations to represent enum values using integer types
narrower than `int`, but for the moment we choose not to. This may be
incompatible with some ABIs.

```haskell
enumReprType :: CType
enumReprType = IsInt Signed (BitWidth 32)
```

```haskell
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
        (_name, mty) <- getIdent (StructIdent ident)
        ty <- case mty of
            Just (_, ty) -> return ty
            Nothing -> emitIncomplete ident
        return (mut, ty)
    go (CSUType (CStruct CStructTag mident (Just declarations) _ _) _) (mut, _) = do
        fields <- fmap concat $ forM declarations $ \ declaration@(CDecl spec decls _) -> do
            (storage, base) <- baseTypeOf spec
            case storage of
                Just s -> badSource s "storage class specifier in struct"
                Nothing -> return ()
            forM decls $ \ decl -> case decl of
                (Just declr@(CDeclr (Just field) _ _ _ _), Nothing, Nothing) -> do
                    (_mut, isFunc, ty) <- derivedTypeOf base declr
                    when isFunc (badSource declr "function as struct field")
                    return (identToString field, ty)
                (_, Nothing, Just _size) -> unimplemented declaration
                _ -> badSource declaration "field in struct"
        name <- case mident of
            Just ident -> do
                let name = identToString ident
                addIdent (StructIdent ident) (Rust.Immutable, IsStruct name fields)
            Nothing -> uniqueName "Struct"
        let attrs = [Rust.Attribute "derive(Clone, Copy)", Rust.Attribute "repr(C)"]
        emitItems [Rust.Item attrs Rust.Public (Rust.Struct name [ (field, toRustType fieldTy) | (field, fieldTy) <- fields ])]
        return (mut, IsStruct name fields)
    go (CSUType (CStruct CUnionTag mident _ _ _) node) (mut, _) = do
        ident <- case mident of
            Just ident -> return ident
            Nothing -> do
                name <- uniqueName "Union"
                return (internalIdentAt (posOfNode node) name)
        ty <- emitIncomplete ident
        return (mut, ty)
    go spec@(CEnumType (CEnum (Just ident) Nothing _ _) _) (mut, _) = do
        (_, mty) <- getIdent (EnumIdent ident)
        case mty of
            Just (_, ty) -> return (mut, ty)
            Nothing -> badSource spec "undefined enum"
    go (CEnumType (CEnum mident (Just items) _ _) _) (mut, _) = do
        let Rust.TypeName repr = toRustType enumReprType
        name <- case mident of
            Just ident -> do
                 let name = identToString ident
                 addIdent (EnumIdent ident) (Rust.Immutable, IsEnum name)
            Nothing -> uniqueName "Enum"
        enums <- forM items $ \ (ident, mexpr) -> do
            enumName <- addIdent (SymbolIdent ident) (Rust.Immutable, IsEnum name)
            case mexpr of
                Nothing -> return (Rust.EnumeratorAuto enumName)
                Just expr -> do
                    expr' <- interpretExpr True expr
                    return (Rust.EnumeratorExpr enumName (castTo enumReprType expr'))
        let attrs = [ Rust.Attribute "derive(Clone, Copy)"
                    , Rust.Attribute (concat [ "repr(", repr, ")" ])
                    ]
        emitItems [Rust.Item attrs Rust.Public (Rust.Enum name enums)]
        return (mut, IsEnum name)
    go spec@(CTypeDef ident _) (mut1, _) = do
        (name, mty) <- getIdent (TypedefIdent ident)
        case mty of
            Just (mut2, ty) -> return (if mut1 == mut2 then mut1 else Rust.Immutable, ty)
            Nothing | name == "__builtin_va_list" -> do
                ty <- emitIncomplete ident
                return (mut1, IsPtr Rust.Mutable ty)
            Nothing -> badSource spec "undefined type"
    go spec _ = unimplemented spec

derivedTypeOf :: (Rust.Mutable, CType) -> CDeclr -> EnvMonad (Rust.Mutable, Bool, CType)
derivedTypeOf (basemut, basety) declr@(CDeclr _ derived _ _ _) =
    foldrM derive (basemut, False, basety) derived
    where
```

In our internal type representation, `IsFunc` is a function _pointer_.
So if we see a `CPtrDeclr` followed by a `CFunDeclr`, we should eat the
pointer.

```haskell
    derive (CPtrDeclr _ _) (c, True, to) = return (c, False, to)
```

If we see a `CArrDeclr` or `CFunDeclr` before a `CFunDeclr`, that's an
error; there must be an intervening pointer.

```haskell
    derive _ (_, True, _) = badSource declr "use of function type"
    derive (CPtrDeclr quals _) (c, False, to) = return (mutable quals, False, IsPtr c to)
    derive (CArrDeclr quals _ _) (c, False, to) = return (mutable quals, False, IsPtr c to)
```

> **TODO**: Handling old-style function declarations is probably not
> _too_ difficult...

```haskell
    derive (CFunDeclr (Left _) _ _) _ = unimplemented declr
    derive (CFunDeclr (Right (args, variadic)) _ _) (c, False, retTy) = do
        args' <- sequence
            [ do
                (storage, base') <- baseTypeOf argspecs
                case storage of
                    Nothing -> return ()
                    Just (CRegister _) -> return ()
                    Just s -> badSource s "storage class specifier on argument"
                case declr' of
                    [] -> return (Nothing, snd base')
                    [(Just argdeclr@(CDeclr argname _ _ _ _), Nothing, Nothing)] -> do
                        (mut, isFunc, ty) <- derivedTypeOf base' argdeclr
                        when isFunc (badSource arg "function as function argument")
                        return (fmap ((,) mut) argname, ty)
                    _ -> badSource arg "function argument"
            | arg@(CDecl argspecs declr' _) <-
```

Treat argument lists `(void)` and `()` the same: we'll pretend that both
mean the function takes no arguments.

```haskell
                case args of
                [CDecl [CTypeSpec (CVoidType _)] [] _] -> []
                _ -> args
            ]
        return (c, True, IsFunc retTy args' variadic)

mutable :: [CTypeQualifier a] -> Rust.Mutable
mutable quals = if any (\ q -> case q of CConstQual _ -> True; _ -> False) quals then Rust.Immutable else Rust.Mutable

typeName :: CDecl -> EnvMonad (Rust.Mutable, CType)
typeName decl@(CDecl spec declarators _) = do
    (storage, base) <- baseTypeOf spec
    case storage of
        Just s -> badSource s "storage class specifier in type name"
        Nothing -> return ()
    (mut, ty) <- case declarators of
        [] -> return base
        [(Just declr@(CDeclr Nothing _ _ _ _), Nothing, Nothing)] -> do
            (mut, isFunc, ty) <- derivedTypeOf base declr
            when isFunc (badSource decl "use of function type")
            return (mut, ty)
        _ -> badSource decl "type name"
    useType ty
    return (mut, ty)
```
