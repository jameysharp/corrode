Languages with different primitives for control-flow can be tricky for
automatic translation. That's especially true if you're translating from
a language that allows arbitrary `goto` statements, like C, to a
language that does not, like pretty much every other widely used
programming language.

This module takes care of most of that complexity in two steps.

1. First, it allows you to construct a Control-Flow Graph (CFG)
representing all loops, conditionals, and gotos for a function in the
source program. (This is usually pretty straight-forward.)

2. Then this module can analyse that CFG and identify which parts should
be treated as loops and which should be treated as `if`-statements, and
what order those should appear in for the translated function.

If there are `goto` statements in the source, the output of step 2 may
look very different than the input to step 1!

```haskell
{-# LANGUAGE Rank2Types #-}
module Language.Rust.Corrode.CFG (
    Label, Terminator'(..), Terminator, BasicBlock(..),
    CFG, Unordered, DepthFirst, prettyCFG,
    BuildCFGT, mapBuildCFGT, addBlock, newLabel, buildCFG,
    depthFirstOrder, removeEmptyBlocks, structureCFG,
) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import qualified Control.Monad.Trans.RWS.Lazy as RWS
import Control.Monad.Trans.State
import Data.Either
import Data.Foldable
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.IntSet as IntSet
import Data.List
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Text.PrettyPrint.HughesPJClass hiding (empty)
```


Control-Flow Graph representation
=================================

A control-flow graph is a collection of "basic blocks" containing
sequential code, plus arrows indicating what to execute next when the
computer reaches the end of the current basic block.

To be a valid basic block, control flow must enter only at the beginning
of the block, and leave only at the end.

Basic blocks have a type parameter, `s`, for whatever type you want to
use to represent the code inside the basic block. This module generally
doesn't care what representation you use&mdash;a reasonable choice might
be a list of statements in your target language&mdash;but whatever you
choose, it should probably have an instance of both `Foldable` and
`Monoid`. (The built-in list type provides both of these, for instance.)
Otherwise you won't be able to use some key functions that this module
provides.

(We'll discuss the `c` type parameter while explaining terminators,
next.)

We assign every basic block an arbitrary "label" that we can use to
refer to it from elsewhere in the control-flow graph. This could be
anything, but it's convenient to use distinct integers as labels.

```haskell
data BasicBlock s c = BasicBlock s (Terminator c)
type Label = Int
```

A basic block ends with a specification of which block to proceed to
next, which we'll call the block's "terminator".

We model these cases:

- `Unreachable` indicates that the source language guarantees that
  control will never reach the end of this block. This is usually
  because the block ends with a `return` statement. But it can also
  happen if the block ends with a call to a function that is known to
  never return, for example.

- `Branch` indicates that when this block completes, control always
  proceeds to the specified block.

- `CondBranch` is a "conditional branch". If the specified condition is
  true at runtime, then control goes to the first specified block;
  otherwise it goes to the second block. Note that we represent
  conditional branches as always having both a "true" case and a "false"
  case; there's no implicit "fall-through" behavior like you might find
  for a conditional jump in assembly language, for instance.

```haskell
data Terminator' c l
    = Unreachable
    | Branch l
    | CondBranch c l l
```

The above `Terminator'` type has two generic type parameters:

The first is the type to use for condition expressions. This should
probably be whatever type you use to represent boolean expressions in
your target language, but this module doesn't look at what's inside
those condition expressions at all, so you can use any representation
you want.

The second type parameter is for whatever type you want to use for
labels for basic blocks. Although we've chosen a specific `Label` type
above, it's convenient to make this a type parameter so we can define
instances of the standard `Functor` and `Foldable` type-classes, for
generic access to the outgoing edges.

For convenience, we define a type alias that specifies that the label
type is specifically the above-chosen `Label`.

```haskell
type Terminator c = Terminator' c Label

instance Functor (Terminator' c) where
    fmap _ Unreachable = Unreachable
    fmap f (Branch l) = Branch (f l)
    fmap f (CondBranch c l1 l2) = CondBranch c (f l1) (f l2)

instance Foldable (Terminator' c) where
    foldMap _ Unreachable = mempty
    foldMap f (Branch l) = f l
    foldMap f (CondBranch _ l1 l2) = f l1 `mappend` f l2
```

Now we can define a complete control-flow graph in terms of the previous
types. It has a "start" label, indicating which basic block is the first
one to start executing on entrance to a function; and a map from labels
to their corresponding basic blocks.

After the CFG has been constructed, there's a pre-processing step we do
to sort the basic blocks into a useful order. We use a small type-system
trick here to indicate whether that sorting has happened: a value of
type `CFG Unordered` has not been sorted yet, while a `CFG DepthFirst`
has. A function that accepts any `CFG k` doesn't care whether the blocks
have been sorted or not. So keep an eye out for that, below, because the
type signatures serve as documentation of an important precondition.

With this type-system trick, the Haskell compiler will enforce that
callers pass only sorted CFGs to functions that require them, which is a
nice sanity check. However, within this module we still have to be
careful to only tag a CFG as sorted if it actually is, and also to tag
functions as requiring a sorted CFG as needed. Haskell can't magically
figure that out!

```haskell
data Unordered
data DepthFirst
data CFG k s c = CFG Label (IntMap.IntMap (BasicBlock s c))
```

When things go wrong, it's handy to be able to print a human-readable
version of an entire control-flow graph so we can inspect it. This
function takes helper functions for formatting statements and
conditional expressions, respectively, and uses them within each basic
block to format the entire control-flow graph.

```haskell
prettyCFG :: (s -> Doc) -> (c -> Doc) -> CFG k s c -> Doc
prettyCFG fmtS fmtC (CFG entry blocks) = vcat $
    (text "start @" <> text (show entry)) : blocks'
    where
    blocks' = do
        (label, BasicBlock stmts term) <- IntMap.toList blocks
        let blockHead = text (show label) <> text ":"
        let blockBody = fmtS stmts
        let blockTail = case term of
                Unreachable -> text "// unreachable"
                Branch to -> text ("goto " ++ show to ++ ";")
                CondBranch cond true false ->
                    text "if(" <> fmtC cond
                        <> text ") goto " <> text (show true)
                        <> text "; else goto " <> text (show false)
                        <> text ";"
        blockHead : map (nest 4) [blockBody, blockTail] ++ [text ""]
```


Constructing CFGs
=================

This module provides a small monadic interface for constructing
control-flow graphs. It's provided as a "monad transformer", meaning that
you can combine this monad with other monads. For example, if you need
to keep information about variable declarations that are in scope in
order to translate statements and expressions correctly, you can use a
`State` monad for that, and layer this `BuildCFGT` monad on top of it.
Then you can use actions from either monad as needed.

```haskell
type BuildCFGT m s c = StateT (BuildState s c) m
```

Because this is a monad transformer, you may find you need to perform
some operation transforming the underlying monad. For example, `Reader`
monads have a `local` operation that runs some specified monadic action
with a different value in its environment than the outer computation
uses, and similarly with the `Writer` monad's `listen` and `censor`
operations. To use these kinds of operations with `BuildCFGT`, you need
to wrap them in `mapBuildCFGT`.

The type signature here is a little bit weird. Your function has to
preserve the current state of the CFG builder, because we're suspending
the usual monad rules that would normally carry that state around behind
the scenes. But we don't allow you to peek at or modify the CFG builder
state along the way. That's enforced by using the GHC `Rank2Types`
language extension (enabled at the top of this module) to declare that
your transformation must work for all possible state types: Code that
must work for all possible types can't possibly do anything but pass
that data along unchanged.

```haskell
mapBuildCFGT
    :: (forall st. m (a, st) -> n (b, st))
    -> BuildCFGT m s c a -> BuildCFGT n s c b
mapBuildCFGT = mapStateT
```

While constructing a new control-flow graph, we need to keep track of
two things: any basic blocks constructed so far, and a unique label to
use for the next basic block. We keep both in a new data type,
`BuildState`.

It might seem like we shouldn't need to keep a separate counter for
unique labels. Couldn't we just look at the label for the last block
that was constructed, add 1, and use that as the next block's label?

Unfortunately, during CFG construction we often need to refer to blocks
that we haven't constructed yet. For example, to construct a loop, we
might construct the body of the loop with a branch back to the loop
header, and only then construct the loop header with a branch into the
body.

That means we may have to generate any number of labels before finishing
the corresponding blocks, so we have to keep track of which IDs we
already handed out.

Note that this also means that this intermediate representation of a CFG
is generally not a valid CFG, because it includes blocks that branch to
other blocks that haven't been constructed yet. It's the caller's
responsibility to ensure that all blocks get added eventually.

```haskell
data BuildState s c = BuildState
    { buildLabel :: Label
    , buildBlocks :: IntMap.IntMap (BasicBlock s c)
    }
```

`newLabel` just returns a unique `Label`.

```haskell
newLabel :: Monad m => BuildCFGT m s c Label
newLabel = do
    old <- get
    put old { buildLabel = buildLabel old + 1 }
    return (buildLabel old)
```

`addBlock` saves the given statements and terminator in the state.

```haskell
addBlock :: Monad m => Label -> s -> Terminator c -> BuildCFGT m s c ()
addBlock label stmt terminator = do
    modify $ \ st -> st
        { buildBlocks = IntMap.insert label (BasicBlock stmt terminator)
            (buildBlocks st)
        }
```

Finally we have the function that runs a builder and returns the CFG
that it built. The builder's return value must be the label to use as
the entry-point for the control-flow graph.

Note that the constructed CFG is tagged as `Unordered` because we
haven't sorted it yet.

```haskell
buildCFG :: Monad m => BuildCFGT m s c Label -> m (CFG Unordered s c)
buildCFG root = do
    (label, final) <- runStateT root (BuildState 0 IntMap.empty)
    return (CFG label (buildBlocks final))
```

It's normal to write simple translations for building the CFG that
produce some pretty silly-looking control-flow graphs. For example, they
may produce a lot of basic blocks that have no statements in them and
just unconditionally branch somewhere else. Those blocks can be safely
removed, if we're a little careful, without changing the meaning of the
CFG, and that's what `removeEmptyBlocks` does.

> **NOTE**: I don't think this is necessary; all of the following
> algorithms should produce the same output even with empty blocks
> present, as far as I can figure. But when something goes wrong and we
> need to report an error, it's nice to have a simpler CFG to examine.
> So I'm not deleting this, but I'm not going to bother documenting how
> it works because it isn't important.

> **TODO**: Think about whether this can be folded into
> `depthFirstOrder` without making that function too complicated.

```haskell
removeEmptyBlocks :: Foldable f => CFG k (f s) c -> CFG Unordered (f s) c
removeEmptyBlocks (CFG start blocks) = CFG (rewrite start) blocks'
    where
    go = do
        (empties, done) <- get
        case IntMap.minViewWithKey empties of
            Nothing -> return ()
            Just ((from, to), empties') -> do
                put (empties', done)
                step from to
                go
    step from to = do
        (empties, done) <- get
        case IntMap.splitLookup to empties of
            (_, Nothing, _) -> return ()
            (e1, Just to', e2) -> do
                put (e1 `IntMap.union` e2, done)
                step to to'
        (empties', done') <- get
        let to' = IntMap.findWithDefault to to done'
        put (empties', IntMap.insert from to' done')
    isBlockEmpty (BasicBlock s (Branch to)) | null s = Just to
    isBlockEmpty _ = Nothing
    rewrites = snd $ execState go (IntMap.mapMaybe isBlockEmpty blocks, IntMap.empty)
    rewrite to = IntMap.findWithDefault to to rewrites
    discards = IntMap.keysSet (IntMap.filterWithKey (/=) rewrites)
    rewriteBlock from _ | from `IntSet.member` discards = Nothing
    rewriteBlock _ (BasicBlock b term) = Just (BasicBlock b (fmap rewrite term))
    blocks' = IntMap.mapMaybeWithKey rewriteBlock blocks
```


Transforming CFGs to structured programs
========================================

Once we've constructed a CFG, the real challenge is to turn that messy
pile of basic blocks back into structured control flow.

This implementation would work for a pretty wide variety of languages.
It assumes the target language has:

1. If-then-else,
2. Loops,
3. Multi-level exits from loops.

That last point needs some explanation. Most languages with loops
provide some way for the programmer to break out of a loop early, or
restart at the beginning of the loop without finishing the current
iteration. (Let's call both kinds of control-flow "loop exits".) Of
those languages, many but not all of them allow the programmer to exit
more than one loop in one go, by giving loops names and specifying which
loop to exit by name. This code assumes that your target language is one
of the latter kind.

This algorithm proceeds by first sorting the basic blocks into an order
that makes the later steps more efficient; then collecting a bunch of
analyses about the CFG; and finally using all the analysis results to
decide which blocks are loops, which are if-then-else, and where to
place them all.

One helper used in several algorithms just finds, for each block in the
control-flow graph, the set of other blocks that can branch directly to
it.

```haskell
predecessors :: CFG k s c -> IntMap.IntMap IntSet.IntSet
predecessors (CFG _ blocks) = IntMap.foldrWithKey grow IntMap.empty blocks
    where
    grow from (BasicBlock _ term) rest = foldr (insertEdge from) rest term
    insertEdge from to = IntMap.insertWith IntSet.union to (IntSet.singleton from)
```


Depth-First Ordering
--------------------

Every algorithm below gets simpler and more efficient if we establish
one simple invariant first:

> If block `u` can branch to block `v`, then either the label for `u` is
> less than the label for `v`, or that branch is returning to the
> beginning of a loop.

(Note that there are often multiple assignments of labels that satisfy
this rule.)

In some cases it's also useful to establish that every basic block in
the control-flow graph is reachable by some path from the start of the
function, and it turns out this is a convenient place to do that too.

Let's explore how we can accomplish all that in a moment, but first, why
is this a useful invariant?

By re-labeling every basic block according to that rule, we get two
benefits:

1. If we know that there's a control-flow path from one basic block to
another, then we can check which one should be earlier in the function
by just checking which one has a smaller label.

2. We can accumulate control-flow facts about all blocks in a single
pass by processing blocks in label order. If computing a fact for a
particular block depends only on data from blocks that came earlier,
then we just need to process blocks in increasing order. If instead
facts propagate from later blocks to earlier ones, then we should
process blocks in decreasing order.

Conveniently, we chose to store the collection of basic blocks in an
`IntMap`, which provides efficient ways to work in either ascending or
descending order by label. So all we have to do is re-number all the
labels.

(There's a nice bonus that this order makes the output of `prettyCFG`
easier to understand, if you happen to be unlucky enough to need to
inspect the raw basic blocks.)

So how can we do this? Different authors call this a "reverse postorder"
or just a "depth-first ordering". For the latter term, see the "red
dragon" book: "Compilers: Principles, Techniques, and Tools", by Aho,
Sethi, and Ullman, pages 660-664. The "reverse postorder" terminology
seems to be more common today, and there's good background for it all
over the web; see for example the Wikipedia article on
[Data-flow analysis](https://en.wikipedia.org/wiki/Data-flow_analysis#The_order_matters).

As hinted by the name, we can efficiently compute the desired ordering
with a depth-first traversal of the control-flow graph. The general idea
is that once we've finished traversing all the successors of a block, we
can insert the block itself at the beginning of the ordering, because
that way it appears before its successors. Once we've inserted all nodes
into the list, we can assign successive labels to the blocks in the
newly-computed order.

An interesting thing happens if there's a basic block which is
unreachable from the start node: that block won't be visited in the
depth-first traversal, so it won't be assigned a new label. This
implementation has a bonus feature that it simply deletes unreachable
nodes.

```haskell
depthFirstOrder :: CFG k s c -> CFG DepthFirst s c
depthFirstOrder (CFG start blocks) = CFG start' blocks'
    where
    search label = do
        (seen, order) <- get
        unless (label `IntSet.member` seen) $ do
            put (IntSet.insert label seen, order)
            case IntMap.lookup label blocks of
                Just (BasicBlock _ term) -> traverse_ search term
                _ -> return ()
            modify (\ (seen', order') -> (seen', label : order'))
    final = snd (execState (search start) (IntSet.empty, []))
    start' = 0
    mapping = IntMap.fromList (zip final [start'..])
    rewrite label = IntMap.findWithDefault (error "basic block disappeared") label mapping
    rewriteBlock label (BasicBlock body term) = (label, BasicBlock body (fmap rewrite term))
    blocks' = IntMap.fromList (IntMap.elems (IntMap.intersectionWith rewriteBlock mapping blocks))
```


Dominators
----------

The "dominators" of a basic block are the blocks that you must pass
through to get there. For example:

- The entry node for the function dominates all blocks in the function,
  because you can't reach any node unless you pass through the entry
  node first.

- Every node dominates itself. That's a tautology: if you got there, you
  must have gotten there. (It's called "strictly dominating" if you
  don't include nodes dominating themselves.)

- The start of a loop dominates every block inside the loop body.

- In code like:

    ``` { .c .ignore }
    A;
    if(...)
        B;
    else
        C;
    D;
    ```

    `A` dominates all of `B`, `C`, and `D`. But `B` doesn't dominate
    `D`, because it's possible to reach `D` without passing through `B`
    by going through `C` instead; and similarly, `C` doesn't dominate
    `D`, because you could have gone through `B`.

- Dominance is transitive: If `A` dominates `B`, and `B` dominates `C`,
  then `A` also dominates `C`.

We'll use this information in several of the following algorithms so
we'll look at what it's useful for then. For now, how can we compute it?

The dominators for a block are the block itself, plus those nodes which
dominate all the predecessors of the block. Let's consider a few
cases...

- If there are no loops, then all of a block's predecessors have earlier
  labels in the depth-first ordering. That means that if we compute
  dominators in increasing order by label, we can be certain we have all
  the information we need by the time we get to each block.

- If there's a loop, but the only way to enter the loop is through a
  single node (usually called the "loop header"), then we can still
  compute dominators in increasing order by label. In this case, when we
  encounter predecessors that we haven't computed dominance for yet,
  that means those are branches to a loop header from somewhere inside
  the loop. A loop header dominates all blocks within the loop, and
  since dominance is transitive, everything that dominates the loop
  header also dominates every node within the loop. That means that
  nodes inside the loop can't remove any nodes from the set of
  dominators we'd compute by just using the earlier blocks' dominators,
  so we can ignore the later blocks.

- The only remaining possibility is if there's a loop that can be
  entered via two or more nodes, like this fragment of C:

    ``` { .c .ignore }
    if(...) goto b;
    for(;;) {
        step1();
    b:  step2();
    }
    ```

    In that case, neither entry block for the loop dominates the other,
    but computing dominators in depth-first order will assume that one
    of them is a loop header, leading to incorrect results. In compilers
    literature, this is called "irreducible control flow". For a classic
    example of this, check out Tom Duff's original 1983 e-mail about
    ["Duff's Device"](https://www.lysator.liu.se/c/duffs-device.html).

In that last case, we can tell the control flow is irreducible by making
a second pass of dominator computation over all the basic blocks, and
checking whether any of the results changed after having later nodes'
results available.

We can even compute the correct dominators by re-running the computation
repeatedly until the result stops changing. If control flow is
reducible, this will stop after two passes.

Many important data-flow analysis algorithms have trouble with
irreducible control flow, not just dominator computation, so there's
been lots written on the subject. But James Stanier and Des Watson's
2010 paper,
["A study of irreducibility in C programs"](http://onlinelibrary.wiley.com/doi/10.1002/spe.1059/abstract),
is of particular interest. They examined 15 open source projects which
together contained 1,709 "goto" statements. They found that out of
10,427 functions, only 5 had irreducible control flow! In practice, this
problem occurs extraordinarily rarely in real C programs.

Based on those statistics, and because deciding what to generate is hard
for irreducible control flow, we currently just detect this case here
and report an error so later steps can assume the input is reducible.

```haskell
type Dominators = IntMap.IntMap IntSet.IntSet

dominators :: CFG DepthFirst s c -> Either String Dominators
dominators cfg@(CFG start blocks) = case foldl go IntMap.empty (IntMap.keys blocks) of
    seen | all (check seen) (IntMap.keys blocks) -> Right seen
    _ -> Left "irreducible control flow"
    where
    update _ label | label == start = IntSet.singleton start
    update seen label = IntSet.insert label self
        where
        allPredecessors = predecessors cfg
        selfPredecessors = maybe [] IntSet.toList (IntMap.lookup label allPredecessors)
        predecessorDominators = mapMaybe (\ parent -> IntMap.lookup parent seen) selfPredecessors
        self = case predecessorDominators of
            [] -> IntSet.empty
            _ -> foldr1 IntSet.intersection predecessorDominators

    go seen label = IntMap.insert label (update seen label) seen
    check seen label = Just (update seen label) == IntMap.lookup label seen
```


Finding loops
-------------

To identify parts of the control-flow graph that represent loops, first
we find those branches that go "backward".

Each back-edge marks a loop where the loop header is the target of the
back-edge, but several back-edges may branch to the same loop header. So
we group back-edges by loop header.

> **FIXME**: Because we reject irreducible control flow while computing
> dominators, any "retreating edge" in the depth-first order is also a
> back-edge to a loop header, so we could simplify this to finding edges
> `(from, to)` where `to` is less than `from`. By contrast, this version
> is correct for the general case. Which is the right choice for
> pedagogy now? Which for a hypothetical future version that supports
> irreducible control flow?

```haskell
backEdges :: CFG k s c -> Dominators -> IntMap.IntMap IntSet.IntSet
backEdges cfg dom =
    IntMap.filter (not . IntSet.null) $
    IntMap.intersectionWith IntSet.intersection (flipEdges dom) $
    predecessors cfg
    where
    flipEdges :: IntMap.IntMap IntSet.IntSet -> IntMap.IntMap IntSet.IntSet
    flipEdges edges = IntMap.unionsWith IntSet.union [ IntMap.fromSet (const (IntSet.singleton from)) to | (from, to) <- IntMap.toList edges ]
```

Given the back-edges for a loop header, we can find the rest of the
blocks that are part of that same loop.

- The header is part of the loop.
- Add the back-edge sources to the loop.
- Aside from the header, for each node newly added to the loop, add its
  predecessors, unless they're already there.

```haskell
type NaturalLoops = IntMap.IntMap IntSet.IntSet

naturalLoops :: CFG k s c -> Dominators -> NaturalLoops
naturalLoops cfg dom = IntMap.mapWithKey makeLoop (backEdges cfg dom)
    where
    makeLoop header inside = execState (growLoop inside) (IntSet.singleton header)
    allPredecessors = predecessors cfg
    growLoop toAdd = do
        inLoop <- get
        let new = toAdd `IntSet.difference` inLoop
        unless (IntSet.null new) $ do
            put (inLoop `IntSet.union` new)
            growLoop (IntSet.unions (mapMaybe (\ label -> IntMap.lookup label allPredecessors) (IntSet.toList new)))
```


Finding loop exits
------------------

Once we know which blocks are loop headers and what blocks are in each
loop, we can find the branches that leave each loop. We'll translate
those as `break` statements if they go someplace after the loop, or
`continue` statements if they go backward to the beginning of the
current loop or an enclosing one.

For `break` statements, we need to note which loop to exit, and it needs
to be the outer-most loop that contains the `break` edge but does not
contain its target. But determining which is the inner loop and which is
the outer is extra work. Fortunately we don't actually need to do it.

If loop A encloses loop B, the loop header for A must come before the
header for B in a depth-first ordering. So visiting loops in depth-first
order is good enough; we don't have to work out how the loops are nested
first.

```haskell
data Exit = BreakFrom Label | Continue
    deriving Show
type Exits = Map.Map (Label, Label) Exit

exitEdges :: CFG DepthFirst s c -> NaturalLoops -> Exits
exitEdges (CFG _ blocks) = Map.unions . map eachLoop . IntMap.toList
    where
    successors = IntMap.map (\ (BasicBlock _ term) -> nub (toList term)) blocks
    eachLoop (header, nodes) = Map.fromList
        [ ((from, to), if to == header then Continue else BreakFrom header)
        | from <- IntSet.toList nodes
        , to <- IntMap.findWithDefault [] from successors
        , to == header || to `IntSet.notMember` nodes
        ]
```

A loop may have `break` edges to several different blocks, but we have
to pick just one block to place immediately after the loop. Fortunately,
either one of the candidates is reachable from all the others, or some
of them return early and it doesn't matter where we place them. Once
we've chosen a unique `break` target for a loop, we just need to mark
all of its in-loop predecessors as exits.

```haskell
unifyBreaks :: CFG DepthFirst s c -> NaturalLoops -> (IntMap.IntMap Label, Exits)
unifyBreaks cfg loops = (breaks, Map.fromList exits')
    where
    exits = exitEdges cfg loops
    (breakList, continues) = partitionEithers
        [ case exit of
            BreakFrom header -> Left (header, IntSet.singleton to)
            Continue -> Right orig
        | orig@((_, to), exit) <- Map.toList exits
        ]
    breaks = IntMap.map IntSet.findMax (IntMap.fromListWith IntSet.union breakList)
    breakExits header to = fromMaybe [] $ do
        candidates <- IntMap.lookup to (predecessors cfg)
        insideLoop <- IntMap.lookup header loops
        return (IntSet.toList (candidates `IntSet.intersection` insideLoop))
    exits' =
        [ ((from, to), BreakFrom header)
        | (header, to) <- IntMap.toList breaks
        , from <- breakExits header to
        ] ++ continues
```


Structuring the CFG
-------------------

With all the preliminary analyses out of the way, we're finally ready to
turn a control-flow graph back into a structured program full of loops
and `if`-statements!

Since we need various analysis results available throughout the
transformation, we'll just package them up into a new data type that we
can pass around using a `Reader` monad.

```haskell
data StructureInput = StructureInput
    { getDominators :: IntMap.IntMap IntSet.IntSet
    , getExits :: Exits
    , getLoops :: IntMap.IntMap (Maybe Label)
    }
```

Since this module is not language-specific, the caller needs to provide
functions for constructing `break`, `continue`, loop, and `if`
statements. The loop-related constructors take a label and generate a
loop name from it, to support multi-level exits.

```haskell
structureCFG
    :: Monoid s
    => (Label -> s)
    -> (Label -> s)
    -> (Label -> s -> s)
    -> (c -> s -> s -> s)
    -> CFG DepthFirst s c
    -> Either String s
structureCFG mkBreak mkContinue mkLoop mkIf cfg@(CFG start blocks) = runExcept $ do
    doms <- except $ dominators cfg
    let loops = naturalLoops cfg doms
    let (breaks, exits) = unifyBreaks cfg loops
    let input = StructureInput
            { getDominators = doms
            , getExits = exits
            , getLoops = IntMap.map Just breaks `IntMap.union` IntMap.map (const Nothing) loops
            }
```

Once we've computed all the analysis results, we walk backwards over all
the blocks, structuring them one at a time. By going in the opposite of
the depth-first ordering, we are guaranteed that when we structure a
block, all of the blocks it branches to have been
structured&mdash;except for back-edges to loop headers, which we handle
separately.

```haskell
    (final, _) <- RWS.execRWST (mapM_ doBlock (IntMap.toDescList blocks)) input IntMap.empty
```

Structuring should use every block exactly once. Considering that the
depth-first ordering already pruned any unreachable nodes, if there are
any left over then we did not reach all the nodes in the control-flow
graph.

```haskell
    case IntMap.toList final of
        [(label, (body, _))] | label == start -> return body
        pieces -> throwE $ "unconsumed blocks: " ++ show (map fst pieces)
    where
```

To structure a basic block, we need to combine the block body with `if`,
`break`, and `continue` statements as appropriate, and then wrap the
whole thing in a `loop` if this is a loop header.

Then we save the newly-structured block so that earlier nodes can
consume it.

```haskell
    doBlock (label, BasicBlock body term) = do
        loops <- RWS.asks getLoops
        (wrapped, reachable) <- RWS.listen $ do
            body' <- mappend body <$> doTerm label term
            case IntMap.lookup label loops of
                Nothing -> return body'
                Just breakTo -> do
                    after <- case breakTo of
                        Nothing -> return mempty
                        Just to -> join (consumeBlock label to)
                    return (mkLoop label body' `mappend` after)
        RWS.modify (IntMap.insert label (wrapped, IntSet.insert label reachable))
```

Consuming a block means looking it up in the blocks that have already
been structured, and then removing it. This lets us enforce a rule that
the structuring algorithm never duplicates code. If we try to consume a
block a second time, then it will no longer be available and we can
report an error.

We also check that the block we want to consume is dominated by the
block we're placing it after. This way we ensure we can't trigger the
"block isn't available" error, because we'll only place a block after
code that must execute in order to reach it.

```haskell
    consumeBlock from to = do
        input <- RWS.ask
        seen <- RWS.get
        case IntMap.lookup to seen of
            Nothing -> lift $ throwE $ "block " ++ show to ++ " isn't available from " ++ show from
            Just (body, reachable) -> do
                RWS.tell reachable
                return $ if from `IntSet.notMember` IntMap.findWithDefault IntSet.empty to (getDominators input)
                    then return mempty
                    else do
                        RWS.modify (IntMap.delete to)
                        return body
```

`consumeBlock` assumes you're sure you want that block. When we're
following branches from a terminator, though, we need to check if any of
those branches are exit edges. If so, that's not the time to structure
them; they'll get consumed later, when we process the loop's header,
instead. Meanwhile we should just construct a `break` or `continue`
statement.

```haskell
    followEdge from to = do
        input <- RWS.ask
        case Map.lookup (from, to) (getExits input) of
            Just (BreakFrom header) -> return (return (mkBreak header))
            Just Continue -> return (return (mkContinue to))
            Nothing -> consumeBlock from to
```

Translating an `Unreachable` or unconditional `Branch` terminator is
easy; there's either no code at all, or just the code from the next
block, respectively.

Conditional branches are trickier. We need to look at which blocks are
reachable from the true and false branches, respectively, to identify
one of these cases:

- Each branch goes to a different block, and one or both blocks end with
  a `return`, `break`, or `continue` statement.
- Each branch goes to a different block, and once both sides finish,
  control flow merges again. This should structure as an "if-then-else".
- One branch goes to a block that eventually branches to the same place
  as the other branch. This should produce an "if-then" statement with
  no "else", although the condition may have to be negated in the
  process.
- Both branches go to the same block. The condition should be evaluated
  for its side effects but the block should simply be placed, once,
  after that.

All of these come down to figuring out where control flow merges again
after the conditional branch, because that "join point" (if one exists)
should not be included in either branch of the conditional. If we did
include it, that would cause us to try to consume the join point twice,
leading to duplicate code at best.

```haskell
    doTerm _ Unreachable = return mempty
    doTerm label (Branch to) = join (followEdge label to)
    doTerm label (CondBranch c t f) = do
        (consumeT, tReachable) <- RWS.listen (followEdge label t)
        (consumeF, fReachable) <- RWS.listen (followEdge label f)
        let joinPoint = fmap fst (IntSet.minView (tReachable `IntSet.intersection` fReachable))
        let ifDisjoint consume l =
                if Just l /= joinPoint then consume else return mempty
        stmt <- mkIf c <$> ifDisjoint consumeT t <*> ifDisjoint consumeF f
        after <- case joinPoint of
            Just after -> join (consumeBlock label after)
            Nothing -> return mempty
        return (stmt `mappend` after)
```
