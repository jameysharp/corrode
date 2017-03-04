# Corrode: Automatic semantics-preserving translation from C to Rust

[![Build Status](https://travis-ci.org/jameysharp/corrode.svg?branch=master)](https://travis-ci.org/jameysharp/corrode)

This program reads a C source file and prints an equivalent module in
Rust syntax. It's intended for partial automation of migrating legacy
code that was implemented in C. This tool does not fully automate the
job because its output is only as safe as the input was; you should
clean up the output afterward to use Rust features and idioms where
appropriate.

## Quick Start

As of now, there are no pre-built binaries available, so you need to build the
project yourself, but don't let that scare you away; clone the project, `cd`
into it and follow along :)

### Windows

If you're using Windows, start by running `fixGitSymlinksForWindows.bat`
as admin (this is necessary for Git to create symlinks).

### Cabal

Ensure that you have GHC and the `cabal-install` tool installed by following
the [directions on haskell.org](https://www.haskell.org/downloads#minimal).
You'll also need to have the `happy` and `alex` tools available in order to
build `corrode`: you can install them with the `cabal-install` tool, as well.
Once you have installed the `cabal-install` tool, you can build `corrode` by
navigating to the `corrode` directory, installing the `happy` and `alex` tools,
and then building and installing the `corrode` package:

```
cabal install happy
cabal install alex
cabal install
```

This puts the `corrode` executable in `~/.cabal/bin`, so ensure that that
location is in your `$PATH`.

### Alternate instructions: Stack

Alternately, you can use the [Haskell Stack](http://haskellstack.org) tool
for Haskell development. If you don't have it, head over to their website
and follow the instructions for installing it on your machine.

Install the Glasgow Haskell Compiler using ```stack setup```. You can skip this
step if you already have a version of GHC installed on your system.
You can then build and install `corrode` by navigating to the `corrode`
directory and running:

```
stack install
```

Stack will build and install `corrode` to `~/.local/bin`. For ease of use, make
sure that directory is in your `$PATH`.

To experiment with the project itself, you can build it using

```
stack build
```

then run the executable:

```bash
stack exec -- corrode -Wall filename.c -I/usr/local/include -lm
```

## Usage

There are two ways to use Corrode. You can simply generate a `.rs` file
from the C source, or you can do this _and_ compile in one step.

### Generating Rust source

You can now run `corrode`, giving it any options that `gcc` would
accept.

```
corrode -Wall filename.c -I/usr/local/include -lm
```

It will only use the options that are relevant to the C pre-processor,
like `-I` or `-D`, but since it accepts and ignores any other options,
you can usually get going just by changing `gcc` to `corrode` in the
`gcc` invocation you've been using.

Unlike a real C compiler, Corrode does not produce an object file or
executable! Instead, if you ask it to process `filename.c`, it generates
equivalent Rust source code in `filename.rs`. If you _do_ want object
code, there is a script to help with that.

### Codegen with compilation

You can either invoke `rustc` on Corrode's output yourself (or import it
into a Rust project), or use the `scripts/corrode-cc` tool in place of
`gcc` to compile and link. In many build systems, such as `make`, you
can simply set `CC=corrode-cc` without modification.

## Design principles

The overarching goal of Corrode is to preserve the original properties
of the source program as much as possible: behavior, ABI compatibility,
and maintainability. We expect the output of Corrode to be used to
replace the original C, not just as an intermediate step in a compiler
toolchain.

Corrode aims to produce Rust source code which behaves exactly the same
way that the original C source behaved, if the input is free of
undefined and implementation-defined behavior. In the presence of
undefined behavior, we've tried to pick a behavior that isn't too
surprising. For example, if a signed addition might overflow (which is
undefined behavior in C), Corrode just translates it to Rust's `+`
operator, which panics on overflow in debug builds.

The compiled Rust source in turn will be ABI-compatible with the
original C. If you compile Corrode-generated Rust to a `.o` file, you
can link to it exactly as if it were generated from the original C.
Every function that Corrode generates with be annotated with the `extern
"C"` modifier.

At the same time, Corrode should produce code which is recognizably
structured like the original, so that the output is as maintainable as
the original. Every statement and every expression should be represented
in the output&mdash;in the same order, where possible. If a programmer
went to the trouble to put something in, we usually want it in the
translated output; if it's not necessary, we can let the Rust compiler
warn about it.

If either behavior or ABI is not preserved, we consider that a bug in
Corrode. However, it is not always possible to preserve the structure of
the original code, so we do the best that we can.

## Testing

So far, Corrode has primarily been tested by generating random C
programs using [csmith](https://github.com/csmith-project/csmith),
fixing Corrode until it can handle all syntax used in that particular
program, and verifying that the resulting Rust module compiles without
errors.

Verifying that the translated output is equivalent to the input is not
trivial. One approach I think is worth trying is to use the
Galois [Software Analysis Workbench](http://saw.galois.com/) to prove
that the LLVM bitcode generated from `clang` on a C source file is
equivalent to the LLVM bitcode generated from `rustc` on a Rust source
file from Corrode. SAW uses a symbolic simulator over LLVM bitcode to
extract logical formulas representing the behavior of each function, and
then uses an SMT solver to prove equivalence between pairs of formulas.
Generating large numbers of random C programs using csmith and then
proving the translation results equivalent for each one should give
pretty good confidence in the implementation.

Because the project is still in its early phases, it is not yet possible
to translate most real C programs or libraries. But if you have one you
particularly want to try out, I'd love to get pull requests implementing
more of C!

## Contributing

If this seems cool and you'd like to help complete it, welcome! There
are quite a few fundamental pieces of the C standard which are not yet
implemented. I'd love to chat with you if you're not quite sure how to
get started! You can e-mail me at <mailto:jamey@minilop.net>.

## What Corrode is not

A Rust module that exactly captures the semantics of a C source file is
a Rust module that doesn't look very much like Rust. ;-) I would like to
build a companion tool which rewrites parts of a valid Rust program in
ways that have the same result but make use of Rust idioms. I think it
should be separate from this tool because I expect it to be useful for
other folks, not just users of Corrode. I propose to call that program
"idiomatic", and I think it should be written in Rust using the Rust AST
from [`syntex_syntax`](https://github.com/serde-rs/syntex).
