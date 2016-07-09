# Corrode: Automatic semantics-preserving translation from C to Rust

This program reads a C source file and prints an equivalent module in
Rust syntax. It's intended to be useful for two different purposes:

1. Partial automation for migrating legacy code that was implemented in
   C. (This tool does not fully automate the job because its output is
   only as safe as the input was; you should clean up the output
   afterward to use Rust features and idioms where appropriate.)

2. A new, complementary approach to static analysis for C programs. If
   this program can't translate your C source to equivalent Rust, you
   might consider whether your program is too complicated and hiding
   bugs. Or, if translation succeeds, the Rust compiler may report
   warnings and errors that your C compiler misses, or you may be able
   to use a custom Rust linter to detect project-specific problems.

## Quick Start

As of now, there are no pre-built binaries available, so you need to build the
project yourself, but don't let that scare you away; clone the project, `cd`
into it and follow along :)

The easiest way to build the project is to use the
[Haskell Stack](http://haskellstack.org) tool. If you don't have it, head over
to their website and follow the instructions for installing it on your machine.

Install the Glasgow Haskell Compiler using ```stack setup```. You can skip this
step if you already have a version of GHC installed your system.

To build and install `corrode`, run:

```
stack install
```

Stack will build and install `corrode` to `~/.local/bin`. For ease of use, make
sure that directory is in your `$PATH`.

You can now run `corrode`, giving it any options that `gcc` would
accept.

```
corrode -Wall filename.c -I/usr/local/include -lm
```

It will only use the options that are relevant to the C pre-processor,
like `-I` or `-D`, but since it accepts and ignores any other options,
you can usually hack it into existing build systems just by setting
`CC=corrode`.

However, unlike a real C compiler, Corrode does not produce an object
file or executable! Instead, if you ask it to process `filename.c`, it
generates equivalent Rust source code in `filename.rs`. At the moment,
it's up to you to invoke `rustc` on the output with appropriate options
to finish compilation.

To experiment with the project itself, you can build it using

```
stack build
```

then run the executable:

```bash
stack exec -- corrode -Wall filename.c -I/usr/local/include -lm
```

## Design principles

Corrode aims to produce Rust source code which behaves exactly the same
way that the original C source behaved, if the input is free of
undefined and implementation-defined behavior.

At the same time, Corrode should produce code which is recognizably
structured like the original. Every statement and every expression
should be represented in the output&mdash;in the same order, where
possible. If a programmer went to the trouble to put something in, I
want it in the translated output; if it's not necessary, we can let the
Rust compiler warn about it.

In the presence of undefined behavior, I've tried to pick a behavior
that isn't too surprising and preserves the structure of the input
program. For example, if a signed addition might overflow (which is
undefined behavior in C), Corrode just translates it to Rust's `+`
operator, which panics on overflow in debug builds.

## Testing

So far, Corrode has primarily been tested by generating random C
programs using [csmith](https://github.com/csmith-project/csmith),
fixing Corrode until it can handle all syntax used in that particular
program, and verifying that the resulting Rust module compiles without
errors.

Because the project is still in its early phases, it is not yet possible
to translate most real C programs or libraries. But if you have one you
particularly want to try out, I'd love to get pull requests implementing
more of C!

## Contributing

If this seems cool and you'd like to help complete it, welcome! There
are quite a few fundamental pieces of the C standard which are not yet
implemented. I'm trying to keep track of good starting projects as
[issues with the 'Easy' label](https://github.com/jameysharp/corrode/issues?q=is%3Aissue+is%3Aopen+label%3Aeasy).

"Easy" is, of course, a relative term in a project mashing together C's
complicated semantics with Rust's not-fully-documented semantics and all
implemented in Haskell. I'd love to chat with you if you're not quite
sure how to get started! You can e-mail me at
<mailto:jamey@minilop.net>.

## Future directions

A Rust module that exactly captures the semantics of a C source file is
a Rust module that doesn't look very much like Rust. ;-) I would like to
build a companion tool which rewrites parts of a valid Rust program in
ways that have the same result but make use of Rust idioms. I think it
should be separate from this tool because I expect it to be useful for
other folks, not just users of Corrode. I propose to call that program
"idiomatic", and I think it should be written in Rust using the Rust AST
from [`syntex_syntax`](https://github.com/serde-rs/syntex).

Verifying that the translated output is equivalent to the input is not
trivial. One approach I think is worth trying is to use the Galois
[Software Analysis Workbench](http://saw.galois.com/) to prove that the
LLVM bitcode generated from `clang` on a C source file is equivalent to
the LLVM bitcode generated from `rustc` on a Rust source file from
Corrode. SAW uses a symbolic simulator over LLVM bitcode to extract
logical formulas representing the behavior of each function, and then
uses an SMT solver to prove equivalence between pairs of formulas.
Generating large numbers of random C programs using csmith and then
proving the translation results equivalent for each one should give
pretty good confidence in the implementation.
