Thank you for your interest in contributing to Corrode!

Kinds of Contributions
======================

This project has a goal of being useful and correct, but it also has a
goal of being helpful for learning. So I value many kinds of
contributions!

- Code improvements
- Bug reports
- Tests or other verification tools
- And documentation improvements!

One of the most valuable contributions you could make is to read through
any part of the code, take notes on anything you find confusing, and
ideally, come up with a better way to explain those confusing parts.

Reporting Bugs
==============

Corrode has plenty of bugs, and I want to know about them!

Bugs in Corrode can show up either

- by reporting an error message that it shouldn't have,
- or by successfully generating Rust source, but the generated Rust
  doesn't compile or produces the wrong result.

Before reporting a bug, please check:

1. Does the C source you're testing compile successfully, and produce
   the result you expected, when compiled with GCC or Clang? If not,
   then you should figure out what those compilers think your code means
   first. You may have found a case where the C standard is stupid,
   which would not count as a bug in Corrode.

1. Has this bug already been reported? There are quite a few known bugs
   in Corrode and it's worth taking a moment to search the GitHub issues
   list to see if anything is related.

Once you've checked those things, open a new issue on GitHub. In your
bug report, please clearly explain:

1. What did you try to do? For example, include the smallest C source
   code you can come up with that triggers the bug.
1. What result did you expect to see?
1. What result did you actually get?

I like Simon Tatham's essay on [How to Report Bugs
Effectively](http://www.chiark.greenend.org.uk/~sgtatham/bugs.html).

At your option, if you can see how to fix the bug you've found, you can
choose to open a pull request suggesting a fix without opening a
separate issue first.

Pull Requests
=============

Some project maintainers are picky about the contents of individual
commits. By contrast, I'm just delighted you want to contribute and I'd
like to make it as easy as possible for you to make your mark on
Corrode.

For example: Please don't use `git rebase` on your pull requests. I'm
not interested in Linux kernel style "perfect" patches&mdash;I'm going
to review your patches, but you're unlikely to write something I can't
follow regardless of how "messy" your commit history is&mdash;and rebase
loses information that I find valuable about the development history
that led up to your pull request. (See [Perspectives on Commit
History](http://jamey.thesharps.us/2016/05/perspectives-on-commit-history.html)
for more.)

I encourage you to submit an initial pull request as soon as you have
something kind of working, even if you know there are problems, so I can
review it and give you feedback as early as possible. (See [The Gentle
Art of Patch
Review](http://sarah.thesharps.us/2014/09/01/the-gentle-art-of-patch-review/)
for some observations from a maintainer's perspective on this.)

I'm not picky about code style. It's nice if you can follow the style
used in the rest of the code, but I'm not likely to reject your patches
because of code style. I do have a couple of very general guidelines I'd
appreciate if you could follow:

- I'd like line lengths to be below, oh, something like 85 or 90
  characters, because apparently that's how much Pandoc can fit inside
  1-inch margins on US-Letter paper. I discovered this after writing a
  bunch of code so there are still some lines that are longer.

- I don't like having lines indented based on how long things are on a
  previous line:

    ```haskell
    reallyLongName :: a
                   -> b
    ```

    because if you rename `reallyLongName` then you have to re-indent
    all the lines after it, which leads to giant diffs where it's hard
    to spot the real changes. So I generally try to indent exactly four
    spaces anywhere that I need to indent.
