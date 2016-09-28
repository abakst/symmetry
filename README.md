# Symmetry  [![Build Status](https://travis-ci.org/abakst/symmetry.svg?branch=prolog-out)](https://travis-ci.org/abakst/symmetry)
Protocol verifier for message passing programs.

This package defines a DSL for writing message passing programs. In theory, programs written in this DSL
may be evaluated in one of two ways:

  1. "As normal", e.g. compilation to Cloud Haskell
  2. "For verification", e.g. analyzed to determine if the underlying communication protocol is well formed

In practice, only "2" is currently implemented.

# How to use

The programmer writes a program in the DSL (Symmetry.Language.AST).

By way of example, assume the file `Prog.hs` contains the following:

~~~~{.haskell}
module Main where

import Symmetry.Language
import Symmetry.Verify

mainProc = {- The program in the DSL -}

main :: IO ()
main = checkerMain mainProc
~~~~

The programmer then compiles the program as normal:

~~~~
$ ghc Prog.hs -o Prog
~~~~

To run the verification, run:

~~~~
$ ./Prog --rewrite
~~~~

## What's going on

`./Prog --rewrite`:

  1. creates a first-order abstraction (as a Prolog program) `symverify.pl` in `$CWD/.symcheck`;
  2. checks to see if the Prolog model can be rewritten into a canonical trace

If (2) succeeds, then `Prog` is deadlock-free and no assertion fails at runtime.
  
`./Proc --dump-process`:

   * Prints a representation of the message-passing protocol from `Prog.hs`.

`./Proc --dump-model`:

   * Write the files that `Liquid Haskell` or `QuickCheck` would inspect, but do not actually run them.


# Useful Model-Checking Papers

* Lamport TLA
  [http://research.microsoft.com/pubs/64074/lamport-actions.pdf]
  
* Jhala & Majumdar 
  [http://goto.ucsd.edu/~rjhala/papers/software_model_checking_survey.pdf]
  
* (0,1,infinity) counter abstraction
  [http://link.springer.com/chapter/10.1007%2F3-540-45657-0_9]
