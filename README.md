# Many-SMT
This is an [SMT-LIB](http://smtlib.cs.uiowa.edu/) frontend that runs multiple
backend solvers in parallel, returning the first result.  Like an ordinary
SMT-LIB solver, it accepts SMT-LIB v2.6 input on stdin and writes output to
stdout.

Currently, Many-SMT knows how to use
[Boolector](https://boolector.github.io/),
[CVC4](https://cvc4.github.io/),
[Yices](https://yices.csl.sri.com/), and
[Z3](https://github.com/Z3Prover/z3).

Pull requests are welcome!

## Use/Install

The script requires [Python 3](https://www.python.org/).  It has no
dependencies beyond the Python 3 standard libraries.

The script is small enough to be entirely self-contained.  You can use it
directly out of this folder:

    ./many-smt <test.smt2

Or install it by copying it to a folder on your PATH.

## Details and Caveats

On startup, Many-SMT spawns multiple solver processes.  Using separate
processes has advantages over using libraries:

 - ManySMT is insulated from memory corruption and resource leaks in the
   underlying solvers.
 - ManySMT discovers available solvers dynamically, and requires no
   configuration or compilation.
 - ManySMT itself is single-threaded and very simple.  It uses I/O multiplexing
   to interact with multiple solvers concurrently.

When you write a complete command to stdin, Many-SMT broadcasts that command
to all the underlying solvers.  Solvers that return an error are killed, and
others continue running.  When this happens, Many-SMT writes a message to
stderr to help you diagnose the problem.  Many-SMT returns an error when no
more solvers are left running.

Some commands are handled specially:

 - `(check-sat)` and `(check-sat-assuming ...)` are sent to all solvers, but
   ManySMT returns as quickly as possible the first non-unknown non-error
   output by any of them.  The other solvers are quietly interrupted (using
   SIGKILL, restart, and replay).
 - Inspection commands (`get-value`, `get-assignment`, `get-model`,
   `get-unsat-assumptions`, `get-proof`, and `get-unsat-core`) are only sent to
   the solver that returned from the most recent `(check-sat*)` command.  That
   solver's output is returned unaltered.  Because different solvers output
   models in different formats, the output of these commands can be surprising!

Different solvers have different default sets of options.  For example, CVC4
starts with `:produce-models` false while Z3 starts with it true.  It is a good
idea to explicitly set options to insulate yourself from these differences.

## Similar Projects

[metaSMT](https://github.com/agra-uni-bremen/metaSMT) abstracts over multiple
solvers, but it is a library and not a tool that takes SMT-LIB input.

[Par4](https://smt-comp.github.io/2019/participants/par4) is exactly the same
idea, but does not seem to be publicly available.

[Poolector](https://github.com/Boolector/boolector/blob/ad16fd1b47fdce57cc55ca5f1b2f4f7c95b2f631/contrib/poolector.py)
is exactly the same idea, but only runs instances of the Boolector solver and
does not support interaction.
