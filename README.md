KLEE Symbolic Virtual Machine
=============================

[![Build Status](https://travis-ci.org/klee/klee.svg?branch=master)](https://travis-ci.org/klee/klee)
[![Coverage](https://codecov.io/gh/klee/klee/branch/master/graph/badge.svg)](https://codecov.io/gh/klee/klee)

`KLEE` is a symbolic virtual machine built on top of the LLVM compiler
infrastructure. Currently, there are two primary components:

  1. The core symbolic virtual machine engine; this is responsible for
     executing LLVM bitcode modules with support for symbolic
     values. This is comprised of the code in lib/.

  2. A POSIX/Linux emulation layer oriented towards supporting uClibc,
     with additional support for making parts of the operating system
     environment symbolic.

Additionally, there is a simple library for replaying computed inputs
on native code (for closed programs). There is also a more complicated
infrastructure for replaying the inputs generated for the POSIX/Linux
emulation layer, which handles running native programs in an
environment that matches a computed test input, including setting up
files, pipes, environment variables, and passing command line
arguments.

For further information, see the [webpage](http://klee.github.io/).
# Concolic_klee

In our implementation of concolic execution, we first record the trace
of running KLEE with concrete input, then direct the symbolic executor
using the concrete path. In the first run, we record every branch
encountered and log information such as the program counter, branch
conditions, and source code line. We then re-run KLEE with symbolic
input and follow the concrete trace to create constraint sets for each
step. We modified the `Executor::fork function` so that instead
of actually forking, KLEE picks the successor state that corresponds to
the next entry in the trace. When KLEE reaches the memory bug, KLEE will
send the constraint sets to the solver. If the solver raises an error
state, it means that KLEE would be able to find the bug, if given
sufficient time to search all paths. Otherwise, we mark the bug as
missed, meaning that KLEE's environment model or execution were not
sufficient to uncover the bug.

We ignore paths in all libc functions during replay and assume that they behave the same,
despite the difference between symbolic and concrete environment. An 
exception is the compare functions, e.g. strcmp, memcmp, 
etc. Concolic KLEE replay follows the branch conditions in such functions
because they do not involve the environment and are essential for computing the correct path conditions.
