# HOLiK
This repository contains the symbolic semantics for a language called HOLi implemented for the K-Framework. The purpose is to perform symbolic execution of HOLi.

HOLi (**H**igher-**O**rder **Li**braries) is a toy language used as a proof of concept for higher-order symbolic execution with free variables of arbitrary order. It is a language to define libraries of higher-order stateful methods written in HORef.

In the `/HOLI` directory, we have the game semantics to perform symbolic execution of higher-order open methods, which may contain free variables of arbitrary order. That is, symbolic execution of libraries which may contain undefined methods.

## Usage
For `HOLI` we require `z3` to be present in the PATH environment variable.

To compile, inside `/HOLI`, run `kompile --backend java holib.k`.

Once compiled, use `krun --search <file-to-check>` to perform symbolic execution.

We can use `--pattern` to find traces that lead to an error.
e.g. `krun --search --pattern "<k> fail </k> <trace> T </trace>" programs/<file>.holi` finds all the traces that violate an assertion in test file `<file>.holi`
