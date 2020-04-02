# HOLiK
This repository contains an implementation of a symbolic game semantics for an ML-like language called HOLi in the K-Framework. The semantics implement a symbolic execution tool for HOLi, which serves as a proof of concept of symbolic execution for terms with free variables of arbitrary order (i.e. containing undefined code).

HOLi (**H**igher-**O**rder **Li**braries) is a simple ML-like language used as an idealised language for higher-order stateful libraries. In HOLi, one can implement libraries that define higher-order stateful methods, similar to OCaml and other functional languages with references. References in the language are global and higher-order, meaning that they may be called anywhere in the term, and may referencing methods.

## Organisation
In the `/HOLI` directory there are two files: 
- `HOLi.k` defines the syntax and symbolic game semantics for HOLi
- `z3.k` defines an interface between K and Z3 through system calls

## Installation

Prequisites:
- [Z3 binaries](https://github.com/Z3Prover/z3/releases) present in the PATH environment variable
- [K Framework Package](https://github.com/kframework/k/releases)

To compile, within `/HOLI`, run `kompile --backend java holi.k`. We currently only support the Java backend.

## Usage

Once compiled, use:
- `krun --search <file>` will output all final configurations in the computation tree of `<file>` reachable within the bound
- `krun --search --pattern <pattern> <file>` will output configurations as before, filtered by the pattern provided

e.g. `krun --search --pattern "<k> fail </k> <trace> T </trace>" <file>` finds all the traces that violate an assertion in file `<file>` and outputs the traces `T` that leads to the violation.
