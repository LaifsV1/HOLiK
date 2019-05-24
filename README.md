# HOLib-semantics
K-Framework semantics of HORef and HOLib for symbolic execution.

HORef and HOLib are toy languages used as a proof of concept for higher-order symbolic execution with free variables of arbitrary order.

- HoRef is a Higher-Order functional language with references.
- HOLib is a language to define libraries of higher-order stateful methods written in HORef.

In the `/HOREF` directory, we have the semantics to perform symbolic execution of higher-order open terms where free variables are of ground type. That is, symbolic execution of higher-order programs where no undefined methods are being called at compile time.

In the `/HOLIB` directory, we have the game semantics to perform symbolic execution of higher-order open methods, which may contain free variables of arbitrary order. That is, symbolic execution of libraries which may contain undefined methods. More concretely, given a library `L` wrriten in `HOLIB`, executing the `HOLIB` semantics will perform a bounded model checking to find whether it is possible to call `L` such that assertions are violated.

## Usage
For `HOLIB` we require `z3` to be present in the PATH environment variable.

To compile, inside either `/HOREF` or `/HOLIB`, run `kompile --backend java <holib/horef>.k`.

Once compiled, use `krun --search <file-to-check>` to perform symbolic execution.

For `HOLIB`, we can use `--pattern` to find traces that lead to an error.
e.g. `krun --search --pattern "<k> fail </k> <trace> T </trace>" programs/test2.holib` finds all the traces that violate an assertion in test file `test2.holib`
