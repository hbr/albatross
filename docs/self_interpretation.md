Language Definition
===================


Definition:

>   A language `L = (P, eval)` consists of a set `P` of programs where `P` is a
>   subset of the natural numbers and an evaluation function

>       eval: P x N -> N

>   which is a partial function. It is decidable, if a natural number is a
    program, i.e. there is a computable function valid: `N -> {0,1}` where `valid
    (n) = 1` means that `n` is a valid program.

We define programs in the domain of natural numbers. This is not a restriction,
because every file or collection of files can be interpreted as a natural
number, because they are sequence of bytes and every sequence of bytes can be
mapped one-to-one to a natural number.

Furthermore we consider only functions from natural numbers to natural numbers.
This is not a restriction either for the same argument.

Note that partial functions are functional relations, i.e. `r n m1` and
`r n m2` imply `m1 = m2` when `r` is a functional relation. A relation is left
total, if for all `x` in its domain there is a `y` such that `r x y`. Therefore
a functional, left-total relation represents a function.

Definition:

>   A language is total, if its evaluation function is total.




Implementation of Functions
===========================

Definition:

>   Assume a language `L = (P,eval)`. We say that an `F in P` implements a
>   function `f: N -> N`, if

>       eval(F, m) = f(m)

>   for all `m in N`.


Definition:

> A language `L = (P, eval)` is closed under composition if for all functions
> `f` and `g` which it implements, it implements the composition of the
> functions `f` and `g` as well.





Interpretation of a Language
============================

Definition:

>   Assume two languages `L1 = (P1, eval1)` and `L2 = (P2, eval2)`. We say that
>   `L1` *interprets* `L2` if there is an interpreter program `u` in `P1` such
>   that

>       eval1(u, <n,m>) ~ eval2(n, m)

>   for all valid programs `n` in `P2` and `m` in `N`.


In this definition we use a pairing function `<n,m>` which maps each pair of
natural numbers one-to-one into a natural number.

Furthermore we don't use equality in this definition. We use equivalence. I.e.
if `eval1(u, <n,m>)` is undefined, then `eval2(n, m)` is undefined as well and
vice versa. If both functions are defined for the arguments, then they
return the same value.


A language `L = (P, eval)` interprets itself, if it has an interpreter program
`u` such that

    eval(u, <n,m>) ~ eval(n, m)

for all valid programs `n`.





Total Languages cannot interpret themselves
===========================================


In the following we prove the fact that a total language cannot interpret
itself as long as it implements at least the successor function and the diagonal
function and is closed under composition.

Assume that `L = (P, eval)` is a total function which has an interpreter program
`u` which implements self interpretation.

Therefore we get for all valid programs `n` and all natural numbers `m`

    eval(u, <n,m>) = eval(n,m)

Here we have equality, because being a total language the evaluation function is
total.

According to our definitions, the program `u` implements the function

    x |-> eval(u, x)

because of the triviality

    eval (u, x) = eval(u, x)

Furthermore we have the programs `succ` and `diag` such that

    eval(succ, m) = m + 1

    eval(diag, m) = <m,m>

Now we define a function `f: N -> N` as

    f(k) := 1 + eval(u, <k,k>)

In that definition it is crucial, that the language is total. Therefore `eval`
is total and the above definition is a valid function definition. If the
language were not total, the above definition of `f` would be illegal.

Because the language is closed under composition, there is a program `F` such
that

    eval(F, k) = f(k)

for all natural numbers `k`.

Now we form `eval(u, <F,F>)` and get

    eval(u, <F,F>)

    = eval(F, F)            -- `u` is interpreter program

    = f(F)                  -- `F` implements `f`

    = 1 + eval(u, <F,F>)    -- definition of `f`

This is a contradiction because a number and its successor cannot be equal.
Therefore our assumptions are wrong and either the language `L` is not total or
the language does not interpret itself.
