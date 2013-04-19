There are some difficulties in parsing expressions because other list of
formal arguments look like expressions.


# Formal arguments in function expressions

The list of formal arguments

    a:A, b:B

can be parsed as the expression `a` converted to type `A` and the expression
`b` converted to type `B`.

This is no problem in a function specification

    fun(a:A,b:B): RT ...

because no expression can be expected between the parentheses. However within
the function expression

    a:A,b:B -> a+b

the parser before seeing the `->` does expect expressions. Therefore within
the context of expressions the argument list `a:A,b:B` is parsed as an
expression. I.e. we have an expression on the left and on the right hand side
of the arrow and convert the lefthandside to an argument list.

# Formal arguments in sets (i.e. predicates)

Because of processes we have colon expressions. E.g.

    p: {a,b}: a::b::p

specifies a process with alphabet `{a,b}` and the prefix expression `a::b::p`.


Furthermore we have predicate expressions (i.e. sets) of the form

   {a:A,b:B: pred(a,b)}

specifying the set of all pairs `a,b` which satisfy the boolean valued
expression `pred(a,b)`.

And we allow singleton sets of the form

    {p: {a,b}: a::b::p}   -- illegal

being a set with one element which is a process. The last one is illegal in
this form, because `p : {a,b} : a::b::p` will be parsed as a colonexpression
treating the colon as a left associative binary operator. Then the left hand
side `p:{a,b}` of the outermost colon will be converted to an arguments list
which fails because it is no argument list.

A legal specification of a singleton set with one process look like

    {(p: {a,b}: a::b::p)}

In this form there is no possiblity to treat part of the expression as an
argument list.


# Tagged expressions

In assertions we allow tags to mark certain assertions.

    f(a:A): B
        require
            r1: pre_1
            r2: pre_2
            ...
        ensure
            Result = ...
        end

An ambiguity arises if the assertion on the right hand side of the colon
(i.e. after the tag) is a colon (e.g. a process expression)

    r1: p: {a,b}: a::b::p = proc

The compiler will issue the error message `r:p:{a,b}` is not a valid tag. In
order to disambiguate parentheses are necessary.


    r1: (p: {a,b}: a::b::p) = proc



# Function expressions and function types

The argument list

    a,b:A,c,d:C

is parsed as an expression and converted to an entitylist. This is possible
because `a:A` is a perfect expression, it is the expression `a` converted to
type `A`. I.e. argument lists look like expressions and have therefore a
common parsing construct.

But we get the following ambiguity:

    f:A->exp
    f:A->A

The parser of seeing `f:A->` cannot decide whether to reduce `f:A` to an
expression (which is an argument list in this case or to shift the `->` and
expect to see the result type of the function type `A->A`.

Solution: We first parse an expression with arrow e.g. `x->`, `x,y->`,
`f:A->`, `a,f:A->`. The next can be another expression or a type. In case of
an expression we get a function expression, in case of a type we get a
function type.




<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
