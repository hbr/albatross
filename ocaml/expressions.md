There are some difficulties in parsing expressions because other syntactic
entities look like expressions.


# Expressions and entity groups

E.g. the construct

    a,b,c:A, d,e,f:D

is a list of two entity groups and a list of expression. Note that `c:A` is an
expression (it is the identifier `c` converted to type `A`.

Possible solution: Don't let a mere identifier be an expression, let an
expression be a list of entity groups. I.e. the construct

    a,b,c:A, d,e,f:D, x+y

will be parsed until `f:D, x` as a list of entity groups. But by looking at
`+` it is evident that it can no longer be a list of entity groups.


# Right associativity

Sometimes it is convenient to parse the comma `,` as a right associative
operator in order to construct the lists without reversing them. I.e. the
construct

   a,b:A, x+y

gets parsed as

    (a,b:A) , (x + y)

I.e. with the parse tree

              comma
         exp          exp
        eglist         +
        colon        x    y
       comma A
       a   b



# Tagged expressions

Tagged expression are convenient in assertions like e.g.

    all(a,b:CURRENT)
        require
            r1: a=b
        check
            c1: a=a
            c2: a in {x:x=a}
            ...
        ensure
            b=a
        end

This creates another potential ambiguity. The parser on looking at `r1:`
cannot decide whether to reduce `r1` to an identifier list (because `r1:T` is
a valid entity list and therefore a valid expression) or to a tag.

A possible solution is to parse a tag like an identifier list and signal an
error as soon as the parser wants to reduce to a tagged expression with a list
with more than one identifier.


# Sets/predicates, local bindings

Moreover sets are defined with the `{x,y:T,z:U: expression}` notation. In this
case the 'tag' is a complete entity list. But sets can be defined as well with
enumeration `{x,y:T,z:U}` which can be at the same time an expression list
(i.e. an expression) or an entity list (note that `x,y:T,z:U` is an entity
list and an expression).

Possible solution:

* Differentiate between `tagged` (expression) and `expression`

Syntax of sets:

    set:
        "{" expression "}"
    |   "{" entity_list ":" expression "}" 

Tagged expressions can occur only in compounds (e.g. within assertion blocks
or implementation blocks).


# Process expressions

## Description of the problem

The original syntax for process expression is

    a -> b -> p               -- prefix notation

    x: a -> b -> x            -- anonymous process expression

The first one has the same syntax as function expressions. This implies that
the `->` operator has to be treated as a binary operator i.e. its left and
right hand side have to be general expressions and not special entity list (as
it would be possible for formal arguments of functions). Function expressions
and prefix expressions for processes cannot be distinguished during syntax
analyis. The type checker can distinguish both because it expects either a
function expression or a process expression. However it would be preferable if
the distinction could be done on the syntax level.

The anonymous process expression looks syntactically like a tagged
expression. Since the anonymous process expression is usually a subexpression
(e.g. `Process = x:a->b->x`) tagged expressions has to be allowed on all
levels of expressions. This clashes with the requirement that tagged
expressions are allowed only at the toplevel (e.g. assertions; see
above). This is not a grave problem, because the type checker can rule out all
unallowed tagged expressions.



## A possible solution on the syntax level

Prefix notation: Use another right associative operator for prefixes and
reserve `->` for function expressions. Examples

    a :: b :: p              -- list cons operator

    a ^ b ^ p                -- exponentiation operator


Advantage of the `::` operator: It plays a similar role for
lists. Disadvantage of both: `->` is more suggestive than `::` and `^`.

The anonymous process expression can be written like a function of the type
PROCESS->PROCESS, i.e.

    x -> a::b::x

is a function and there is a conversion from the type PROCESS->PROCESS to the
type PROCESS. With this syntax we usually get expressions in postconditions of
the form

    a   note event end
    b   note event end

    p
        ensure
            Process = (x -> a::b::x)
        end

This syntax opens up more actions. We can design a general function

    A: ANY

    fixpoint(f:A->A): A
        require
            f.has_unique_fixpoint
        ensure
            Result in f.fixpoints
        end

and use it in the process expression either explicitly

    p
        ensure
            Process = (x -> a::b::x).fixpoint
        end

or define a conversion function in the module `process`

    convert
        to_process(f:PROCESS->PROCESS): PROCESS
            require
                f.has_unique_fixpoint
            ensure
                Result = f.fixpoint
            end
    end


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
