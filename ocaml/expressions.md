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
cannot decide whether to reduce `r1` to an indentifier list (because `r1:T` is
a valid expression) or to a tag.

A possible solution is to parse a tag like an identifier list and signal an
error as soon as the parser wants to reduce to a tagged expression with a list
with more than one identifier.


# Sets/predicates

Moreover sets are defined with the `{x,y:T,z:U: expression}` notation. In this
case the 'tag' is a complete entity list. But sets can be defined as well with
enumeration `{x,y:T,z:U}` which can be at the same time an expression list
(i.e. an expression) or an entity list (note that `x,y:T,z:U` is an entity
list and an expression).


<!---
comment
-->
