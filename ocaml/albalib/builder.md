# Invariant

After the analysis of a syntactic term, all generated placeholders have got a
substitution.



# Function type "all (x: A) (y: B)  ... : RT"

- Variables can be untyped, the return type must be given.

- Untyped variables must occur in the remaining argument types or in the result
  type.

- Each argument type and the return type get a new placeholder. The placeholder
  is substituted by the analyzed expression for the type, if there is one.

- The types of untyped variables get a substitution, however the substitution
  term might be another placeholder.

Error condition: Some argument types are either unsubstituted or substituted by
some other new placeholder.


Condition after analysis of the argument types and the return type.

    Gamma,
    [A]: Any 1,
    x: [A],
    ...             -- Analysis of A
    [B]: Any 1,
    y: B,
    ...             -- Analysis of B
    ...,
    [RT]: Any 1
    ...             -- Analysis of RT

    One placeholder for each argument type and for the result type.


Check if all placeholders for the argument types have got a nontrivial
substitution. A substitution by placeholder above is a trivial substitution.


Example of a case where some argument types get just a trivial substitution.

    all a b: a = b

Since `(=)` has the type `all (A: Any): A -> A -> Proposition`, the subterm `a =
b` generates a placeholder for `A` which substitutes the types of `a` and `b`.
Since `A` is not unified with other types, the substitution for the types of `a`
and `b` remain trivial.




Note: The placeholder for the return type is guaranteed to have a nontrivial
substitution.

Error condition:

>  At least one placeholder for an argument type does not have a nontrivial
   substitution.

   => Report: "Cannot infer a type for the variable."

Success:

>   The invariant guarantees that there are no new placeholders which do not
    have a substitution.

- Generate the term "all (x: [A]) (y: [B]) .... : [RT]"
- Substitute all placeholders
- Unify its type (which must be either Any or Proposition) with the required
  result type of the whole expression.
- Assign the generated term to its placeholder.


## Correct generation of `all (x: [A]) (y: [B]) .... : [RT]`

After analyis of the syntactic expression the context looks like

    Gamma = ..., A: Any 1, x: A, ..., B: Any 1, y: B, ..., RT: Any 1, ...

    stack = RT, ..., B, A, ...

The entries on the stack are references to the corresponding absolute positions
in `Gammma`.

Potential problem: The bound variable `x` might occur in `B`, ..., `RT`.
Therefore in the types `A`, `B`, ... `RT` we must substitute the bound variables
by the correct bound variables.

We work with an array of optional pointers for each entry starting at `A`.

    arguments : [ ., 0, ..., 1, ...]

where 0, 1, ... point to the corresponding argument and `.` are void entries.
