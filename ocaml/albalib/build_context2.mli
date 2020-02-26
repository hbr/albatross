type t

(**

A build context consists of a context with holes and a stack of to be
constructed terms.

There is always a next to be constructed term. The term is either in a function
position or an argument position.

*)


val make: Gamma.t -> t
(**
    [make gamma]

    Make a build context based on [gamma]. Push 2 holes onto the context to get

    Gamma, E: Any(2), e: E

    The next to be constructed term points to [e].
*)


val final:
        t
        -> (Term.t * Term.typ, Term.t list * Term.t * Term.typ * Gamma.t) result


(** {1 Terminals } *)

val base_candidate: Term.t -> int -> t -> t option
(**
    [base_candidate term nargs bc]

    Receive the term [term] as a candidate for the next to be constructed term.
    The candidate is from the base context and in applied to [nargs] arguments.

    Base candidates are either

    - Literals (Numbers, characters, strings)

    - Variables from the base context
*)




(*
val candidate: Term.t -> t -> t option
(**
    [candidate term bc]

    Receive the term [term] as a candidate for the next to be constructed term.

    Candidates are either

    - Base candidates

    - Bound variables


New placeholder for implicit arguments have to be generated in case that the
required type is not just a placeholder. The candidate term has to be applied to
the implicit arguments before assigning it to the next to be constructed term.

*)
*)




(** {1 Function Application [f a b c ... ]}

{[
    start_application nargs bc
    ...                    (* process function term *)
    expect_argument bc
    ...                    (* process argument a *)
    expect_argument bc
    ...                    (* process argument b *)
    ...
    end_application bc
]}

*)
(*
val expect_application: int -> t -> t
(**
    [expect_applicition nargs bc]

    Expect a function application with [nargs] arguments as the next term
    to be constructed.

    For each argument introduce one placeholder for the function term and one
    for the argument term and one placeholder for the corresponding types.

{[

    Syntactic expression:  f a b c

    stack = f  a   g   b   h   c   e
]}
*)
*)


(*
val expect_argument: t -> t
(**
[expect_argument bc]

Expect the next argument of the function application.

If [n] arguments have already been received, the top of the stack points to the
function term applied to [n] arguments plus potential implicit arguments to be
applied before the next argument. The type of the next argument has already been
unified.
{v
    A: Any1, a: A, F: A -> Any1, f: all (x: A): F x
v}
{[
before:  stack = f a e ...

assign   e := f a i0 i1 ...

after:   stack = a e ...
]}
*)
*)



(** {1 Function Abstraction [\ x y ... := t]}

{[
    start_function nargs bc
    ...                      (* process formal argument type *)
    end_formal_argument bc
    ...                      (* process formal argument type *)
    end_formal_argument bc
    ...                      (* process result type *)
    end_result_type bc
    ...                      (* process inner term *)
    end_function bc
]}
*)

(*
val start_function: int -> t -> t

val end_formal_argument: t -> t

val end_result_type: t -> t

val end_function: t -> t
*)



