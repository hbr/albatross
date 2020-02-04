type t




val make: Gamma.t -> t

val final: t -> Term.t * Term.typ * Gamma.t


val expect_type: t -> t
(**
    [expect_type bc]

    Expect a type as the next term to be constructed i.e. push a new element
    onto the stack whose required type is [Any(1)].
*)


val expect_typed: t -> t
(**
    [expect_typed bc]

    Expect a term whose type conforms to the previously constructed type.
*)



val expect_untyped: t -> t
(**
    [expect_untyped bc]

    Expect a term whose type is not known and must be inferred. I.e. we have to
    add a hole of [Any(1)] and make this new type variable the expected type of
    the term.
*)





val expect_function: int -> t -> t
(**
    [expect_function nargs bc]

    Expect a function which can be applied to [nargs] arguments as the next term
    to be constructed.

*)




val receive_base_candidate: Term.t -> t -> t option
(**
    [receive_base_candidate term bc]

    Receive the term [term] as a candidate for the next to be constructed term.
    The candidate is from the base context.

    In case of success set the next to be constructed term to the status
    constructed.

    In case of failure return [None].
*)



val base:           t -> Gamma.t
val required_type:  t -> Term.typ
val built_type:     t -> Term.typ

val candidate:      Term.t -> t -> t option
val pop: t -> Term.t * t

val make_typed: t -> Term.t * t

val push_implicits: t -> t
val push_argument: t -> t option
val apply_argument: Ast.Expression.argument_type -> t -> t


val start_binder: t -> t
val make_bound: int -> t -> Term.t * t
val check_bound: int -> int -> t -> (t, unit) result

val lambda_bound: string -> t -> t
(** Insert a type variable for the unknown type of the bound variable and the
bound variable. *)

val lambda_bound_typed: string -> t -> (t, Term.typ * t) result
val lambda_inner_typed: t -> t

val pi_bound: string -> t -> t
(** Insert a type variable for the unknown type of the bound variable and the
bound variable. *)

val pi_bound_typed: string -> t -> t

val pi_make: t -> Term.typ * t
