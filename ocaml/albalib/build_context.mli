type t




val make: Gamma.t -> t

val final: t -> Term.t * Term.typ * Gamma.t


val base:           t -> Gamma.t
val required_type:  t -> Term.typ
val built_type:     t -> Term.typ

val candidate:      Term.t -> t -> t option
val base_candidate: Term.t -> t -> t option
val pop: t -> Term.t * t

val push_type: t -> t
val push_typed: t -> t
val make_typed: t -> Term.t * t

val start_function_application: t -> t
val push_implicits: t -> t
val push_argument: t -> t option
val apply_argument: Ast.Expression.argument_type -> t -> t


val start_binder: t -> t
val make_bound: int -> t -> Term.t * t
val check_bound: int -> int -> t -> (t, unit) result

val lambda_bound: t -> t
val lambda_inner: t -> t
val lambda_bound_typed: t -> (t, Term.typ * t) result
val lambda_inner_typed: t -> (t, Term.typ * t) result

val pi_bound: string -> t -> t
(** Insert a type variable for the unknown type of the bound variable and the
bound variable. *)

val pi_bound_typed: string -> t -> t

val pi_make: t -> Term.typ * t
