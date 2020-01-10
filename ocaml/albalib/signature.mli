type t

val base_count: t -> int

val count_arguments: t -> int

val count_explicit_args: t -> int

val count_first_implicits: t -> int

val typ: t -> Term.typ

(*val arg_typ: t -> Term.typ*)

(** [make cnt nargs tp] *)
val make: int -> int -> Term.typ -> t


(** [push sign arg_tp tp is_implicit] *)
val push: t -> Term.typ -> Term.typ -> bool -> t

val pop: t -> (Term.typ * t) option

val up: int -> t -> t
