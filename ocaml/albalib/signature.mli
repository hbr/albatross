type t

val count_explicit_args: t -> int

val count_first_implicits: t -> int

val count: t -> int

val has_args: t -> bool

val typ: t -> Term.typ

val arg_typ: t -> Term.typ

val make: Term.typ -> t


(** [push sign arg_tp tp implicit] *)
val push: t -> Term.typ -> Term.typ -> bool -> t
