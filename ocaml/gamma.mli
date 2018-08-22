open Alba2_common

module Term = Term2



type t
val empty: t

val count_sorts: t -> int
val sortvariable_le: t -> int -> int -> bool
val sortvariable_lt: t -> int -> int -> bool
val push_sorts: int -> (int*int*bool) list -> t -> t

val count: t -> int
val entry_type: int -> t -> Term.typ
val has_definition: int -> t -> bool
val definition: int -> t -> Term.t
val is_constructor: int -> t -> bool
val constructor_offset: int -> t -> int
val push: Feature_name.t option -> Term.typ -> t -> t
val push_unnamed: Term.typ -> t -> t
val push_inductive: Inductive.t -> t -> t
