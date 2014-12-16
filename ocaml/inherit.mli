open Support
open Term


val do_inherit: int -> (int*type_term array)list -> info -> Proof_context.t -> unit

val export_inherited: int -> (int*type_term array)list -> Proof_context.t -> unit

val inherit_to_descendants: int -> info -> Proof_context.t -> unit
