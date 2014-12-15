open Support
open Term


val do_inherit: int -> (int*type_term array)list -> info -> Feature_table.t -> unit

val export_inherited: int -> (int*type_term array)list -> Feature_table.t -> unit

val inherit_to_descendants: int -> info -> Feature_table.t -> unit
