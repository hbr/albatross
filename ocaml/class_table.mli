open Support
open Type

type t

val base_table: unit -> t

val put: header_mark withinfo -> int withinfo -> t -> unit

val boolean_type:   t -> typ

val boolean_binary: t -> typ

val boolean_unary:  t -> typ

val get_type: type_t withinfo -> t -> typ

val arguments: entities list withinfo -> t -> int array * typ array

val feature_type: entities list withinfo -> return_type -> t ->
  typ array * typ * typ * int array

val split_function: typ -> t -> typ array * typ

val print: t -> unit

val type2string: typ -> int -> t -> string

val arguments_to_string: int array -> typ array -> t -> string
