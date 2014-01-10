open Support
open Type

type t

val empty_table: unit -> t

val base_table: unit -> t

val put_formal: int withinfo -> type_t withinfo -> t -> unit

val put: header_mark withinfo -> int withinfo -> t -> unit

val boolean_type:   t -> typ

val is_boolean_binary: typ array -> typ -> bool

val is_boolean_unary: typ array -> typ -> bool

val signature: entities list withinfo -> return_type -> t ->
  int array * typ array * int array * typ array * (typ*bool) option

val argument_signature: entities list withinfo -> t ->
  int array * typ array * int array * typ array

val feature_type: entities list withinfo -> return_type -> t ->
  int array * typ array * int array * typ array * typ * typ

val split_function: typ -> t -> typ array * typ

val print: t -> unit

val type2string: typ -> int -> t -> string

val arguments_to_string: int array -> typ array -> t -> string
