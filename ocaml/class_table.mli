open Support
open Term
open Signature
open Container

type formal = int * type_term

type t

val boolean_index:   int
val any_index:       int
val predicate_index: int
val function_index:  int
val tuple_index:     int



val base_table: unit -> t

val put_formal: int withinfo -> type_t withinfo -> t -> unit


val module_table: t -> Module_table.t

val count: t -> int

val class_symbol: int -> t -> int
val class_name:   int -> t -> string

val add_feature:    int -> int -> bool -> t -> unit
val add_assertion:  int -> int -> bool -> t -> unit

val owner:          int -> type_term array -> Sign.t -> t -> int

val find:  int -> t -> int
val find_in_module: int -> t -> int

val update: int -> header_mark withinfo -> formal_generics -> t -> unit

val add: header_mark withinfo -> int withinfo -> formal_generics -> t -> unit


val boolean_type:   int -> term

val is_boolean_binary: Sign.t -> int -> bool
val is_boolean_unary:  Sign.t -> int -> bool

val formal_generics:
    entities list withinfo -> return_type -> formal array -> t
      -> (int*type_term) array * int

val formal_arguments:
    entities list withinfo -> int -> formal array -> t
      -> formal array

val result_type:
    return_type -> int -> formal array -> t
      -> Result_type.t

val satisfies: type_term -> formal array -> type_term -> t -> bool

val print: t -> unit

val type2string: term -> int -> int array -> t -> string
val string_of_signature: Sign.t -> int -> int array -> t -> string

val type_of_signature: Sign.t -> int -> type_term
