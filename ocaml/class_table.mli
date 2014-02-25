open Support
open Term
open Signature
open Container

type t

val empty_table: unit -> t

val base_table: unit -> t

val put_formal: int withinfo -> type_t withinfo -> t -> unit

val put: header_mark withinfo -> int withinfo -> t -> unit

val boolean_type:   term

val is_boolean_binary: term array -> term -> bool

val is_boolean_unary: term array -> term -> bool

val collect_formal_generics:
    entities list withinfo -> return_type -> t -> IntSet.t

val arguments: entities list withinfo -> int array -> t 
  -> int array * type_term array

val signature: entities list withinfo -> return_type -> t ->
  int array * term array * int array * term array * (term*bool) option

val argument_signature: entities list withinfo -> t ->
  int array * term array * int array * term array

val feature_type: entities list withinfo -> return_type -> t ->
  int array * term array * int array * term array * term

(*val split_function: term -> t -> term array * term*)

val print: t -> unit

val type2string: term -> int -> t -> string

val arguments_to_string: int array -> term array -> t -> string
