open Support
open Term
open Type

type t

val empty: unit -> t


val put: 
    feature_name withinfo -> entities list withinfo -> return_type 
      -> feature_body option ->
        Block_stack.t -> Class_table.t -> t -> unit

val term: info_expression -> int array -> typ array 
  -> Class_table.t -> t -> term

val term_to_string: term -> int array -> t -> string

val print: Class_table.t -> t -> unit

