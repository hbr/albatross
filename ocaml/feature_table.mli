open Support
open Term
open Signature

type t

type implementation_status = No_implementation | Builtin | Deferred

val count:      t -> int

val implication_index: int
val all_index:         int
val some_index:        int

val base_table: unit -> t


val implication_term: term -> term -> int -> t -> term

val expand_term: term->int->t->term

val normalize_term: term->int->t->term

val find_funcs: feature_name -> int -> t -> (int * TVars.t * Sign.t) list

val put_function:
    feature_name withinfo -> int array -> type_term array -> int array
      -> Sign.t -> bool -> implementation_status -> term option -> t -> unit

val term_to_string: term -> int array -> t -> string

val print: Class_table.t -> t -> unit

