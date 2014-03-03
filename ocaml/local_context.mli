open Signature
open Support
open Term

type t
val make_basic: unit -> t
val make_next:
    entities list withinfo -> return_type -> t -> t

val is_basic:   t -> bool
val is_private: t -> bool
val is_public:  t -> bool
val set_visibility: visibility -> t -> unit
val reset_visibility: t -> unit

val arity:     t -> int
val argument:  int -> t -> int * TVars.t * Sign.t

val result_type: t -> type_term

val count_type_variables: t -> int

val nfgs:    t -> int
val nargs:   t -> int
val fgnames: t -> int array
val ct:      t -> Class_table.t
val ft:      t -> Feature_table.t
val at:      t -> Assertion_table.t

val tvars_sub: t -> TVars_sub.t

val boolean: t -> term

val update_type_variables: TVars_sub.t -> t -> unit

val string_of_term: term -> t -> string
val sign2string:    Sign.t -> t -> string
val signature_string: t -> string
val named_signature_string: t -> string

val put_global_function:
    feature_name withinfo -> bool -> Feature_table.implementation_status ->
      term option -> t -> unit
