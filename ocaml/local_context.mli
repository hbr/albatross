open Signature
open Support
open Term
open Proof

type t
val make:  unit -> t
val push:  entities list withinfo -> return_type -> t -> unit
val pop:   t -> unit
val print: t -> unit

val is_global:   t -> bool
val is_toplevel: t -> bool
val is_private:  t -> bool
val is_public:   t -> bool
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

val type_variables: t -> TVars_sub.t

val boolean: t -> term

val update_type_variables: TVars_sub.t -> t -> unit

val string_of_term: term -> t -> string
val sign2string:    Sign.t -> t -> string
val signature_string: t -> string
val named_signature_string: t -> string

val find_identifier: int ->          int -> t -> (int * TVars.t * Sign.t) list
val find_feature:    feature_name -> int -> t -> (int * TVars.t * Sign.t) list

val put_global_function:
    feature_name withinfo  -> Feature_table.implementation_status ->
      term option -> t -> unit

val implication_id: t -> int

val put_global_assertion:
    term -> proof_term option -> t -> unit

val put_formal_generic: int withinfo -> type_t withinfo -> t -> unit
val put_class: header_mark withinfo -> int withinfo -> t -> unit
