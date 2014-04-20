open Signature
open Support
open Term
open Container

type t
type proof_term
val make:  unit -> t
val push:  entities list withinfo -> return_type -> t -> unit
val push_empty: t -> unit
val push_untyped: int array -> t -> unit
val pop:   t -> unit
val pop_keep_assertions: t -> unit
val print: t -> unit

val is_global:   t -> bool
val is_toplevel: t -> bool
val depth:       t -> int
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
    term -> Proof.proof_term option -> t -> unit

val put_formal_generic: int withinfo -> type_t withinfo -> t -> unit
val put_class: header_mark withinfo -> int withinfo -> t -> unit

val all_quantified_outer: term -> t -> term
val implication_chain:  term list -> term -> t -> term
val split_implication:    term -> t -> term * term
val split_all_quantified: term -> t -> int * int array * term

val count_assertions: t -> int
val find_assertion: term -> t -> int
val has_assertion:  term -> t -> bool
val expanded_term:  term -> t -> term
val add_assumption: term -> t -> int
val add_axiom:      term -> t -> int
val discharged:     int -> t -> term * proof_term
val add_proved:     term -> proof_term -> t -> unit
val add_backward:   term -> t -> unit
val assertion:      int -> t -> term
val backward_set:   term -> t -> int list
val backward_data:  int  -> t -> term list * IntSet.t

val print_all_local_assertions: t -> unit
val print_global_assertions:    t -> unit
