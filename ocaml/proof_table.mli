open Term
open Support
open Container

type t
type proof_term

val context: t -> Context.t
val class_table: t -> Class_table.t

val is_private:         t -> bool
val is_public:          t -> bool
val is_interface_use:   t -> bool
val is_interface_check: t -> bool
val add_used_module:    int -> int list -> IntSet.t -> t -> unit
val add_current_module: int -> IntSet.t -> t -> unit
val set_interface_check: IntSet.t -> t -> unit


val depth:       t -> int
val is_global:   t -> bool
val is_local:    t -> bool
val is_toplevel: t -> bool
val count:       t -> int
val count_previous: t -> int
val count_global:   t -> int
val nbenv:       t -> int
val nbenv_local: t -> int
val names:       t -> int array
val all_id:      t -> int
val imp_id:      t -> int

val split_implication: term -> t -> term * term
val split_all_quantified: term -> t -> int * int array * term
val implication: term -> term -> t -> term
val all_quantified:  int -> int array -> term -> t -> term
val all_quantified_outer: term -> t -> term
val implication_chain: term list -> term -> t -> term

val term:          int -> t -> term * int
val nbenv_term:    int -> t -> int
val local_term:    int -> t -> term
val is_assumption: int -> t -> bool
val variant:       int -> int -> t -> term

val stacked_counts: t -> int list

val make: unit -> t
val push: entities list withinfo -> t -> unit
val push_untyped: int array -> t -> unit
val pop:  t -> unit
val keep: int -> t -> unit

val add_proved_global: bool -> int -> term -> proof_term -> int -> t -> unit
val add_proved:        term -> proof_term -> int -> t -> unit

val add_axiom:      term -> t -> unit
val add_assumption: term -> t -> unit
val add_mp:         term -> int -> int -> t -> unit
val add_expand:     term -> int -> t -> unit
val add_expand_backward:  term -> term -> t -> unit
val add_reduce:     term -> int -> t -> unit
val add_reduce_backward:  term -> term -> t -> unit
val add_specialize: term -> int -> term array -> t -> unit
val add_inherited:  term -> int -> int -> t -> unit

val discharged:   int -> t -> term * proof_term
