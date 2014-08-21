open Support
open Container
open Term


type t
type proof_term

val context: t -> Context.t
val feature_table: t -> Feature_table.t

val is_global: t -> bool

val print_all_local_assertions: t -> unit
val print_global_assertions:   t -> unit

val get_trace_info: t -> unit

val make:      unit -> t

val push: entities list withinfo -> t -> unit
val push_untyped: int array -> t -> unit
val pop:          t -> unit

val depth:     t -> int

val find:               term -> t -> int
val has:                term -> t -> bool
val find_equivalent:    term -> t -> int
val has_equivalent:     term -> t -> bool
val add_assumption:     term -> t -> int
val add_axiom:          term -> t -> int
val has_work:           t -> bool
val work:               t -> int list
val is_used_forward:    int -> t -> bool
val close_step:         t -> unit
val close:              t -> unit
val close_assumptions:  t -> unit
val set_forward:        t -> unit
val reset_forward:      t -> unit
val add_backward:       term -> t -> unit
val discharged:         int  -> t -> term * proof_term
val add_proved:   bool -> int -> term -> proof_term -> IntSet.t -> t -> unit
val add_proved_list:   bool -> int -> (term*proof_term) list -> t -> unit
val backward_set:       term -> t -> int list
val backward_data:      int  -> t -> term list * IntSet.t

val split_implication:  term -> t -> term * term
val split_all_quantified: term -> t -> int * int array * term
val all_quantified_outer: term -> t -> term
val implication_chain:  term list -> term -> t -> term

val count:          t -> int
val count_previous: t -> int
val count_global:   t -> int

val term_orig:      int -> t -> term * int
val term:           int -> t -> term
val is_assumption:  int -> t -> bool
val used_schematic: int -> t -> IntSet.t

val check_deferred: t -> unit
val owner:          t -> int

val do_inherit: int -> (int * type_term array) list -> info -> t -> unit
  (** [do_inherit cls anc_lst info ft] let the class [cls] inherit the
      assertions from all ancestors [par_idx[par_args]] in the ancestor list
      [anc_lst]. *)
