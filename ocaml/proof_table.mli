open Term

type t
type proof_term

val context: t -> Context.t

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

val stacked_counts: t -> int list

val make: unit -> t
val push: int -> int array -> t -> unit
val pop:  t -> unit

val add_proved: term -> proof_term -> t -> unit

val term_of_pt: proof_term -> t -> term

val add_axiom:      term -> t -> unit
val add_assumption: term -> t -> unit
val add_mp:         term -> int -> int -> t -> unit
val add_specialize: term -> int -> term array -> t -> unit

val discharged:   int -> t -> term * proof_term
