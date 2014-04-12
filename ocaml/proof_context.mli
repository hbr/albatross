open Term


type t
type proof_term

val stacked_counts: t -> int list

val make:      int -> int -> t

val push:      int -> int array -> t -> unit
val pop:       t -> unit

val add_assumption:     term -> t -> int
val add_axiom:          term -> t -> int
val close_step:         t -> unit
val close:              t -> unit
val add_backward:       term -> t -> unit
val pull_backward:      term -> t -> int * term list
val discharged:         int  -> t -> term * proof_term
val add_proved:         term -> proof_term -> t -> unit
val all_quantified_outer: term -> t -> term
val implication_chain:  term list -> term -> t -> term
(*
  val is_global:   t -> bool
  val is_local:    t -> bool
  val nbenv:       t -> int
  val nbenv_local: t -> int
  val count:       t -> int
  val all_id:      t -> int
  val imp_id:      t -> int
 *)


val count:          t -> int
val count_previous: t -> int
val count_global:   t -> int

val term: int -> t -> term * int
