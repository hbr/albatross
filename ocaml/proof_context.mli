open Term


type t
type proof_term

val make:      int -> int -> t

val push:      int -> int array -> t -> unit
val pop:       t -> unit

val add_assumption:     term -> t -> unit
val add_axiom:          term -> t -> unit
val close_step:         t -> unit
val close:              t -> unit
val add_backward:       term -> t -> unit
val pull_backward:      term -> t -> int * term list
val discharged:         int  -> t -> int * int array * term * proof_term
(*
  val is_global:   t -> bool
  val is_local:    t -> bool
  val nbenv:       t -> int
  val nbenv_local: t -> int
  val count:       t -> int
  val all_id:      t -> int
  val imp_id:      t -> int
 *)
