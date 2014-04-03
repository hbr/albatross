open Term

type t
type proof_term

val depth:       t -> int
val is_global:   t -> bool
val is_local:    t -> bool
val is_toplevel: t -> bool
val count:       t -> int
val nbenv:       t -> int
val nbenv_local: t -> int
val names:       t -> int array
val all_id:      t -> int
val imp_id:      t -> int

val make: int -> int -> t
val push: int -> int array -> t -> unit
val pop:  t -> unit

val add:            term -> proof_term -> t -> unit
val add_axiom:      term -> t -> unit
val add_assumption: term -> t -> unit

val term_of_pt: proof_term -> t -> term
    (*val implication: int -> t -> term*)

    (*val used_assertions: int -> t -> int list -> int list*)

val discharged:   int -> t -> int * int array * term * proof_term
