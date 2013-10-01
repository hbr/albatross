open Term
open Proof

type t
val empty: t
val count: t -> int
val proof_term:   term -> t -> proof_term
val is_proved:    term -> t -> bool
val proved_terms: t -> proof_pair list
val backward_set: term -> t -> BwdSet.t
val consequences: term -> proof_term -> t -> proof_pair list
val add_proof:    term -> proof_term -> t -> t
val add_forward:  term -> term -> proof_term -> t -> t
val add_backward: (term list * term) list -> proof_term -> t -> t

