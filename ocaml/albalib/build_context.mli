type t


val make: Gamma.t -> t


val base_candidate: Term.t -> t -> t option


val final: t -> Term.t * Term.typ * Gamma.t
