type t

val singleton: Term.t -> Gamma.t -> t

val add_unique: Term.t -> Gamma.t -> t -> t option
