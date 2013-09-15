open Type
open Term
open Proof

type t

val empty: unit -> t

val put_axiom:  int array -> typ array -> term -> t -> unit

val put_proved: int array -> typ array -> term -> proof_term -> t -> unit

val print: Class_table.t -> Feature_table.t -> t -> unit
