open Type
open Term
open Proof

type t

val empty: unit -> t

val count: t -> int

val to_string: int -> Class_table.t -> Feature_table.t -> t -> string

val find_backward: term -> int -> Feature_table.t -> t ->
  (proof_pair * int) list

val put_axiom:
    int array -> typ array -> term
      -> Feature_table.t -> t -> unit

val put_proved:
    int array -> typ array -> term -> proof_term
      -> Feature_table.t -> t -> unit

val print: Class_table.t -> Feature_table.t -> t -> unit
