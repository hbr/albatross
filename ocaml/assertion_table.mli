open Term
open Proof

type t

val empty: unit -> t

val count: t -> int

val consequences: term -> int -> t
  -> (proof_pair * int) list

val find_backward: term -> int -> t ->
  (proof_pair * int) list

val put_assertion:
    term -> int -> proof_term option -> Feature_table.t -> t -> unit
