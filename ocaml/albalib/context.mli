open Fmlib

type t

val count: t -> int

val gamma: t -> Gamma.t

val standard: unit -> t

val find_name: string -> t -> int list

val compute: Term.t -> t -> Term.t


module Pretty (P:Pretty_printer.SIG):
sig
  val print: Term.t -> t -> P.t
end
