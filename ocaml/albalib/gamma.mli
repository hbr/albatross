open Fmlib

type name =
  | Normal of string
  | Binary_operator of string * Operator.t


type t

val count: t -> int

val is_valid_index: int -> t -> bool

val index_of_level: int -> t -> int

val level_of_index: int -> t -> int

val string_of_name: name -> string


val raw_type_at_level: int -> t -> Term.typ

(** [type_at_level level c] type of the entry at [level]. *)
val type_at_level: int -> t -> Term.typ

val int_type: t -> Term.typ


val type_of_variable: int -> t -> Term.typ
val type_of_term: Term.t -> t -> Term.typ

val typecheck: Term.t -> t -> Term.typ option


val name_of_level: int -> t -> name

val name_of_index: int -> t -> string

val term_at_level: int -> t -> Term.t

val standard: unit -> t

val compute: Term.t -> t -> Term.t

val push_local: string -> Term.typ -> t -> t




val remove_last: int -> t -> t

val signature: t -> Term.typ -> Signature.t
