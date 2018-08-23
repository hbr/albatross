module Set:
sig
  type t
  val empty: t
  val singleton: int -> bool -> t
  val equal: t -> t -> bool
  val add: int -> bool -> t -> t
  val union: t -> t -> t
  val is_lower_bound: int -> t -> bool
  val is_strict_lower_bound: int -> t -> bool
end

module Variables:
sig
  type t
  val count: t -> int
  val le: t -> int -> int -> bool
  val lt: t -> int -> int -> bool
  val empty: t
  val push: int -> (int*int*bool) list -> t -> t
end

type t =
  | Proposition
  | Datatype
  | Any1
  | Variable of int
  | Variable_type of int
  | Max of Set.t

val type_of: t -> t option
val product: t -> t -> t
val sub: t -> t -> (int -> int -> bool) -> (int -> int -> bool) -> bool
val equal: t -> t -> bool
