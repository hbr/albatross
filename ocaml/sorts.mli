module Set:
sig
  type t
  val empty: t
  val singleton: int -> bool -> t
  val equal: t -> t -> bool
  val add: int -> bool -> t -> t
  val union: t -> t -> t
  val bindings: t -> (int*bool) list
  val is_lower_bound: int -> t -> bool
  val is_strict_lower_bound: int -> t -> bool
end

module Variables:
sig
  type t
  val count: t -> int
  val le: int -> int -> t -> bool
  val lt: int -> int -> t -> bool
  val empty: t

  (** [push n [lo,hi,strict; .... ] vs] adds n new sort variables and a list
     of constraints to the sort variables [vs].

     constraint element:

         lo,hi,false: lo <= hi

         lo,hi,true: lo < hi

     The new constraints must not introduce any circularity.
 *)
  val push: int -> (int*int*bool) list -> t -> t
end

type t =
  | Proposition
  | Datatype
  | Any1
  | Max of Set.t


val variable: int -> t
val variable_type: int -> t
val type_of: t -> int -> t option
val product: t -> t -> t
val sub: t -> t -> Variables.t -> bool
val equal: t -> t -> bool
