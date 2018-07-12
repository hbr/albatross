open Alba2_common

module Sort:
sig
  type sortvariable = int
  type t =
    | Proposition
    | Level of int
    | Variable of int
    | Type_of of t
    | Max of int * sortvariable
    | Product of t * t
  val type_of: t -> t
  val product: t -> t -> t
end

type fix_index = int
type decr_index = int
type oo_application = bool

type t =
  | Sort of Sort.t * Info.t
  | Variable of int * Info.t
  | Application of t * t * oo_application *Info.t
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * inspect_map * t array * Info.t
  | Fix of fix_index * fixpoint * Info.t
and typ = t
and abstraction =  string option * typ * t * Info.t
and inspect_map = t
and fixpoint = (Feature_name.t option * typ * decr_index * t) array


val sort_of: t -> Sort.t
val maybe_sort: t -> Sort.t option

val up: int -> t -> t

val split_application: t -> t list -> t * t list

val substitute: t -> t -> t

val apply_args: t -> t list -> t

val beta_reduce: t -> t list -> t * t list
