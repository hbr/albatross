open Container
open Alba2_common

module Sort_set:
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

module Sort:
sig
  type lower_bound =
    | No
    | DT
    | A1
  type t =
    | Proposition
    | Datatype
    | Any1
    | Variable of int
    | Variable_type of int
    | Max of lower_bound * Sort_set.t
  val maybe_sort_of: t -> t option
  val product: t -> t -> t
  val sub: t -> t -> (int -> int -> bool) -> bool
end


type fix_index = int
type decr_index = int
type oo_application = bool

type t =
  | Sort of Sort.t
  | Variable of int
  | Application of t * t * oo_application
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * t * t array
  | Fix of fix_index * fixpoint
and typ = t
and abstraction =  string option * typ * t
and fixpoint = (Feature_name.t option * typ * decr_index * t) array

type name_type = string option * typ
type fname_type = Feature_name.t option * typ
type gamma = fname_type array
type arguments = name_type array
type argument_list = name_type list

val datatype: t
val proposition: t
val any1: t
val sort_variable: int -> t
val sort_variable_type: int -> t
val maybe_product: t -> t -> t option
val get_sort: t -> Sort.t option

val variable0: t
val variable1: t
val variable2: t
val variable3: t
val variable4: t
val variable5: t
val apply0: t -> t -> t

val equal: t -> t -> bool
val equal1: t option -> t -> bool

val shift: int -> t -> t
val up_from: int -> int -> t -> t
val up: int -> t -> t

val has_variables: (int->bool) -> t -> bool

val arrow: t -> t -> t


val substitute: t -> t -> t

val split_application: t -> t list -> t * t list
val apply_args: t -> t list -> t
val apply_arg_array: t -> t array -> t
val apply_standard: int -> int -> t -> t

val split_product0: typ -> argument_list -> typ * argument_list
val split_product: typ -> arguments * typ
val push_product: arguments -> typ -> typ

val beta_reduce: t -> t list -> t * t list
