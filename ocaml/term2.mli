open Container
open Alba2_common

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
    | Max of lower_bound * bool IntMap.t
  val maybe_sort_of: t -> t option
  val product: t -> t -> t
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

type arguments = (string option * typ) array
type argument_list = (string option * typ) list

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

val equal: t -> t -> bool
val equal1: t option -> t -> bool

val shift: int -> t -> t
val up: int -> t -> t

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
