open Container
open Alba2_common


type fix_index = int
type decr_index = int
type oo_application = bool

type t =
  | Sort of Sorts.t
  | Variable of int
  | Application of t * t * oo_application
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * t * (t*t) array
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
val product: t -> t -> t option
val product1: t -> t -> t
val get_sort: t -> Sorts.t option

val variable0: t
val variable1: t
val variable2: t
val variable3: t
val variable4: t
val variable5: t
val apply1: t -> t -> t
val apply2: t -> t -> t -> t

val equal: t -> t -> bool
val equal1: t option -> t -> bool
val equal_arguments: arguments -> arguments -> bool

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


val lambda: argument_list -> t -> t
val split_lambda0: int -> t -> int -> argument_list -> t * argument_list
val split_lambda: t -> arguments * t

val split_product0: typ -> argument_list -> typ * argument_list
val split_product: typ -> arguments * typ
val push_product: arguments -> typ -> typ

val beta_reduce: t -> t list -> t * t list
