open Alba2_common

module Sort:
sig
  type t =
    | Var of int
    | Level of int
  type constraint_ =
    | Eq of int * int
    | LE of int * int
    | LT of int * int
end

type fix_index = int
type decr_index = int
type oo_application = bool

type t = {term: t0; info: Info.t}
and t0 =
  | Sort of Sort.t
  | Variable of int
  | Application of t * t * oo_application
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * inspect_map * t array
  | Fix of fix_index * fixpoint
and typ = t
and abstraction =  string option * typ * t
and inspect_map = t
and fixpoint = (Feature_name.t option * typ * decr_index * t) array


val up: int -> t -> t
