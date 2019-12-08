val bruijn_convert: int -> int -> int


module Value:
sig
  type t =
    | Int of int (* int32? *)
    | Char of int
    | String of string
    | Unary of (t -> t)
    | Binary of (t -> t -> t)

  val number_values: string -> t list
  val int_plus: t
  val int_minus: t
  val int_times: t
  val string_concat: t
  val apply: t -> t -> t
end



module Sort:
sig
  type t =
    | Any of int
  val is_super: t -> t -> bool
end


type appl =
  | Normal
  | Binary


type t =
  | Sort of Sort.t

  | Variable of int

  | Appl of t * t * appl

  (*| Lam of typ * t*)

  | Pi of string * typ * t

  | Value of Value.t

and typ = t


val any: t
val char:   int -> t
val string: string -> t


(** [up_from delta start t] *)
val up_from: int -> int -> t -> t


(** [up delta t] *)
val up: int -> t -> t


(** [down_from delta start t] *)
val down_from: int -> int -> t -> t option


(** [down delta t] *)
val down: int -> t -> t option


val substitute: (int -> t) -> t -> t

val apply: t -> t -> t

val application: t -> int -> appl -> t
