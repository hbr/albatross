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
    | Proposition
    | Any of int

  (** [is_sub s1 s2] Is [s1] a subtype of [s2] (or equal)? *)
  val is_sub: t -> t -> bool

  (** [is_super s1 s2] Is [s1] a supertype of [s2] (or equal)? *)
  val is_super: t -> t -> bool
end



module Lambda_info:
sig
  type t
  val name:         t -> string
  val is_anonymous: t -> bool
  val is_typed:     t -> bool

  val typed:   string -> t
  val untyped: string -> t
end


module Pi_info:
sig
  type t
  val name:         t -> string
  val is_anonymous: t -> bool
  val is_arrow:     t -> bool
  val is_typed:     t -> bool

  val arrow: t
  val typed:   string -> t
  val untyped: string -> t
end


type appl =
  | Normal
  | Binary


type t =
  | Sort of Sort.t

  | Variable of int

  | Appl of t * t * appl

  | Lambda of typ * t * Lambda_info.t

  | Pi of typ * typ * Pi_info.t

  | Value of Value.t

and typ = t


val proposition: t
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



(** [application f n mode] returns

       f (Var (n-1)) ... (Var 0)

    where all applications are done with mode [mode].
*)
val application: t -> int -> appl -> t


val fold_free_variables: 'a -> (int -> 'a -> 'a) -> t -> 'a
