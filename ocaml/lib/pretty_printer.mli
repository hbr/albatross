type item =
  | String of string
  | Sub of (int*int*string)
  | Space of int
  | Newline of int

type t

val make: int -> t

val has_pending: t -> bool

val fold: ('a -> item -> 'a) -> 'a -> t -> 'a

val hbox: t -> t

val vbox: int -> t -> t

val hvbox: int -> t -> t

val hovbox: int -> t -> t

val close: t -> t

val put: string -> t -> t

val put_sub: int -> int -> string -> t -> t

val break: int -> int -> t -> t

val test: unit -> unit
