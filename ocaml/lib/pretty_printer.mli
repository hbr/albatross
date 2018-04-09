(*type item =
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
 *)




module type PRINTER =
  sig
    include Monad.MONAD
    type channel
    val put: int -> int -> string -> channel -> unit t
    val space: int -> channel -> unit t
    val newline: int -> channel -> unit t
  end

module type PRETTY =
  sig
    module P: PRINTER
    type t
    val make:   int -> P.channel -> t P.t
    val hbox:   t -> t P.t
    val vbox:   int -> t -> t P.t
    val hvbox:  int -> t -> t P.t
    val hovbox: int -> t -> t P.t
    val close:  t -> t P.t
    val put:    string -> t -> t P.t
    val put_sub: int -> int -> string -> t -> t P.t
    val put_wrapped: string list -> t -> t P.t
    val cut:    t -> t P.t
    val space:  t -> t P.t
    val break:  int -> int -> t -> t P.t
    val (>>):   'a P.t -> 'b P.t -> 'b P.t
    val (>>=):  'a P.t -> ('a -> 'b P.t) -> 'b P.t
  end



module String_printer:
sig
  include PRINTER with type channel = unit
  val run: int -> 'a t -> string
end

module Make (P:PRINTER): PRETTY with module P = P



val test: unit -> unit
