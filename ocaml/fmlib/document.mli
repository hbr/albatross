open Common_module_types

type t

val empty: t
val (^): t -> t -> t
val nest: int -> t -> t
val text: string -> t
val space: t
val cut: t
val line: string -> t
val group: t -> t
val (^+): t -> t -> t
val (^/): t -> t -> t
val fold: (t -> t -> t) -> t list -> t
val spread: t list -> t
val stack:  t list -> t
val bracket: int -> string -> t -> string -> t


module type PRINTER =
  sig
    include MONAD
    val putc: char -> unit t
    val put_string: string -> unit t
    val put_substring: string -> int -> int -> unit t
    val fill: char -> int -> unit t
  end

module type PRETTY =
  functor (P:PRINTER) ->
  sig
    val print: int -> t -> unit P.t
  end

module Pretty: PRETTY

val string_of: int -> t -> string

val test: unit -> unit
