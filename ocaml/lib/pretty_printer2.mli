module type PRINTER =
  sig
    include Monad.MONAD
    val putc: char -> unit t
    val put_string: string -> unit t
    val put_substring: string -> int -> int -> unit t
    val fill: char -> int -> unit t
  end



type alternative_text = string
type start = int
type length = int
type indent = int

module type PRETTY =
  functor (P:PRINTER) ->
  sig
    include Monad.MONAD

    val text_sub: string -> start -> length -> unit t
    val text: string -> unit t
    val line: alternative_text -> unit t
    val cut: unit t
    val space: unit t
    val nest: indent -> 'a t -> unit t
    val group: 'a t -> unit t
    val fill_of_string: string -> unit t
    val fill_of_stringlist: string list -> unit t
    val chain: unit t list -> unit t
    val run: int -> int -> int -> 'a t -> unit P.t
  end



module Make: PRETTY



val test: unit -> unit
