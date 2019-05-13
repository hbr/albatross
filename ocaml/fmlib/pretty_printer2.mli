open Common_module_types

module type PRINTER =
  sig
    include MONAD
    val putc: char -> unit t
    val put_string: string -> unit t
    val put_substring: string -> int -> int -> unit t
    val fill: char -> int -> unit t
  end






type alternative_text = string
type start = int
type length = int
type indent = int
type width  = int
type ribbon = int






module Document:
sig
  type t
  val empty: t
  val text: string -> t
  val text_sub: string -> start -> length -> t
  val line: alternative_text -> t
  val cut: t
  val space: t
  val (^): t -> t -> t (* concatenation *)
  val nest: indent -> t -> t
  val group: t -> t
  val bracket: indent -> string -> t -> string -> t
end




module type PRETTY =
  sig
    include MONAD

    val text_sub: string -> start -> length -> unit t
    val text: string -> unit t
    val line: alternative_text -> unit t
    val cut: unit t
    val space: unit t
    val nest: indent -> 'a t -> unit t
    val group: 'a t -> unit t
    val fill_of_string: string -> unit t
    val fill_of_strings: string list -> unit t
    val chain: unit t list -> unit t
    val of_document: Document.t -> unit t
  end






module Make:
functor (P:PRINTER) ->
sig
  include PRETTY
  val run: indent -> width -> ribbon -> 'a t -> unit P.t
end





module Pretty_string: (* Pretty prints into a string *)
sig
  include PRETTY
  val string_of: 'a t -> int -> indent -> width -> ribbon -> string
end


val test: unit -> unit
