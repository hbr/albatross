module type PRINTER =
  (* The IO monad is a printer, the PRINTER module type is a subtype
     of IO_TYPE. Therefore any module conforming to IO_TYPE can be
     used to generate a pretty printer. *)
  sig
    include Monad.MONAD
    type out_file
    val putc: out_file -> char -> unit t
    val put_substring: out_file -> int -> int -> string -> unit t
    val fill: out_file  -> char -> int -> unit t
  end


module type PRETTY =
  (* Signature of a pretty printer. *)
  sig
    type _ out
    type out_file
    type t
    val make:   int -> out_file -> t out
    val hbox:   t -> t out
    val vbox:   int -> t -> t out
    val hvbox:  int -> t -> t out
    val hovbox: int -> t -> t out
    val close:  t -> t out
    val fill:   char -> int -> t -> t out
    val put:    string -> t -> t out
    val put_left:  int -> string -> t -> t out
    val put_right: int -> string -> t -> t out
    val put_sub: int -> int -> string -> t -> t out
    val put_wrapped: string list -> t -> t out
    val cut:    t -> t out
    val space:  t -> t out
    val break:  string -> int -> int -> t -> t out
    val (>>):   'a out -> 'b out -> 'b out
    val (>>=):  'a out -> ('a -> 'b out) -> 'b out
    val stop:   t -> unit out
  end



module String_printer:
sig
  include PRINTER with type out_file = unit
  val run: int -> 'a t -> string
end

module Make (P:PRINTER): PRETTY with type 'a out = 'a P.t and
                                     type out_file = P.out_file



val test: unit -> unit
