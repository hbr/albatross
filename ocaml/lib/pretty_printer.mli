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

    (** Type of the outfile *)
    type out_file

    type t

    type pp = t -> t out

    val make:   int -> out_file -> t out
    (** [make width fd] creates a pretty printer of line size [width]
       outputting to the file [fd]. *)

    val hbox:   pp -> pp
    val vbox:   int -> pp -> pp
    val hvbox:  int -> pp -> pp
    val hovbox: int -> pp -> pp
    val fill:   char -> int -> pp
    val put:    string -> pp
    val put_left:  int -> string -> pp
    val put_right: int -> string -> pp
    val put_sub: int -> int -> string -> pp
    val put_wrapped: string list -> pp
    val cut:    pp
    val space:  pp
    val break:  string -> int -> int -> pp
    val chain:  pp list -> pp
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
