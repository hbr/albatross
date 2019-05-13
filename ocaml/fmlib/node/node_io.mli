(* IO Interface *)
module type IO =
  sig
    open Fmlib
    open Common_module_types

    include MONAD

    type in_file
    type out_file
    type in_stream
    type out_stream

    val exit: int -> 'a t
    val execute: unit t -> unit


    module Reader (P:Io.WRITABLE):
    sig
      val parse_file: string -> P.t -> P.t option t
    end

    module Filter (F:Io.FILTER):
    sig
      type error =
        | Cannot_open_input
        | Cannot_open_output
        | Cannot_write of F.t * F.Readable.t

      val parse_file: string -> string -> F.t -> (F.t, error) result t
    end
  end





type 'a t
type in_file
type out_file

val exit: int -> 'a t
val execute: unit t -> unit

val return: 'a -> 'a t
val (>>=):  'a t -> ('a -> 'b t) -> 'b t

val create_directory: string -> unit option t
val remove_directory: string -> unit option t

val open_for_read: string -> in_file option t
val open_for_write: string -> out_file option t
val close_readable: in_file -> unit option t
val close_writable: in_file -> unit option t

val getc: in_file -> char option t
val putc: out_file -> char -> unit option t

val getchar: char option t
val putchar: char -> unit option t
val errchar: char -> unit option t
