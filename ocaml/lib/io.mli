open Common


module type SCANNER =
  sig
    type t
    val can_receive: t -> bool
    val receive: char -> t -> t
    val end_buffer: t -> t
    val end_stream: t -> t
  end


module type S0 =
  sig
    type in_file
    type out_file

    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file

    include Monad.MONAD

    val exit: int -> 'a t
    val execute: unit t -> unit

    val command_line: string array t

    val open_for_read:  string -> in_file  option t
    val open_for_write: string -> out_file option t
    val create: string -> out_file option t
    val close_in:  in_file  -> unit t
    val close_out: out_file -> unit t
    val flush: out_file -> unit t
    val flush_all: unit t

    val getc: in_file -> char option t
    val putc: out_file -> char ->  unit t
    val get_line: in_file -> string option t
    val scan: in_file -> (char,'a) Scan.t -> 'a t
    val put_substring: out_file -> int -> int -> string -> unit t

    module Scan: functor (S:SCANNER) ->
                 sig
                   val buffer: in_file -> S.t -> S.t t
                   val stream: in_file -> S.t -> S.t t
                 end
  end


module type S =
  sig
    include S0

    val read_file:   string -> 'a t -> (in_file  -> 'a t) -> 'a t
    val write_file:  string -> 'a t -> (out_file -> 'a t) -> 'a t
    val create_file: string -> 'a t -> (out_file -> 'a t) -> 'a t

    val put_string: out_file -> string -> unit t
    val put_line:   out_file -> string -> unit t
    val put_newline:   out_file -> unit t
    val fill: out_file -> char -> int -> unit t

    val getc_in: char option t
    val get_line_in: string option t

    val putc_out: char -> unit t
    val put_string_out: string -> unit t
    val put_line_out: string -> unit t
    val put_newline_out: unit t

    val putc_err: char -> unit t
    val put_string_err: string -> unit t
    val put_line_err: string -> unit t
    val put_newline_err: unit t
  end


module Make (M:S0): S
