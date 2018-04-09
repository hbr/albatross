module type IO_TYPE =
  sig
    include Monad.MONAD
    val exit: int -> 'a t
    val execute: unit t -> unit
    val command_line: string array t

    type in_file
    type out_file
    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file
    val getc: in_file -> char option t
    val putc: out_file -> char -> unit t
    val get_line: in_file -> string option t
    val put_string: out_file -> string -> unit t
    val open_for_read:  string -> in_file option t
    val open_for_write: string -> out_file option t
    val create_file:    string -> out_file option t
    val close_in:  in_file -> unit t
    val close_out: out_file -> unit t
    val flush: out_file -> unit t

    val get_line_in:    string option t
    val putc_out: char -> unit t
    val putc_err: char -> unit t
    val put_string_out:  string -> unit t
    val put_string_err:  string -> unit t
    val put_line_out:    string -> unit t
    val put_line_err:    string -> unit t
  end


module IO: IO_TYPE
