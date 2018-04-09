module type IO_TYPE =
  sig
    include Monad.MONAD
    val exit: int -> 'a t
    val execute: unit t -> unit
    val command_line: string array t
    val get_line:    string option t
    val put_string:  string -> unit t
    val put_line:    string -> unit t
    val put_newline: unit t
    val put_stderr_string:  string -> unit t
    val put_stderr_line:    string -> unit t
    val put_stderr_newline: unit t

    type in_file
    type out_file
    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file
    val getc: in_file -> char option t
    val putc: out_file -> char -> unit t
    val open_for_read:  string -> in_file option t
    val open_for_write: string -> out_file option t
    val create_file:    string -> out_file option t
    val close_in_file:  in_file -> unit t
    val close_out_file: out_file -> unit t
    val flush: out_file -> unit t
  end


module IO: IO_TYPE
