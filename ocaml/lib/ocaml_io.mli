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

    type file_descr
    val stdin:  file_descr
    val stdout: file_descr
    val stderr: file_descr
    val getc: file_descr -> char option t
    val putc: file_descr -> char -> unit t
    val open_for_read:  string -> file_descr option t
    val open_for_write: string -> file_descr option t
    val create_file:    string -> file_descr option t
    val close_file: file_descr -> unit t
    val flush: file_descr -> unit t
  end


module IO: IO_TYPE
