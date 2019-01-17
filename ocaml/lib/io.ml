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
    val create_file: string -> out_file option t
    val close_in:  in_file  -> unit t
    val close_out: out_file -> unit t
    val flush: out_file -> unit t
    val flush_all: unit t

    val getc: in_file -> char option t
    val putc: out_file -> char ->  unit t
    val get_line: in_file -> string option t
    val put_substring: out_file -> int -> int -> string -> unit t
  end


module type S =
  sig
    include S0

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


module Make (M:S0): S =
  struct
    include M

    let put_string (fd:out_file) (s:string): unit t =
      put_substring fd 0 (String.length s) s

    let put_newline (fd:out_file): unit t =
      putc fd '\n'

    let put_line (fd:out_file) (s:string): unit t =
      put_string fd s >>= fun _ ->
      put_newline fd


    let fill (fd:out_file) (c:char) (n:int): unit t =
      let rec put i =
        if i = n then
          make ()
        else
          putc fd c >>= fun _ -> put (i+1)
      in
      put 0


    let getc_in: char option t =
      getc stdin

    let get_line_in: string option t =
      get_line stdin

    let putc_out (c:char): unit t =
      putc stdout c

    let put_string_out (s:string): unit t =
      put_string stdout s

    let put_line_out (s:string): unit t =
      put_line stdout s

    let put_newline_out: unit t =
      put_newline stdout

    let putc_err (c:char): unit t =
      putc stderr c

    let put_string_err (s:string): unit t =
      put_string stderr s

    let put_line_err (s:string): unit t =
      put_line stderr s

    let put_newline_err: unit t =
      put_newline stderr
  end
