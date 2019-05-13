open Common_module_types
open Common

(** A path to a file or a directory. *)
module type PATH =
  sig
    (** [separator = '/'] for posix and [separator = '\'] for windows.*)
    val separator: char


    (** [delimiter = ':'] for posix and [delimiter = ';'] for windows.*)
    val delimiter: char


    (** [basename path] returns the last portion of [path]. Trailing directory
       separators are ignored.

       [basename "/foo/bar/baz/asdf/quux.html" = "quux.html"] *)
    val basename: string -> string


    (** [dirname path] returns the directory name of a path, similar to the
       Unix dirname command. Trailing directory separators are ignored.

       [dirname "/foo/bar/baz/asdf/quux.html" = "/foo/bar/baz/asdf"] *)
    val dirname: string -> string

    (** [extname path] returns the extension of the path, from the last
       occurrence of the . (period) character to end of string in the last
       portion of the path. If there is no . in the last portion of the path,
       or if the first character of the basename of path (see {!val:basename})
       is ., then an empty string is returned.

       [extname "index.html" = ".html"]

       [extname "index.coffee.md" = ".md"]

       [extname "index." = "."]

       [extname "index" = ""]

       [extname ".index" = ""] *)
    val extname: string -> string
  end




(** Statistic data about a file/directory. *)
module type STAT =
  sig
    (** Type of the data. *)
    type t

    (** Time stamp. *)
    type time

    (** Compare time stamps. *)
    val compare: time -> time -> int

    (** Is the node a directory? *)
    val is_directory: t -> bool

    (** Is the node a file? *)
    val is_file:      t -> bool

    (** Time of last modification. *)
    val modification: t -> time
  end



(** IO Buffer *)
module type BUFFER =
  sig
    type t
    val alloc: int -> t
  end

module type BUFFERS =
  functor (B:BUFFER) ->
  sig
    type t
    val make: int -> t
    val is_open_read: t -> int -> bool
    val is_open_write: t -> int -> bool
    val capacity: t -> int

    (** [occupy_readable s fd] allocates a buffer for reading and associates
       the buffer with the file descriptor [fd]. Returns the position of the
       file in the system. *)
    val occupy_readable: t -> int -> int

    (** [occupy_writable s fd] allocates a buffer for writing and associates
       the buffer with the file descriptor [fd]. Returns the index of the
       file in the system. *)
    val occupy_writable: t -> int -> int

    (** [release s idx] releases the buffer at the index [idx]. *)
    val release: t -> int -> unit

    val readable_file: t -> int -> int * B.t
    val writable_file: t -> int -> int * B.t

    val find_open: t -> int -> int
  end




(** A readable structure *)
module type READABLE =
  sig
    (** Type of the structure.*)
    type t

    (** Does the structure have more characters to read? *)
    val has_more: t -> bool

    (** [peek r] returns the next character. *)
    val peek: t -> char

    (** [advance r] advances the structure by one character. *)
    val advance: t -> t
  end




(** A writable structure *)
module type WRITABLE =
  sig
    (** Type of the structure.*)
    type t

    (** Is it possible to write more characters to the structure? *)
    val needs_more: t -> bool

    (** [putc w c] writes the character [c] to the structure and returns a
       structure which might accept more characters. *)
    val putc: t -> char ->  t

    (** [putend w] signals to the structure [w] that there are no more
       characters available to write (e.g. eof reached). *)
    val putend: t -> t
  end

(** IO filter

   An IO filter is a {!module-type:WRITABLE} structure which returns on each
   character besides the structure a {!module-type:READABLE} structure which is
   considered as its output as a reaction to its input.

 *)
module type FILTER =
  sig
    module Readable: READABLE
    type t
    val needs_more: t -> bool
    val putc: t -> char -> t * Readable.t
    val put_end: t -> t * Readable.t
  end









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

    include MONAD

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
    val putc: char -> out_file  ->  unit t
    val get_line: in_file -> string option t
    val scan: (char,'a) Scan.t -> in_file -> 'a t
    val put_substring: string -> int -> int -> out_file -> unit t

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

    val put_string: string -> out_file -> unit t
    val put_line:   string -> out_file -> unit t
    val put_newline:   out_file -> unit t
    val fill: char -> int -> out_file -> unit t

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



module String_reader:
sig
  include READABLE

  (** [of_string s] creates a readable structure of the string [s]. *)
  val of_string: string -> t

  (** [of_substring s start len] creates a readable structure of the substring
     of [s] starting at position [start] and having length [len]. *)
  val of_substring: string -> int -> int -> t
end

module Fill_reader:
sig
  include READABLE

  (** [make n c] makes a character filler with [n] characters [c]. *)
  val make: int -> char -> t
end


module Buffers: BUFFERS

module Make (M:S0): S


module Output (Io:S):
sig
  include Monad.OUTPUT
  val run: Io.out_file -> 'a t -> 'a Io.t
end
