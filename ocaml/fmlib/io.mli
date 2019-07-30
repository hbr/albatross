open Common_module_types



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








module type SIG_MIN =
  sig
    type in_file
    type out_file

    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file

    module M: MONAD
    include MONAD

    module Process:
    sig
      val exit: int -> 'a t
      val execute: unit t -> unit
      val command_line: string array t
      val current_working_directory: string  t
    end

    module Path0:
    sig
      val separator: char
      val delimiter: char
    end

    val read_directory: string -> string array option t

    val prompt: string -> string option t

    (*val open_for_read:  string -> in_file  option t
    val open_for_write: string -> out_file option t
    val create: string -> out_file option t
    val close_in:  in_file  -> unit t
    val close_out: out_file -> unit t
    val flush: out_file -> unit t
    val flush_all: unit t

    val getc: in_file -> char option t
    val putc: char -> out_file  ->  unit t
    val get_line: in_file -> string option t
    val put_substring: string -> int -> int -> out_file -> unit t*)

    module Read: functor (W:WRITABLE) ->
                 sig
                   val read_buffer: in_file -> W.t -> W.t t
                   val read: in_file -> W.t -> W.t t
                 end
    module Write: functor (R:READABLE) ->
                  sig
                    val write_buffer: out_file -> R.t -> R.t t
                    val write: out_file -> R.t -> R.t t
                  end

  end



module type SIG =
  sig
    include SIG_MIN

    module Path:
    sig
      (** [absolute path] converts [path] into an absolute path. *)
      val absolute: string -> string t


      (** [split path] splits [path] into a dirname and a basename if
         possible.

         Examples:
         {[
           split ""                = None
           split "/"               = None
           split "/hello"          = Some ("/", "hello")
           split "/User/name/xxx/" = Some("/User/name", "xxx")
           split "/User/name/xxx"  = Some("/User/name", "xxx")
         ]}

       *)
      val split: string -> (string * string) option


      (** [normalize path] removes duplicate path separators and normalizes
         "." and ".." segments.


         Examples:
         {[
           normalize ""            = "."
           normalize "/"           = "/"
           normalize "////"        = "/"
           normalize "a//b"        = "a/b"
           normalize "a/./b"       = "a/b"
           normalize "a/../b"      = "b"
           normalize "a/b/../../c" = "c"
           normalize "../a"        = "../a"
         ]}
       *)
      val normalize: string -> string

      (** [join dir file] joins the directory name [dir] with the file name
         [file]. *)
      val join: string -> string -> string
    end


    module Directory:
    sig
      (** [read path] reads the entries (files and subdirectories) of the
         directory [path] and returns it in an array ([..] and [.] are not
         included). *)
      val read: string -> string array option t
    end

    (*val read_file:   string -> 'a t -> (in_file  -> 'a t) -> 'a t
    val write_file:  string -> 'a t -> (out_file -> 'a t) -> 'a t
    val create_file: string -> 'a t -> (out_file -> 'a t) -> 'a t*)


    module File:
    sig
      module In:
      sig
        type fd
      end
      module Out:
      sig
        type fd
        val putc: char -> fd -> unit t
        val substring: string -> int -> int -> fd -> unit t
        val string: string -> fd -> unit t
        val line: string -> fd -> unit t
        val newline: fd -> unit t
        val fill: int -> char -> fd -> unit t
      end
      val stdin:  In.fd
      val stdout: Out.fd
      val stderr: Out.fd
    end


    module Repl:
    sig
      val prompt: string -> string option t
    end


    (*val getc_in: char option t
    val get_line_in: string option t*)

    module Stdout:
    sig
      val putc: char -> unit t
      val string: string -> unit t
      val line: string -> unit t
      val newline: unit t
      val fill: int -> char -> unit t
    end

    module Stderr:
    sig
      val putc: char -> unit t
      val string: string -> unit t
      val line: string -> unit t
      val newline: unit t
      val fill: int -> char -> unit t
    end
  end





module Buffers: BUFFERS


module Make (M:SIG_MIN): SIG


module Output (Io:SIG):
sig
  include OUTPUT
  val run: Io.File.Out.fd -> t -> unit Io.t
end
