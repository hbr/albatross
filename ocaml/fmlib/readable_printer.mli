open Common_module_types

(** A readable printer is a structure you can issue print commands on and
   which returns a readable structure which can be read character by
   character. *)



(** {1 Principles} *)

(** A readable printer is a very lightweight and lazy structure. Issuing a
   command like [string "hello"] just stores the string and does nothing else.

   Since the printer is organized as a monad you chain to printers [p1] and
   [p2] by the monadic sequencing operator [p1 >>= fun _ -> p2]. The readable
   printer just stores [p1] and the function to compute [p2].

   If you printed all your stuff to the printer [p] you use [readable p] to
   generate a readable structure. The readable structure is lazy as well. It
   just has the first item (string, substring, fill or character) explicitly
   and a function to generate the rest if needed. So the actual output is
   generated on demand.

 *)






(** {1 Readable Structure} *)

(** The readable structure returned by the printer. *)
module R: Io.READABLE




(** {1 Monad} *)

(** The printer is organized as a monad. *)
include MONAD





(** {1 Print Commands} *)

(** [string s] prints the string [s].*)
val string: string -> unit t


(** [substring s start len] prints the substring of [s] starting at position
   [start] with length [len].*)
val substring: string -> int -> int -> unit t

(** [fill n c] prints the character [c] [n] times. *)
val fill: int -> char -> unit t

(** [char c] prints the character [c]. *)
val char: char -> unit t




(** {1 Generate the Readable Structure} *)

(** [readable p] generates a readable structure from the printer [p]. *)
val readable: unit t -> R.t
