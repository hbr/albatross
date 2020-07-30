(** Represents a position in a text file. *)

type t (** Position in a text file. *)



(** Make a position with points to the start of a textfile. *)
val start: t



(** Get the line number. First line is line 0. *)
val line: t -> int



(** Get the column number. First column is column 0. *)
val column: t -> int



(** Advance the position by using the next character. If the next character is a
    newline, then the line number is increment and the column number is reset to
    0.
*)
val next: char -> t -> t



(** Advance the position to the start of the next line. *)
val next_line: t -> t



(** Advance the column position by 1. *)
val next_column: t -> t
