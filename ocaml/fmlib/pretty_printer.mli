module Readable:
sig
  type t
  val has_more: t -> bool
  val peek: t -> char
  val advance: t -> t
end



module Document:
sig
  type t
  val empty: t
  val text: string -> t
  val text_sub: string -> int -> int -> t
  val line: string -> t
  val cut: t
  val space: t
  val (^): t -> t -> t (* concatenation *)
  val nest: int -> t -> t
  val group: t -> t
  val bracket: int -> string -> t -> string -> t
end



(** Type of a pretty printer containing a value of type ['a]. Usually ['a] is
   [unit]. *)
type 'a t

(** [return a]: Pretty printer containing the value [a] and printing
   nothing. *)
val return: 'a -> 'a t

(** [pp >>= f]: Pretty printer which first prints [pp] and then [f a] where
   [a] is the value contained in [pp]. The value contained in [pp >>= f] is
   determined by the function [f]. Usually the value contained in pretty
   printers is [()].*)
val (>>=): 'a t -> ('a -> 'b t) -> 'b t


(** [pp1 >> pp2] prints first [pp1] and then [pp2]. *)
val (>>): 'a t -> 'b t -> 'b t


(** [substring s pos len]: pretty printer printing a substring of [s] starting
   at [pos] and having length [len]. *)
val substring: string -> int -> int -> unit t

(** [string s]: pretty printer printing the string [s]. *)
val string: string -> unit t

(** [char s]: pretty printer printing the character [c]. *)
val char: char -> unit t

(** [fill n c]: pretty printer printing the character [c] [n] times. *)
val fill: int -> char -> unit t


(** [text s]: pretty printer printing an optional line break with the
   alternative text [s]. *)
val line: string -> unit t

(** pretty printer printing an optional line break with no alternative text.  *)
val cut: unit t

(** pretty printer printing an optional line break with a blank as alternative
   text.  *)
val space: unit t

(** [nest i pp]: pretty printer printing the same content as [pp] but doing an
   additional indent of [i] at each line break.  *)
val nest: int -> 'a t -> unit t

(** [nest i pp]: pretty printer printing the same content as [pp] but doing an
   additional indent of [i] relative to the current position at each line
   break.  *)
val nest_relative: int -> 'a t -> unit t

(** [group pp]: treat all line breaks appearing in [pp] consistently
   i.e. either output all as line breaks or all with their alternative
   text. *)
val group: 'a t -> unit t

(** [fill_paragraph s]: Print the string [s] as a paragraph i.e. putting as
   many words on a line as possible. *)
val fill_paragraph: string -> unit t

val chain: unit t list -> unit t

(** [of_document d]: A pretty printer generated from the document [d]. *)
val of_document: Document.t -> unit t


(** [run indent width ribbon pp]: A readable generated from the pretty printer
   [pp] formatted with an initial [indent], a line [width] and a [ribbon]
   width. *)
val run: int -> int -> int -> unit t -> Readable.t
