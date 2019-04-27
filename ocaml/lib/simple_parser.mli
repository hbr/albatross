open Common_module_types


module Simple_parser (F:ANY):
sig
  type final = F.t
  type token = char option
  type error = string
  type parser

  type _ t

  val succeed: 'a -> 'a t
  val fail: error -> 'a t
  val backtrackable: 'a t -> 'a t
  val commit: 'a -> 'a t

  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val (>>-): 'a t -> ('a -> 'b t) -> 'b t

  val expect: (char -> ('a,error) result) -> error -> 'a t

  val expect_end: final -> final t
  val char: char -> unit t
  val one_of_chars: string -> unit t
  val string: string -> unit t
  val letter: char t
  val digit:  char t
  val optional: 'a t -> 'a option t
  val one_or_more: 'a t -> 'a list t
  val zero_or_more: 'a t -> 'a list t
  val skip_one_or_more: 'a t -> int t
  val skip_zero_or_more: 'a t -> int t
  val zero_or_more_separated: 'a t -> _ t -> 'a list t
  val one_or_more_separated: 'a t -> _ t -> 'a list t
  val one_of: 'a t list -> 'a t
  val (<|>): 'a t -> 'a t -> 'a t
  val (<?>): 'a t -> string -> 'a t

  val run: final t -> string -> parser

  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val result: parser -> (final,error list) result
  val line:   parser -> int
  val column: parser -> int
  val lookahead: parser -> token list

  val result_string: parser -> (final -> string) -> string
  val lookahead_string: parser -> string
end
