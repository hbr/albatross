open Common_module_types


module Simple_parser (F:ANY):
sig
  type final = F.t
  type token = char option
  type error = string list
  type parser
  type 'a res = ('a,error) result

  include Monad.MONAD

  val succeed: 'a -> 'a t
  val fail: error -> 'a t
  val backtrackable: 'a t -> 'a t
  val commit: 'a -> 'a t
  val (>>-): 'a t -> ('a -> 'b t) -> 'b t
  val (>>|): 'a t -> (error -> 'a t) -> 'a t
  val expect: (char -> 'a res) -> string -> 'a t

  val expect_end: final -> final t
  val char: char -> unit t
  val string: string -> unit t
  val letter: char t
  val optional: 'a t -> 'a option t
  val one_or_more: 'a t -> 'a list t
  val zero_or_more: 'a t -> 'a list t
  val one_of: 'a t list -> 'a t
  val (<|>): 'a t -> 'a t -> 'a t

  val run: final t -> string -> parser

  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val result: parser -> final res
  val line:   parser -> int
  val column: parser -> int
  val lookahead: parser -> token list
end
