open Common_module_types

module type BASIC =
  sig
    type 'a t
    val return: 'a -> 'a t
    val succeed: 'a -> 'a t
    val consumer: 'a t -> 'a t
    val map:     ('a -> 'b) -> 'a t -> 'b t
    val (>>=):   'a t -> ('a -> 'b t) -> 'b t
    val (<|>):   'a t -> 'a t -> 'a t
    val backtrackable: 'a t -> 'a t
    val commit: 'a -> 'a t
  end


module Make (T:ANY) (S:ANY) (E:ANY) (F:ANY):
sig
  type token = T.t
  type state = S.t
  type final = F.t
  type error = E.t

  type parser

  include BASIC


  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val put_token:  parser -> token -> parser
  val state:      parser -> state
  val result:     parser -> (final, error list) result
  val lookahead:  parser -> token list

  val make_parser: state -> final t -> parser

  val get: state t
  val update: (state -> state) -> unit t
  val get_and_update: (state -> state) -> state t

  val return: 'a -> 'a t
  val fail:    error -> 'a t
  val token: (state -> token -> ('a*state,error) result) -> 'a t

  val map: ('a -> 'b) -> 'a t -> 'b t
  val consumer: 'a t -> 'a t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val (<|>): 'a t -> 'a t -> 'a t
  val backtrackable: 'a t -> 'a t
  val commit: 'a -> 'a t
end
