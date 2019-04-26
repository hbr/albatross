open Common_module_types

module Make (T:ANY) (S:ANY) (E:ANY) (F:ANY):
sig
  type token = T.t
  type error = E.t
  type state = S.t
  type final = F.t

  type parser

  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val put_token:  parser -> token -> parser
  val state:      parser -> state
  val result:     parser -> (final, error list) result
  val lookahead:  parser -> token list

  type _ t

  val make_parser: state -> final t -> parser

  val succeed: 'a -> 'a t
  val fail:    error -> 'a t
  val token: (state -> token -> ('a*state,error) result) -> 'a t

  val map: ('a -> 'b) -> 'a t -> 'b t
  val consumer: 'a t -> 'a t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val (<|>): 'a t -> 'a t -> 'a t
  val (<?>): 'a t -> error list -> 'a t
  val backtrackable: 'a t -> 'a t
  val commit: 'a -> 'a t
end
