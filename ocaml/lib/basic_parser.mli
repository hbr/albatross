open Common_module_types
open Parse_combinators

module Basic (T:ANY) (S:ANY) (E:ANY) (F:ANY):
sig
  include BASIC with type token = T.t and
                     type error = E.t
  type final = F.t
  type state = S.t

  type parser

  val parser: state -> final t -> parser

  val expect: (state -> token -> 'a res * state) -> 'a t
  val get: state t
  val put: state -> unit t
  val update: (state -> state) -> unit t

  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val state: parser -> state
  val result: parser -> final res
  val lookahead: parser -> token list

  val put_token: parser -> token -> parser
end
