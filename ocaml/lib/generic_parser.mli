open Common_module_types


module type BASIC =
  sig
    type n_consumed = int
    type token
    type error
    type state
    type 'a parser

    val put_token:'a parser -> token -> 'a parser
    val put_end:  'a parser -> 'a parser
    val consume:  'a parser -> token list -> 'a parser

    val continue: 'a parser ->
                  (state -> 'a -> n_consumed -> token list -> 'z) ->
                  (state -> 'z) ->
                  (state -> error -> n_consumed -> token list -> 'z) ->
                  'z

    module M: Monad.STATE_WITH_RESULT with type state = state and
                                           type error = error

    type ('a,'z) context

    type ('a,'z) t = ('a,'z) context -> 'z parser

    val parser: ('a,'a) t -> state -> 'a parser

    val backtrack: ('a,'a) t -> ('a,'z) t

    val token: (token -> 'a M.t) -> error -> ('a,'z) t

    val succeed: 'a -> ('a,'z) t
    val fail:    error -> ('a,'z) t

    val (>>=): ('a,'z) t -> ('a -> ('b,'z) t) -> ('b,'z) t
    val catch: ('a,'z) t -> (error -> ('a,'z) t) -> ('a,'z) t
    val map: ('a -> 'b) -> ('a,'z) t -> ('b,'z) t
    val map_error: (error -> error) -> ('a,'z) t -> ('a,'z) t
  end




module type COMBINATOR =
  sig
    include BASIC

    val (>>): ('a,'z) t -> ('b,'z) t -> (('a*'b),'z) t

    val (<|>): ('a,'z) t -> ('a,'z) t -> ('a,'z) t

    val many0: ('a,'z) t -> ('a list,'z) t

    val many1: ('a,'z) t -> ('a list,'z) t

    val many0_separated: ('a,'z) t -> ('b,'z) t -> ('a list,'z) t
    val many1_separated: ('a,'z) t -> ('b,'z) t -> ('a list,'z) t

    val between: ('a,'z) t ->
                 ('b,'z) t ->
                 ('c,'z) t ->
                 ('b,'z) t

    val with_prefix: ('a,'z) t ->
                     ('b,'z) t ->
                     ('b,'z) t

    val with_suffix: ('a,'z) t ->
                     ('b,'z) t ->
                     ('a,'z) t

    val count: int -> int ->
               (int -> error) ->
               ('a,'z) t ->
               ('a list,'z) t

    val optional: ('a,'z) t -> ('a option,'z) t
  end (* COMBINATOR *)


module Basic (Token:ANY) (Error:ANY) (State:ANY)
       : BASIC with type token = Token.t and
                    type error = Error.t and
                    type state = State.t


module Combinator (P:BASIC)
       : COMBINATOR with type token = P.token and
                         type error = P.error and
                         type state = P.state

module Make  (Token:ANY) (Error:ANY) (State:ANY)
       : COMBINATOR with type token = Token.t and
                         type error = Error.t and
                         type state = State.t
