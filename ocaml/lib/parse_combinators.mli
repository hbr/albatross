module type BASIC =
  sig
    type token
    type error
    type 'a res = ('a,error) result

    include Monad.MONAD

    val succeed: 'a -> 'a t
    val fail: error -> 'a t
    val consumer: 'a t -> 'a t
    val backtrackable: 'a t -> 'a t
    val commit: 'a -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
  end





module type COMBINATORS =
  functor (P:BASIC) ->
  sig
    val (>>-): 'a P.t -> ('a -> 'b P.t) -> 'b P.t
    val (>>|): 'a P.t -> (P.error -> 'a P.t) -> 'a P.t
    val optional: 'a P.t -> 'a option P.t
    val one_of: 'a P.t list -> (P.error list -> P.error) -> 'a P.t
    val zero_or_more: 'a P.t -> 'a list P.t
    val one_or_more:  'a P.t -> 'a list P.t
    val (|=): ('a -> 'b) P.t -> 'a P.t -> 'b P.t
    val (|.): 'v P.t -> 'a P.t -> 'v P.t
  end


module Combinators: COMBINATORS
