open Common

module type COMBINATORS =
  sig
    type 'a tp
    val optional: 'a tp -> 'a option tp
    val one_of: 'a tp list -> 'a tp
    val loop: 'a -> ('a -> ('a,'b) Loop_state.t tp) -> 'b tp
    val zero_or_more: 'a tp -> 'a list tp
    val one_or_more:  'a tp -> 'a list tp
    val skip_zero_or_more: 'a tp -> int tp
    val skip_one_or_more:  'a tp -> int tp
    val zero_or_more_separated: 'a tp -> _ tp -> 'a list tp
    val one_or_more_separated: 'a tp -> _ tp -> 'a list tp
    val (|=): ('a -> 'b) tp -> 'a tp -> 'b tp
    val (|.): 'v tp -> 'a tp -> 'v tp
  end

module type ADD_COMBINATORS =
  functor (P:Generic_parser.BASIC) ->
  sig
    include COMBINATORS with type 'a tp = 'a P.t
  end


module Add_combinators: ADD_COMBINATORS
