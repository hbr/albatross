open Common_module_types


module Error  (Exp:ANY) (Sem:ANY):
sig
  type t =
    | Syntax of Exp.t list
    | Semantic of Sem.t
end




module type COMBINATORS =
  sig
    type 'a t
    (*type expect
    type semantic*)
    type error
    val return: 'a -> 'a t
    val succeed: 'a -> 'a t
    val fail:    error -> 'a t
    val consumer: 'a t -> 'a t
    val map:     ('a -> 'b) -> 'a t -> 'b t
    val (>>=):   'a t -> ('a -> 'b t) -> 'b t
    val (<|>):   'a t -> 'a t -> 'a t
    val (<?>):   'a t -> error -> 'a t
    val backtrackable: 'a t -> error -> 'a t

    val optional: 'a t -> 'a option t
    val one_of:   'a t list -> 'a t
    val zero_or_more: 'a t -> 'a list t
    val one_or_more_separated:  'a t -> _ t -> 'a list t
    val zero_or_more_separated: 'a t -> _ t -> 'a list t
    val one_or_more:  'a t -> 'a list t
    val skip_zero_or_more: 'a t -> int t
    val skip_one_or_more:  'a t -> int t

    val (|=): ('a -> 'b) t -> 'a t -> 'b t
    val (|.): 'a t -> _ t -> 'a t
  end



module Make (T:ANY) (S:ANY) (E:ANY) (F:ANY):
sig
  type token = T.t
  type state = S.t
  type final = F.t

  type parser

  include COMBINATORS with type error = E.t


  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val put_token:  parser -> token -> parser
  val state:      parser -> state
  val result:     parser -> (final, error list) result
  val lookahead:  parser -> token list
  val has_succeeded: parser -> bool
  val has_failed: parser -> bool

  val make_parser: state -> final t -> parser

  val get: state t
  val update: (state -> state) -> unit t
  val get_and_update: (state -> state) -> state t

  val token: (state -> token -> ('a*state,error) result) -> 'a t
end
