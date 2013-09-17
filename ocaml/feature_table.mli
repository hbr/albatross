open Support
open Term
open Type

type t

val empty: unit -> t

val has_implication: t -> bool

val split_implication: term -> int -> t -> term * term

val implication_chain: term -> int -> t
  -> (term list * term) list

val implication_term: term -> term -> int -> t -> term

val expand_term: term->int->t->term

val normalize_term: term->int->t->term

val put:
    feature_name withinfo -> entities list withinfo -> return_type
      -> feature_body option ->
        Block_stack.t -> Class_table.t -> t -> unit

val typed_term: info_expression -> int array -> typ array
  -> Class_table.t -> t -> term * typ

val assertion_term: info_expression -> int array -> typ array
  -> Class_table.t -> t -> term

val term: info_expression -> int array -> typ array
  -> Class_table.t -> t -> term

val term_to_string: term -> int array -> t -> string

val print: Class_table.t -> t -> unit

