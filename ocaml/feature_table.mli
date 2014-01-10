open Support
open Term
open Type

type t

val empty: unit -> t

val has_implication: t -> bool

val implication_index: t -> int

val implication_chain: term -> int -> t
  -> (term list * term) list  (* still used in prover.ml *)

val implication_term: term -> term -> int -> t -> term

val expand_term: term->int->t->term

val normalize_term: term->int->t->term

val put:
    feature_name withinfo -> entities list withinfo -> return_type
      -> feature_body option ->
        Block_stack.t -> Class_table.t -> t -> unit

val typed_term: info_expression -> typ array -> int array -> typ array
  -> Class_table.t -> t -> term * typ

val assertion_term: info_expression -> typ array -> int array -> typ array
  -> Class_table.t -> t -> term

val term: info_expression -> typ array -> int array -> typ array
  -> Class_table.t -> t -> term

val term_to_string: term -> int array -> t -> string

val raw_term_to_string: term -> int -> t -> string

val print: Class_table.t -> t -> unit

