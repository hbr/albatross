open Support
open Term
open Signature

type t

val empty: unit -> t

val has_implication: t -> bool

val implication_index: t -> int

val implication_chain: term -> int -> t
  -> (term list * term) list  (* still used in prover.ml *)

val implication_term: term -> term -> int -> t -> term

val expand_term: term->int->t->term

val normalize_term: term->int->t->term

val find_funcs: feature_name -> int -> t -> (int * TVars.t * Sign.t) list

val put:
    feature_name withinfo -> entities list withinfo -> return_type
      -> feature_body option ->
        bool -> Class_table.t -> t -> unit

val typed_term: info_expression -> term array -> int array -> term array
  -> Class_table.t -> t -> term * term

val assertion_term: info_expression -> term array -> int array -> term array
  -> Class_table.t -> t -> term

val term: info_expression -> term array -> int array -> term array
  -> Class_table.t -> t -> term

val term_to_string: term -> int array -> t -> string

val raw_term_to_string: term -> int -> t -> string

val print: Class_table.t -> t -> unit

