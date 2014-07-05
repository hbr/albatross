(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)
open Signature
open Support
open Term
open Container

type t
type proof_term
val make:  unit -> t

val class_table: t -> Class_table.t
val feature_table:t -> Feature_table.t

val has_current_module: t -> bool
val current_module:     t -> int
val find_module:        int -> int list -> t -> int
val add_used_modules:   int -> info     -> t -> unit
val push_module:        int -> int list -> t -> unit
val pop_module:         t -> unit

val push:  entities list withinfo -> return_type -> t -> unit
val push_empty: t -> unit
val push_untyped: int array -> t -> unit
val pop:   t -> unit
val print: t -> unit
val read_trace_info: t -> unit

val is_global:   t -> bool
val is_toplevel: t -> bool
val depth:       t -> int
val arity:     t -> int
val argument:  int -> t -> int * TVars.t * Sign.t

val result_type: t -> type_term

val count_type_variables: t -> int

val fgnames: t -> int array

val type_variables: t -> TVars_sub.t

val boolean: t -> term

val concept_satisfies_concept: type_term -> type_term -> t -> bool
val type_satisfies_concept:    type_term -> type_term -> t -> bool

val update_type_variables: TVars_sub.t -> t -> unit

val string_of_term: term -> t -> string
val sign2string:    Sign.t -> t -> string
val signature_string: t -> string
val named_signature_string: t -> string

val find_identifier: int ->          int -> t -> (int * TVars.t * Sign.t) list
val find_feature:    feature_name -> int -> t -> (int * TVars.t * Sign.t) list

val put_global_function:
    feature_name withinfo  -> Feature_table.implementation_status ->
      term option -> t -> unit

val implication_id: t -> int

val put_formal_generic: int withinfo -> type_t withinfo -> t -> unit
val put_class: header_mark withinfo -> int withinfo
  -> formal_generics -> inherit_clause list -> t -> unit

val all_quantified_outer: term -> t -> term
val implication_chain:  term list -> term -> t -> term
val split_implication:    term -> t -> term * term
val split_all_quantified: term -> t -> int * int array * term

val count_assertions: t -> int
val find_assertion: term -> t -> int
val has_assertion:  term -> t -> bool
val expanded_term:  term -> t -> term
val add_assumption: term -> t -> int
val add_axiom:      term -> t -> int
val discharged:     int -> t -> term * proof_term
val add_proved:     term -> proof_term -> IntSet.t -> t -> unit
val add_backward:   term -> t -> unit
val assertion:      int -> t -> term
val backward_set:   term -> t -> int list
val backward_data:  int  -> t -> term list * IntSet.t

val print_all_local_assertions: t -> unit
val print_global_assertions:    t -> unit
