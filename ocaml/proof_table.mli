(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Proof
open Support
open Container

type t

val context: t -> Context.t
val class_table: t -> Class_table.t

val is_private:         t -> bool
val is_public:          t -> bool
val is_interface_use:   t -> bool
val is_interface_check: t -> bool
val add_used_module:    (int * int list) -> IntSet.t -> t -> unit
val add_current_module: int -> IntSet.t -> t -> unit
val set_interface_check: IntSet.t -> t -> unit


val depth:       t -> int
val is_global:   t -> bool
val is_local:    t -> bool
val is_toplevel: t -> bool
val count:       t -> int
val count_previous: t -> int
val count_global:   t -> int
val count_arguments:       t -> int
val count_last_arguments:  t -> int
val last_arguments_string: t -> string
val names:       t -> int array
val all_id:      t -> int
val some_id:     t -> int
val imp_id:      t -> int

val prenex_term: term -> t -> term
val expand_term: term -> t -> term
val equivalent:  term -> term -> t -> bool
val split_implication: term -> t -> term * term
val split_all_quantified: term -> t -> int * int array * term
val split_some_quantified: term -> t -> int * int array * term
val split_equality: term -> int -> t -> int * term * term
val implication: term -> term -> t -> term
val all_quantified:  int -> int array -> term -> t -> term
val all_quantified_outer: term -> t -> term
val implication_chain: term list -> term -> t -> term
val someelim:  int -> t -> term

val term:          int -> t -> term * int
val proof_term:    int -> t -> proof_term
val nbenv_term:    int -> t -> int
val local_term:    int -> t -> term
val is_assumption: int -> t -> bool
val variant:       int -> int -> int -> t -> term

val specialized: int -> term array -> int -> t -> term
val reconstruct_evaluation: Eval.t -> t -> term*term

val make: int -> t
val push: entities list withinfo -> t -> t
val push_untyped: int array -> t -> t
val pop:  t -> t

val definition: int -> int -> t -> term
val expanded_definition: int -> int -> t -> term

val is_proof_pair:  term -> proof_term -> t -> bool

val add_proved:        term -> proof_term -> int -> t -> unit

val add_axiom:      term -> t -> unit
val add_assumption: term -> t -> unit
val add_mp:         term -> int -> int -> t -> unit
val add_eval:       term -> int -> Eval.t -> t -> unit
val add_eval_backward:   term -> term -> Eval.t -> t -> unit
val add_witness:    term -> int -> int array -> term -> term array -> t -> unit
val add_someelim:   int -> term -> t -> unit
val add_specialize: term -> int -> term array -> t -> unit
val add_inherited:  term -> int -> int -> int -> t -> unit

val discharged:   int -> t -> term * proof_term
