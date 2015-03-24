(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Container
open Term
open Proof


type t

val context: t -> Context.t
val module_table: t  -> Module_table.t
val class_table: t   -> Class_table.t
val feature_table: t -> Feature_table.t

val is_private:         t -> bool
val is_public:          t -> bool
val is_interface_use:   t -> bool
val is_interface_check: t -> bool
val is_tracing:         t -> bool
val verbosity:          t -> int
val trace_prefix:       t -> string
val trace_prefix_0:     t -> string
val prover_strength:    t -> int
val add_used_module:    (int * int list) -> IntSet.t -> t -> unit
val add_current_module: int -> IntSet.t -> t -> unit
val set_interface_check: IntSet.t -> t -> unit

val is_global: t -> bool


val string_of_term: term -> t -> string
val string_of_term_i: int -> t -> string

val make:      int -> t

val push: entities list withinfo -> t -> t
val push_untyped: int array -> t -> t
val pop:          t -> t

val depth:     t -> int

val find:               term -> t -> int
val has:                term -> t -> bool
val add_assumption:     term -> t -> int
val add_axiom:          term -> t -> int
val add_mp:             int -> int -> bool -> t -> int
val has_work:           t -> bool
val work:               t -> int list
val close_step:         t -> unit
val close:              t -> unit
val close_assumptions:  t -> unit
val discharged:         int  -> t -> term * proof_term
val add_proved_0:       bool -> int -> int -> term -> proof_term -> int -> t -> int
val add_proved:         bool -> int -> int -> term -> proof_term -> t -> int
val add_proved_list:    bool -> int -> int -> (term*proof_term) list -> t -> unit
val premises:           int -> t -> (term*bool) list
val previous_schematic: int  -> t -> int option
val trying_goal:        term -> t -> unit
val failed_goal:        term -> t -> unit
val proved_goal:        term -> t -> unit

val find_goal:          term -> t -> int
    (** Find a term which exactly matches the goal or which can be specialized to
        match the goal. Add the specialization if necessary and return the index
        of the term which exactly matches or raise [Not_found]. *)

val find_backward_goal: term -> IntSet.t -> t -> int list
    (** Add all possible fully specialized backward rules whose target matches the
        goal by specialization, expansion, beta reduction.
        Return the backward rules whose target matches the goal exactly. *)

val split_implication:  term -> t -> term * term
val split_all_quantified: term -> t -> int * int array * term
val implication_chain:  term list -> term -> t -> term

val count:          t -> int
val count_previous: t -> int
val count_global:   t -> int

val term_orig:      int -> t -> term * int
val term:           int -> t -> term
val is_assumption:  int -> t -> bool

val check_deferred: t -> unit
val owner:          t -> int
val anchor_class:   t -> int

val inherit_parent: int -> int -> type_term array -> info -> t -> unit
    (** [inherit_parent cls par par_args info pc] *)

val add_potential_equalities: int -> t -> unit

val check_interface: t -> unit
