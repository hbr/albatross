(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
 *)

(** Context with stacked declarations of formal arguments *)


open Signature
open Support
open Term
open Container

type t
val make:  int -> t

val module_table: t -> Module_table.t
val class_table: t  -> Class_table.t
val feature_table:t -> Feature_table.t

val current_module:     t -> int
val used_modules:       int -> t -> IntSet.t
val add_used_module:    (int * int list) -> IntSet.t -> t -> unit
val add_current_module: int -> IntSet.t -> t -> unit
val set_interface_check: IntSet.t -> t -> unit

val is_private:        t -> bool
val is_public:         t -> bool
val is_interface_check:t -> bool
val is_interface_use:  t -> bool
    (** Are we using an interface? *)

val verbosity: t -> int

val find_module:        (int * int list) -> t -> int

val push_with_gap:  entities list withinfo -> return_type -> bool -> bool -> bool
  -> int -> t -> t
val push:  entities list withinfo -> return_type -> bool -> bool -> bool -> t -> t
val push_untyped_with_gap: int array -> bool -> bool -> bool -> int -> t -> t
val push_untyped_gap: int array -> int -> t -> t
val push_untyped:     int array -> t -> t
val push_typed:       formals -> formals -> t -> t
val previous: t -> t
val pop:   t -> t

val is_global:   t -> bool
val is_toplevel: t -> bool
val depth:       t -> int
val arity:       t -> int
val info:        t -> info
val is_outer:    t -> t -> bool

val has_result:  t -> bool
val has_result_variable:  t -> bool
val result_type: t -> type_term

val count_type_variables: t -> int
    (** The number of cumulated type variables in this context and all
        preceeding contexts *)

val count_local_type_variables: t -> int
    (** The number of type variables in this context without all preceeding
        contexts *)

val count_formal_generics: t -> int
    (** The number of formal generics in this context and all preceeding
        contexts *)

val count_last_arguments:  t -> int
    (** The number of formal arguments in this context without the preceeding
        contexts *)

val count_last_variables:  t -> int
    (** The number of variables (arguments + result) in this context without
        the preceeding contexts *)

val count_last_formal_generics:  t -> int
    (** The number of formal generics in this context without the preceeding
        contexts *)

val count_last_type_variables: t -> int
    (** The number of type variables in this context without the preceeding
        contexts *)

val count_variables:  t -> int
    (** The number of variables in this context and all preceeding
        contexts *)

val ntvs: t -> int

val implication_index: t -> int
val is_equality_index: int -> t -> bool

val make_lambda:
    int -> int array -> term list -> term -> bool -> int -> type_term -> t -> term
val make_application: term -> arguments -> type_term -> int -> bool -> t -> term
val beta_reduce:      int -> term -> type_term -> term array -> int -> t -> term

val quantified:      bool -> int -> formals -> formals -> term -> t -> term
val all_quantified:  int -> formals -> formals -> term -> t -> term
val some_quantified: int -> formals -> formals -> term -> t -> term
val prenex_term:     term -> t -> term

val variable_name: int -> t -> int
    (** The name of the [i]th variable argument *)

val variable_type: int -> t -> type_term
    (** The type of the [i]th variable argument *)

val variable_index: int -> t -> int

val unique_name:  int -> t -> int
val unique_names: int array -> t -> int array

val fgnames: t   -> int array

val fgnames:    t -> int array
val fgconcepts: t -> types
val local_argnames: t -> int array
val local_types:    t -> types
val local_formals:  t -> formals
val local_fgs: t -> formals
val local_types_reduced: t -> types

val tvars: t -> Tvars.t
val tvars_sub: t -> TVars_sub.t

val ith_arguments_string: int -> t -> string
val local_arguments_string: t -> string

val type_variables: t -> TVars_sub.t
    (** The type variables and their substitutions *)

val boolean: t -> term

val function_index: t -> int

val type_of_term: term -> t -> type_term
val tuple_of_types: types -> t -> type_term
val tuple_of_terms: arguments -> t -> type_term
val predicate_of_type: type_term -> t -> type_term
val predicate_of_term: term -> t -> type_term
val function_of_types: types -> type_term -> t -> type_term
val function_of_terms: arguments -> term -> t -> type_term

val update_types: type_term array -> t -> unit

val string_of_term0:      term -> bool -> bool -> int -> t -> string
val string_of_term:       term -> t -> string
val string_long_of_term:  term -> t -> string
val string_of_term_array: string -> term array -> t -> string
val string_of_arguments:  term array -> t -> string
val string_of_signature:  Sign.t -> t -> string
val string_of_type: type_term -> t -> string
val string_of_type_array: string -> agens -> t -> string
val string_of_ags: agens -> t -> string
val signature_string: t -> string
val named_signature_string: t -> string
val signature:  t -> Sign.t

val transformed_term0: term -> int -> t -> t -> term
val transformed_term:  term -> t -> t -> term

val owner:          t -> int
val anchor_class:   t -> int
val check_deferred: t -> unit

val is_case_match_expression: term -> t -> bool
val find_identifier: int ->          int -> t -> (int * Tvars.t * Sign.t) list
val find_feature:    feature_name -> int -> t -> (int * Tvars.t * Sign.t) list
val variable_data:   int -> t -> Tvars.t * Sign.t
val variable:        int -> t -> int * Tvars.t * Sign.t

val put_formal_generic: int withinfo -> type_t withinfo -> t -> unit

val complexity: term -> t -> int

val split_equality: term -> int -> t -> int * int * term * term
val definition: int -> int -> agens -> t -> int * int array * term
val arity:      int -> int -> t -> int
val is_inductive_set: int -> t -> bool
val inductive_set: term -> t -> term


val preconditions: int -> int -> t -> int * int array * term list
val postconditions: int -> int -> t -> int * int array * term list
val function_property: int -> int -> term array -> t -> term
val has_preconditions: int -> int -> t -> bool
val term_preconditions: term -> t -> term list

val domain_of_lambda:  int -> int array -> term list -> type_term -> int -> t -> term
val domain_of_feature: int -> int -> agens -> t -> term

val existence_condition: term list -> t -> term
val uniqueness_condition: term list -> t -> term
val function_postconditions: int -> term list -> t -> term list

val get_type: type_t withinfo -> t -> type_term

val downgrade_term: term -> int -> t -> term

val arity_of_downgraded_type: type_term -> t -> int
val specialized: term -> t -> term
val is_well_typed:    term -> t -> bool
