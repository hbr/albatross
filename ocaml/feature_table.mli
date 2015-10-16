(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Signature

(** Structure that implements a table of all global features in the system *)

type t

val verbosity:  t -> int

val count:      t -> int
    (** The number of features in the table *)

val count_fgs:  int -> t -> int
    (** [count_fgs i ft] returns the number of formal generics of the feature [i] *)

val anchor: int -> t -> int
    (** [anchor i ft] returns the formal generic which serves as an anchor for
        inheritance. Raises [Not_found] if there is no unique anchor *)


val class_of_feature:  int -> t -> int
val arity: int -> t -> int

val has_anchor: int -> t -> bool

val is_deferred: int -> t -> bool

val is_ghost_function: int -> t -> bool

val seeded_term: term -> int -> t -> term

val variant: int -> int -> t -> int
    (** [variant idx cls ft] returns the variant of the feature [idx] in the
        class [cls] *)

val private_variant: int -> int -> t -> int

val variant_term: term -> int -> int -> int -> t -> term
    (** [variant t nb base_cls cls ft] returns the variant of the term [t]
        with [nb] bound variables of the base class [base_cls] in the class
        [cls] *)

val has_variant: int -> int -> t -> bool
val has_private_variant: int -> int -> t -> bool

val variant_feature: int -> int -> type_term array -> Tvars.t -> t -> int

val find_variant_candidate: int -> int -> t -> int

val has_variant_candidate: int -> int -> t -> bool

val string_of_signature: int -> t -> string

val is_ghost_term: term -> int -> t -> bool
val is_ghost_specification: Feature.Spec.t -> t -> bool

val implication_index: int
val false_index:       int
val true_index:        int
val not_index:         int
val and_index:         int
val or_index:          int
val eq_index:          int
val in_index:          int
val domain_index:      int
val tuple_index:       int
val first_index:       int
val second_index:      int

(*val standard_argnames: int -> int array*)

val base_table: int -> t

val class_table:  t -> Class_table.t

val has_current_module: t -> bool
    (** Is there a current module? *)

val current_module:  t -> int
    (** The current module *)

val count_modules: t -> int
    (** The number of modules in the system *)

val find_module: (int * int list) -> t -> int
    (** [find_module name lib ft] finds the module [lib.name] in [ft] *)

val module_name: int -> t -> string
    (** [module_name mdl ft] returns the name of the module [mdl] *)

val used_modules: int -> t -> IntSet.t
  (** [used_modules mdl ft] returns the used modules of module [mdl] *)

val add_used_module:    (int * int list) -> IntSet.t -> t -> unit
val add_current_module: int -> IntSet.t -> t -> unit
val set_interface_check: IntSet.t -> t -> unit

val is_private: t -> bool
   (** Are we within the implementation of a module? *)

val is_public:  t -> bool
   (** Are we either using or  checking an interface? *)

val is_interface_check:  t -> bool
   (** Are we checking an interface? *)

val is_interface_use:  t -> bool
   (** Are we using an interface? *)



val split_equality: term -> int -> t -> int * int * term * term
    (** [split_equality t nbenv ft] returns the number of arguments, the
        equality in and the left and right hand side of an equality or raises
        [Not_found] if [t] is not an equality. *)

val is_equality: term -> int -> t -> bool
    (** [is_equality t nbenv ft] tells if the term [t] is an equality term *)


val equality_index: int -> t -> int
    (** [equality_index cls ft] returns the equality index of the class [cls]. *)

val equality_index_of_type: term -> Tvars.t -> t -> int
    (** [equality_index tp ft] returns the equality index of the type [tp]. *)


val feature_call: int -> int -> term array -> t -> term

val definition: int -> int -> t -> int * int array * term
    (** [definition idx nb ft] returns the definition of the feature
        [idx]. Raises [Not_found] if feature [idx] has no definition *)

val has_definition: int -> t -> bool

val is_inductive_set: int -> int -> t -> bool
val inductive_set: int -> term array -> int -> t -> term

val specification: int -> t -> term list

val feature_name: int -> t -> string

val is_deferred: int -> t -> bool
val signature: int -> t -> Tvars.t * Sign.t
val argument_names: int -> t -> int array
val private_body: int -> t -> Feature.body
val body:         int -> t -> Feature.body

val is_constructor:    int -> t -> bool
val inductive_arguments: int -> t -> int list
val constructor_rule:  int -> term -> int -> t
  -> int * int array * term list * term
val induction_law:     int -> term -> int -> int -> t -> term
val pattern_subterms:  int -> term -> int -> t -> (int*term*int) list
val peer_constructors: int -> t -> IntSet.t
val is_case_matching:  term -> int -> term -> int -> t -> bool
val peer_matches:      int -> int -> t -> (int*term) list
val unmatched_inspect_cases: term array -> int -> t -> (int * term) list
val inspect_unfolded:  info ->term array -> int -> t -> term array

val is_feature_public: int -> t -> bool
val is_term_public:    term -> int -> t -> bool

val owner: int -> t -> int

val add_tuple_accessors: term -> int -> int -> t -> term
val make_lambda: int -> int array -> term list -> term -> bool -> int -> t -> term
val make_application: term -> term array -> bool -> int -> t -> term
val beta_reduce:      int -> term -> term array -> int -> t -> term
val normalize_lambdas:term -> int -> t -> term
val remove_tuple_accessors: term -> int -> int -> t -> term
val tuple_of_args:    term array -> int -> t -> term
val args_of_tuple:    term -> int -> t -> term array
val args_of_tuple_ext:term -> int -> int -> t -> term array

val prenex: term -> int -> t -> term

val preconditions:  int -> int -> t -> int * int array * term list
val postconditions: int -> int -> t -> int * int array * term list
val count_postconditions: int -> t -> int
val function_property: int -> int -> int -> term array -> t -> term

val find_funcs: feature_name -> int -> t -> (int * Tvars.t * Sign.t) list
  (** [find_funcs fn nargs ft] finds all functions with name [fn] and [nargs]
      arguments in the feature table [ft] and returns the indices with the
      corresponding type variables and signatures. The signatures will be up-
      or downgraded if necessary and possible to match the requirement to have
      [nargs] arguments. *)


val find_with_signature: feature_name -> Tvars.t -> Sign.t -> t -> int

val add_feature: feature_name withinfo -> Tvars.t -> int array -> Sign.t
  -> Feature.implementation -> t -> unit

val update_specification: int -> Feature.Spec.t -> t -> unit
val set_owner_class:      int -> int -> t -> unit
val export_feature: int -> bool -> t -> unit

val add_function:
    feature_name withinfo -> Tvars.t -> int array -> Sign.t
      -> Feature.body -> t -> unit
  (** [add_function fn tvs fnms sign imp_stat term_opt ft] adds the function
      with then name [fn], the formal generics of [tvs], the arguments [fnms],
      the signature [sign] the implementation status [imp_stat] and an
      optional definition term [term_opt] to the feature table [ft] *)

val update_function:
    int -> info  -> bool -> Feature.body -> t -> unit
  (** [update_function fn tvs fnms sign imp_stat term_opt ft] updates the function
      with then name [fn], the formal generics of [tvs], the arguments [fnms],
      the signature [sign] the implementation status [imp_stat] and an
      optional definition term [term_opt] to the feature table [ft] *)



val term_to_string: term -> bool -> int -> int array -> t -> string

val inherit_new_effective: int -> int -> bool -> t -> int

val inherit_feature: int -> int -> int -> bool -> t -> unit

val export_feature: int -> bool -> t -> unit

val check_interface: t -> unit

val downgrade_term: term -> int -> t -> term

val adapt_names: int array -> int array -> int array

val domain_of_feature: int -> int -> t -> term
