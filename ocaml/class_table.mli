(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

(** Structure that implements a table of all classes in the system *)


open Support
open Term
open Signature
open Container

type formal = int * type_term

type t

val dummy_index:     int
val boolean_index:   int
val any_index:       int
val predicate_index: int
val function_index:  int
val tuple_index:     int


val result_type_of_compound: term -> int -> term

val base_table: unit -> t

val put_formal: int withinfo -> type_t withinfo -> t -> unit

val module_table: t -> Module_table.t

val has_current_module: t -> bool
    (** Is there a current module? *)

val current_module: t -> int
    (** The current module *)

val count_modules: t -> int
    (** The number of modules in the system *)

val find_module: int -> int list -> t -> int
    (** [find_module name lib ct] finds the module [lib.name] in [ct] *)

val used_modules: int -> t -> IntSet.t
  (** [used_modules mdl ct] returns the used modules of module [mdl] *)


val module_name: int -> t -> string
    (** [module_name mdl ct] returns the name of the module [mdl] *)


val add_module:   int -> int list -> int -> IntSet.t -> t -> unit
    (** [add_module name lib mode used ct] adds the module [name,lib] to the
        module table, puts it into the mode [mode] and sets the used modules
        to [used]. It resets the formal generics of the class table [ct] and
        in case of private mode adds all builtin classes which belong to this
        module. *)

val is_private: t -> bool
   (** Are we within the implementation of a module? *)

val is_public:  t -> bool
   (** Are we either in checking or using an interface? *)

val is_interface_use:  t -> bool
   (** Are we using an interface? *)


val count: t -> int

val class_symbol: int -> t -> int

val class_name:   int -> t -> string

val class_type: int -> t -> type_term*Tvars.t

val descendants: int -> t -> IntSet.t
    (** [descendants cls ct] returns the set of descendants of the class [cls] *)

val add_feature:  (int*feature_name*type_term*int) -> int -> bool -> t -> unit
    (** [add_feature (fidx,fn,tp,nfgs) cls is_def ct] adds the feature
        [fidx,fn,tp,tvs] to the class [cls] as deferred or effective depending on
        the value of [is_def] *)

val find_features: (feature_name*type_term*int) -> int -> t -> (int*Term_sub.t) list
    (** [find_features (fn,tp,nfgs) cls ct] finds all features of the class
        [cls] with the name [fn] which can be unified with [tp] with [nfgs]
        formal generics *)

val add_assertion:  int -> int -> bool -> t -> unit

val deferred_features: int -> t -> int list
   (** [deferred features cls ct]: The list of deferred features of the class
       [cls] *)

val effective_features: int -> t -> int list
   (** [effective features cls ct]: The list of effective features of the class
       [cls] *)

val owner: Tvars.t -> Sign.t -> t -> int

val check_deferred:  int -> info -> t -> unit

val find:  int -> t -> int
val find_in_module: int -> t -> int

val downgrade_signature: int -> Sign.t -> int -> Sign.t
  (** [downgrade_signature ntvs sign nargs] downgrades the constant signature
      [ntvs,sign] (i.e. a signature which has no arguments and is therefore
      not callable) into a function signature with [nargs] arguments or
      downgrade a callable signature with one argument into callable signature
      with more than one argument.

      This is possible only if the result type of [sign] is a function or a
      predicate or a dummy type and the corresponding actual generic is a
      tuple with the corresponding number of elements in case that [nargs > 1]
      or if the signature is callable with a tuple and the tuple has enough
      argments.  *)

val update: int -> header_mark withinfo -> formal_generics -> t -> unit

val add: header_mark withinfo -> int withinfo -> formal_generics -> t -> unit

val parent_type:    int -> type_t withinfo -> t -> int * type_term array

val inherited_ancestors:
    int -> int -> type_term array -> info -> t -> (int * type_term array) list
   (** [inherited_ancestors cls par par_args info ct] calculates a list of
       inherited ancestors in case the class [cls] inherits
       [par[par_args]]. The returned list contains [par[par_args]] and all
       implicitly inherited ancestors unless they are already in the set of
       ancestors.

       If [par[par_args]] is already in the set of ancestors, then the
       returned list is empty. However it is checked if the actual generics
       coincide with the actual generics of the parent which is already in the
       set of ancestors. If this is not the case an error message is
       triggered.  *)

val do_inherit: int -> (int * type_term array) list -> t -> unit
   (** [do_inherit cls anc_lst ct] let the class [cls] inherit all ancestors
       of the list [anc_lst] *)


val boolean_type:   int -> term

val is_boolean_binary: Sign.t -> int -> bool
val is_boolean_unary:  Sign.t -> int -> bool

val to_dummy: int -> Sign.t -> type_term
   (** [to_dummy ntvs s] converts the signature [s] with [ntvs] type variables
       into the dummy type [dum[tup,rt]] where [tup] is a single type or a
       tuple which represents the arguments and [rt] is the return type of the
       signature.

       In case that [s] is a constant signature which is a
       predicate or a function, the class is updated by the dummy index.

       If the constant signature is neither a predicate nor a function then
       the result type of the signature is returned. *)



val formal_arguments: entities list withinfo -> Tvars.t -> t -> formal array

val result_type: return_type -> Tvars.t -> t -> Result_type.t

val satisfies: type_term -> Tvars.t -> type_term -> Tvars.t -> t -> bool
  (** [satisfies tp1 tvs1 tp2 tvs2 ct]: Does the type [tp1,tvs1] satisfy the
      type [tp2,tvs2] *)

val type2string: term -> int -> int array -> t -> string

val string_of_signature: Sign.t -> Tvars.t -> t -> string

val string_of_complete_signature: Sign.t -> Tvars.t -> t -> string

val string_of_type: type_term -> Tvars.t -> t -> string

val string_of_concepts: Tvars.t -> t -> string

val string_of_fgconcepts: Tvars.t -> t -> string

val string_of_tvs: Tvars.t -> t -> string

val string_of_tvs_sub: TVars_sub.t -> t -> string
