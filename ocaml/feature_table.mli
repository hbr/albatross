open Support
open Term
open Signature

(** Structure that implements a table of all global features in the system *)

type t

type implementation_status = No_implementation | Builtin | Deferred

val count:      t -> int
    (** The number of features in the table *)

val implication_index: int
val all_index:         int
val some_index:        int

val base_table: unit -> t

val module_table: t -> Module_table.t
val class_table:  t -> Class_table.t

val implication_term: term -> term -> int -> t -> term

val expand_term: term->int->t->term
  (** [expand_term t nbound ft] expands the definitions of the term [t] within
      an environment with [nbound] bound variables, i.e. a variable [i] with
      [nbound<=i] refers to the global feature [i-nbound] *)


val normalize_term: term->int->t->term
  (** [normalize_term t nbound ft] expands the definitions of the term [t] and
     beta reduce it within an environment with [nbound] bound variables,
     i.e. a variable [i] with [nbound<=i] refers to the global feature
     [i-nbound] *)


val find_funcs: feature_name -> int -> t -> (int * TVars.t * Sign.t) list
  (** [find_funcs fn nargs ft] finds all functions with name [fn] and [nargs]
      arguments in the feature table [ft] and returns the indices with the
      corresponding type variables and signatures. The signatures will be up-
      or downgraded if necessary and possible to match the requirement to have
      [nargs] arguments. *)


val put_function:
    feature_name withinfo -> int array -> type_term array -> int array
      -> Sign.t -> implementation_status -> term option -> t -> unit
  (** [put_function fn fgnames concepts fnms sign imp_stat term_opt ft] adds
      the function with then name [fn], the formal generics
      [fgnames,concepts], the arguments [fnms], the signature [sign] the
      implementation status [imp_stat] and an optional definition term
      [term_opt] to the feature table [ft] *)


val term_to_string: term -> int array -> t -> string

val do_inherit: int -> int -> type_term array -> info -> t -> unit
  (** [do_inherit cls_idx par_idx par_args info ft] let the class [cls_idx]
      inherit the features from the parent [par_idx[par_args]]. *)

val print: t -> unit

