open Alba2_common

module Term = Term2

type constraint_list = (int*int*bool) list

module Definition:
sig
  type t
  val name: t -> Feature_name.t option
  val typ:  t -> Term.typ
  val term: t -> Term.t
  val make: Feature_name.t option -> Term.typ -> Term.t -> t
  val make_simple: string option -> Term.typ -> Term.t -> t
end

type t
val empty: t


val count: t -> int
val is_valid: int -> t -> bool
val to_level: int -> t -> int
val to_index: int -> t -> int
val entry_type: int -> t -> Term.typ
val name: int -> t -> Feature_name.t option
val has_definition: int -> t -> bool
val definition: int -> t -> Term.t
val inductive_index: Term.t -> t -> (int*Inductive.t) option
val constructor_index: Term.t -> t -> (int * int * Inductive.t) option

val count_inductive_params_and_types: int -> t -> (int * int) option
val constructor_types: int -> Term.t list -> t -> Term.typ list
val constructor_arguments: int -> int -> t -> Inductive.carg_class list

val inductive_family: int -> t -> (int * Inductive.t) option
(** [inductive_family i c] returns the inductive family of the variable [i]
   and the position of the type of [i] within the family. *)

val is_constructor: int -> t -> bool
val constructor_offset: int -> t -> int
val constructor_of_inductive_variable: int -> Term2.t -> t -> int
val push: Feature_name.t option -> Term.typ -> t -> t
val push_simple: string option -> Term.typ -> t -> t
val push_definition: Definition.t -> t -> t
val push_n: int -> (int -> Term.fname_type) -> t -> t
val push_unnamed: Term.typ -> t -> t
val push_arguments: Term.arguments -> t -> t
val push_argument_list: Term.argument_list -> t -> t
val push_fixpoint: Term.fixpoint -> t -> t
val push_lambda: Term.t -> t -> Term.t * t
val push_ind_types_params: Inductive.t -> t -> t
val push_inductive: Inductive.t -> t -> t
