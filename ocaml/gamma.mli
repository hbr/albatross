open Alba2_common

module Term = Term2

type constraint_list = (int*int*bool) list

module Definition:
sig
  type t
  val name: t -> Feature_name.t option
  val typ:  t -> Term.typ
  val term: t -> Term.t
  val constraints: t -> constraint_list
  val make: Feature_name.t option -> Term.typ -> Term.t -> constraint_list -> t
  val make_simple: string option -> Term.typ -> Term.t -> constraint_list -> t
end

type t
val empty: t

val count_sorts: t -> int
val sort_variables: t -> Sorts.Variables.t
val push_sorts: int -> (int*int*bool) list -> t -> t

val count: t -> int
val entry_type: int -> t -> Term.typ
val name: int -> t -> Feature_name.t option
val has_definition: int -> t -> bool
val definition: int -> t -> Term.t
val is_constructor: int -> t -> bool
val constructor_offset: int -> t -> int
val push: Feature_name.t option -> Term.typ -> t -> t
val push_simple: string option -> Term.typ -> t -> t
val push_definition: Definition.t -> t -> t
val push_n: int -> (int -> Term.fname_type) -> t -> t
val push_unnamed: Term.typ -> t -> t
val push_arguments: Term.arguments -> t -> t
val push_fixpoint: Term.fixpoint -> t -> t
val push_ind_types_params: Inductive.t -> t -> t
val push_inductive: Inductive.t -> t -> t
