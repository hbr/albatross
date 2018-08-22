open Alba2_common

module Term = Term2

type name_type = string option * Term.typ
type fname_type = Feature_name.t option * Term.typ
type gamma = fname_type array

module Constructor:
sig
  type t
  val make: Feature_name.t option -> Term.arguments -> Term.t array -> t
  val name: t -> Feature_name.t option
  val cargs: t -> Term.arguments
  val ctype: int -> int -> int -> t -> Term.typ
end

module Inductive:
sig
  type t
  val nparams: t -> int
  val ntypes: t -> int
  val nconstructors: int -> t -> int
  val parameter: int -> t -> name_type
  val itype0: int -> t -> fname_type
  val itype: int -> t -> fname_type
  val ctype0: int -> int -> t -> fname_type
  val cargs: int -> int -> t -> Term.arguments
  val is_valid_iargs: int -> int -> t -> bool
  val make: Term.arguments -> gamma -> Constructor.t array array -> t
  val make_simple: Feature_name.t option -> Term.arguments -> Term.typ ->
                   Constructor.t array -> t
  val make_natural: t
  val make_false: t
  val make_true: t
  val make_and: t
  val make_or: t
  val make_equal: int -> t
  val make_list: int -> t
  val make_accessible: int -> t
end

type t
val empty: t

val count_sorts: t -> int
val sortvariable_le: t -> int -> int -> bool
val sortvariable_lt: t -> int -> int -> bool
val push_sorts: int -> (int*int*bool) list -> t -> t

val count: t -> int
val entry_type: int -> t -> Term.typ
val has_definition: int -> t -> bool
val definition: int -> t -> Term.t
val is_constructor: int -> t -> bool
val constructor_offset: int -> t -> int
val push: Feature_name.t option -> Term.typ -> t -> t
val push_unnamed: Term.typ -> t -> t
val push_inductive: Inductive.t -> t -> t
