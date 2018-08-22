open Alba2_common

module Term = Term2


module Constructor:
sig
  type t
  val make: Feature_name.t option -> Term.arguments -> Term.t array -> t
  val name: t -> Feature_name.t option
  val cargs: t -> Term.arguments
  val ctype: int -> int -> int -> t -> Term.typ
end





type t
val nparams: t -> int
val ntypes: t -> int
val nconstructors: int -> t -> int
val parameter: int -> t -> Term.name_type
val itype0: int -> t -> Term.fname_type
val itype: int -> t -> Term.fname_type
val ctype0: int -> int -> t -> Term.fname_type
val ctype: int -> int -> t -> Term.fname_type
val cargs: int -> int -> t -> Term.arguments
val is_valid_iargs: int -> int -> t -> bool
val make: Term.arguments -> Term.gamma -> Constructor.t array array -> t
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
