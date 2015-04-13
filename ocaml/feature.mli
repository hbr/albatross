open Term

module Spec: sig
  type t
  val make_func_def:   int array -> term option -> term list -> t
  val make_func_spec:  int array -> term list -> term list -> t
  val equivalent:      t -> t -> bool
  val has_definition:  t -> bool
  val definition:      t -> term option
  val definition_term: t -> term
  val has_preconditions: t -> bool
  val count_arguments: t -> int
  val names:           t -> int * int array
  val preconditions:   t -> term list
end

type implementation =
    Builtin
  | Deferred
  | Empty
  (*| Code of ???*)


type body = Spec.t * implementation
