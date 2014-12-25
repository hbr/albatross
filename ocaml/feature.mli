open Term

module Spec: sig
  type t
  val make_func:       term option -> term list -> term list -> t
  val has_definition:  t -> bool
  val definition:      t -> term option
  val definition_term: t -> term
  val has_preconditions: t -> bool
  val preconditions:   t -> term list
end

type implementation =
    Builtin
  | Deferred
  | Empty
  (*| Code of ???*)


type body = Spec.t * implementation
