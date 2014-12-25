open Term
open Container

module Spec = struct
  type t = {def:   term option;
            pres:  term list;
            posts: term list}

  let make_func (def: term option) (pres: term list) (posts: term list): t =
    assert (posts = [] || not (Option.has def));
    {def = def; pres = pres; posts = posts}

  let has_definition (spec:t): bool =
    Option.has spec.def

  let definition (spec:t): term option =
    spec.def

  let definition_term (spec:t): term =
    match spec.def with
      None   -> raise Not_found
    | Some t -> t

  let has_preconditions (spec:t): bool =
    spec.pres <> []

  let preconditions (spec:t): term list =
    spec.pres
end


type implementation =
    Builtin
  | Deferred
  | Empty
  (*| Code of ???*)

type body = Spec.t * implementation
