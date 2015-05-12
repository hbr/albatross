open Term
open Container

module Spec = struct
  type t = {nms:   int array;
            def:   term option;
            pres:  term list;
            posts: term list}

  let make_func_def (nms:int array) (def: term option) (pres:term list): t =
    {nms = nms; def = def; pres = pres; posts = []}


  let make_func_spec (nms:int array) (pres: term list) (posts: term list): t =
    {nms = nms; def = None; pres = pres; posts = posts}

  let names (spec:t): int * int array =
    Array.length spec.nms, spec.nms


  let count_arguments (spec:t): int =
    Array.length spec.nms

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


  let has_postconditions (spec:t): bool =
    spec.posts <> []

  let postconditions (spec:t): term list =
    if spec.posts = [] then
      raise Not_found
    else
      spec.posts


  let equivalent (s1:t) (s2:t): bool =
    if s1.def <> s2.def && Option.has s1.def && Option.has s2.def then
      Printf.printf "definitions not equivalent %s %s\n"
        (Term.to_string (Option.value s1.def))
        (Term.to_string (Option.value s2.def));
    s1.def = s2.def && s1.pres = s2.pres && s1.posts = s2.posts

end


type implementation =
    Builtin
  | Deferred
  | Empty
  (*| Code of ???*)

type body = Spec.t * implementation
