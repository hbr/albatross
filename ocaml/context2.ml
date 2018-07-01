open Alba2_common

module Term = Term2
module IArr = Immutable_array

type definition = Feature_name.t option * Term.typ * Term.t

type gamma_arr = (Feature_name.t option * Term.typ) array

type inductive = {
    nparams: int;
    itypes:  gamma_arr;
    constructors: gamma_arr
  }

type justification =
  | Assumption of Feature_name.t option
  | Definition of definition
  | Indtype of int * inductive
  | Constructor of int * inductive
  | Recursive of Term.fixpoint

type entry = {
    typ:  Term.t;
    just: justification
  }

type t = {
    global: entry IArr.t;
    local:  entry IArr.t;
  }

let global_count (c:t): int =
  IArr.length c.global

let local_count (c:t): int =
  IArr.length c.local

let count (c:t): int =
  global_count c + local_count c

let entry (i:int) (c:t): entry =
  assert (i < count c);
  let n = global_count c in
  if i < n then
    IArr.elem i c.global
  else
    IArr.elem (i-n) c.local

let entry_type (i:int) (c:t): Term.t =
  Term.up (count c - i) (entry i c).typ
