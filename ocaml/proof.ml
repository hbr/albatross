open Term

type reduction =
    RVar of int
  | RApply of int (* nargs *)
  | RLam of int * int array  (* nargs, names *)
  | RBeta
  | RExpand
  | REqual of int  (* index of the equality assertion *)



type proof_term =
    Axiom      of term
  | Assumption of term
  | Detached   of int * int  (* modus ponens *)
  | Specialize of int * term array
  | Expand     of int        (* index of term which is expanded *)
  | Expand_bwd of term       (* term which is backward expanded *)
  | Reduce     of int        (* index of term which is reduced  *)
  | Reduce_bwd of term       (* term which is backward reduced  *)
  | Witness    of int * term * term array
        (* term [i] is a witness for [some (a,b,...) t] where
           [a,b,..] in [t] are substituted by the arguments in the term array *)
  | Someelim   of int        (* index of the existenially quantified term *)
  | Inherit    of int * int  (* assertion, descendant class *)
  | Subproof   of int        (* nargs *)
                * int array  (* names *)
                * int        (* res *)
                * proof_term array


module Proof_term: sig
  type t = proof_term
  val adapt: int -> int -> t -> t
end = struct
  type t = proof_term
  let adapt (start:int) (delta:int) (pt:t): t =
    let index (i:int): int =
      if i < start then i else i + delta
    in
    let rec adapt (pt:t): t =
      match pt with
        Axiom _ | Assumption _ -> pt
      | Detached (a,b) ->
          Detached (index a, index b)
      | Specialize (i,args) ->
          Specialize (index i, args)
      | Inherit (i,cls) ->
          Inherit (index i, cls)
      | Expand i     -> Expand (index i)
      | Expand_bwd t -> Expand_bwd t
      | Reduce i     -> Reduce (index i)
      | Reduce_bwd t -> Reduce_bwd t
      | Witness (i,t,args) ->
          Witness (index i,t,args)
      | Someelim i   -> Someelim (index i)
      | Subproof (nargs,names,res,pt_arr) ->
          Subproof (nargs,names, index res, Array.map adapt pt_arr)
    in
    if delta = 0 then pt else adapt pt
end
