open Term
open Proof
open Container

type t = {
    proved:  proof_pair Term_table.t;
    forward: (int * proof_pair * bool * bool) Term_table.t;
    (* index of the implication a=>b
       proof pair of the implication
       is simplification rule
       is closed *)
    backward: (int * proof_pair * bool) Term_table.t
      (* index of the implication a=>b=>...=>z
         proof pair of the implication
         is simplification rule *)
  }



let count (c:t): int = Term_table.count c.proved

let empty: t = {proved=Term_table.empty; forward=Term_table.empty;
                backward=Term_table.empty}



let has (t:term) (nargs:int) (c:t): bool =
  let lst = Term_table.unify t nargs c.proved in
  List.exists (fun (_,_,_,sub) -> Term_sub.is_injective sub) lst





let find (t:term) (nbt:int) (c:t)
    : int * int * proof_pair * Term_sub.t =
  (* Find an assertion which is unifyable with the term 't' with 'nbt'
     bound variables.

     Return:  nargs: number of formal arguments of the assertion
              idx:   index of the assertion
              pp:    proof pair of the assertion
              sub:   substitution if applied to the assertion term
                     yields 't'
   *)
  let lst = Term_table.unify t nbt c.proved in
  match lst with
    []    -> raise Not_found
  | [res] ->
      let nargs,idx,(t0,_),sub = res in
      let args = Term_sub.arguments nargs sub in
      let tt = Term.sub t0 args nbt in
      assert(t=tt);
      res
  | _     -> assert false






let forward (t:term) (nbt:int) (c:t)
    : (int * int * proof_pair * Term_sub.t * bool * bool) list =
  (* Find all assertions of the form 'a=>b' so that 't' can be unified
     with 'a' and 'a=>b' is a valid forward rule

     Return:  nargs:  number of formal arguments of 'a=>b'
              idx:    index of 'a=>b'
              pp:     proof pair of 'a=>b'
              sub:    substitution if applied to 'a' yields 't'
              simpl:  is simplification rule
              closed: 'sub' applied to 'b' does not leave open formal args
   *)
  let lst = Term_table.unify t nbt c.forward in
  List.rev_map
    (fun (nargs,_,(idx,pp,simpl,closed),sub) ->
      nargs,idx,pp,sub,simpl,closed
    )
    lst






let backward (t:term) (nbt:int) (c:t)
    : (int * int * proof_pair * Term_sub.t * bool) list =
  (* Find all assertions of the form 'a=>b=>...=>z' so that 't' can be
     unified with 'z' and 'a=>b=>...=>z' is a valid backward rule

     Return:  nargs:  number of formal arguments of 'a=>b=>...=>z'
              idx:    index of 'a=>b=>...=>z'
              pp:     proof pair of 'a=>b=>...=>z'
              sub:    substitution if applied to 'z' yields 't'
              simpl:  is simplification rule
   *)
  List.rev_map
    (fun (nargs,_,(idx,pp,simpl),sub)->
      nargs,idx,pp,sub,simpl
    )
    (Term_table.unify t nbt c.backward)




let add (t:term) (pt:proof_term) (nargs:int) (impid:int) (c:t): t =
  let idx = Term_table.count c.proved
  and pp  = t,pt
  in
  let add0 (): t =
    let proved =
      Term_table.add t nargs pp c.proved
    and forward =
      try
        let a,b = Term.binary_split t (impid+nargs) in
        let bvars_a,fvars_a  = Term.split_variables a nargs
        and bvars_b,fvars_b  = Term.split_variables b nargs
        and n_a      = Term.nodes a
        and n_b      = Term.nodes b
        in
        let is_closed = IntSet.is_empty (IntSet.diff bvars_b bvars_a)
        and is_elim   = not (IntSet.is_empty (IntSet.diff fvars_a fvars_b))
        and is_simpl  = n_b <= n_a
        in
        if is_simpl || is_elim then
           Term_table.add a nargs (idx,pp,is_simpl,is_closed) c.forward
        else
          c.forward
      with Not_found -> c.forward

    and backward =
      List.fold_left
        (fun table (premises,target) ->
          let bvars_tgt = Term.bound_variables target nargs
          and n_tgt     = Term.nodes target
          in
          let ok,simpl =
            List.fold_left
              (fun (ok,simpl) p ->
                ok &&
                p<>target &&
                IntSet.subset (Term.bound_variables p nargs) bvars_tgt,
                simpl && (Term.nodes p) <= n_tgt)
              (true,true)
              premises
          in
          if ok then
            Term_table.add target nargs (idx,pp,simpl) table
          else
            table
        )
        c.backward
        (Term.implication_chain t (impid+nargs))
    in
    {proved  = proved;
     forward = forward;
     backward = backward}
  in
  let lst = Term_table.unify t nargs c.proved in
  match lst with
    [] ->
      add0 ()
  | _ ->
      c

