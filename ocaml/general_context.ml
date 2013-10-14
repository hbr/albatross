open Term
open Proof
open Container


type 'a t = {
    proved:  (proof_pair * 'a) Term_table.t;
    forward: (int * proof_pair * 'a * bool * int) Term_table.t;
    (* index of the implication a=>b
       proof pair of the implication
       is simplification rule
       number of open variables *)
    backward: (int * proof_pair * 'a * bool) Term_table.t
      (* index of the implication a=>b=>...=>z
         proof pair of the implication
         is simplification rule *)
  }



let count (c:'a t): int = Term_table.count c.proved

let empty: 'a t = {proved=Term_table.empty; forward=Term_table.empty;
                   backward=Term_table.empty}



let has (t:term) (nargs:int) (c:'a t): bool =
  let lst = Term_table.unify t nargs c.proved in
  List.exists (fun (_,_,_,sub) -> Term_sub.is_injective sub) lst





let find (t:term) (nbt:int) (c:'a t)
    : int * int * proof_pair * 'a * Term_sub.t =
  (* Find an assertion which is unifyable with the term 't' with 'nbt'
     bound variables.

     Return:  nargs: number of formal arguments of the assertion
              idx:   index of the assertion
              pp:    proof pair of the assertion
              dat:   data of the assertion
              sub:   substitution if applied to the assertion term
                     yields 't'
   *)
  let lst = Term_table.unify t nbt c.proved in
  match lst with
    []    -> raise Not_found
  | [res] ->
      let nargs,idx,((t0,pt),dat),sub = res in
      let args = Term_sub.arguments nargs sub in
      let tt = Term.sub t0 args nbt in
      assert(t=tt);
      nargs,idx,(t0,pt),dat,sub
  | _     -> assert false






let forward (t:term) (nbt:int) (c:'a t)
    : (int * int * proof_pair * 'a * Term_sub.t * bool * int) list =
  (* Find all assertions of the form 'a=>b' so that 't' can be unified
     with 'a' and 'a=>b' is a valid forward rule

     Return:  nargs:  number of formal arguments of 'a=>b'
              idx:    index of 'a=>b'
              pp:     proof pair of 'a=>b'
              dat:    data associated with 'a=>b'
              sub:    substitution if applied to 'a' yields 't'
              simpl:  is simplification rule
              nopen: 'sub' applied to 'b' does  leave nopen formal args open
   *)
  let lst = Term_table.unify t nbt c.forward in
  List.rev_map
    (fun (nargs,_,(idx,pp,dat,simpl,nopen),sub) ->
      nargs,idx,pp,dat,sub,simpl,nopen
    )
    lst






let backward (t:term) (nbt:int) (c:'a t)
    : (int * int * proof_pair * 'a * Term_sub.t * bool) list =
  (* Find all assertions of the form 'a=>b=>...=>z' so that 't' can be
     unified with 'z' and 'a=>b=>...=>z' is a valid backward rule

     Return:  nargs:  number of formal arguments of 'a=>b=>...=>z'
              idx:    index of 'a=>b=>...=>z'
              pp:     proof pair of 'a=>b=>...=>z'
              dat:    data associated with 'a=>b=>...=>z'
              sub:    substitution if applied to 'z' yields 't'
              simpl:  is simplification rule
   *)
  List.rev_map
    (fun (nargs,_,(idx,pp,dat,simpl),sub)->
      nargs,idx,pp,dat,sub,simpl
    )
    (Term_table.unify t nbt c.backward)




let add (t:term) (pt:proof_term)  (dat:'a) (nargs:int) (impid:int)(c:'a t)
    : 'a t =
  let idx = Term_table.count c.proved
  and pp  = t,pt
  in
  let add0 (): 'a t =
    let proved =
      Term_table.add t nargs (pp,dat) c.proved
    and forward =
      try
        let a,b = Term.binary_split t (impid+nargs) in
        let bvars_a,fvars_a  = Term.split_variables a nargs
        and bvars_b,fvars_b  = Term.split_variables b nargs
        and n_a      = Term.nodes a
        and n_b      = Term.nodes b
        in
        let nopen     = IntSet.cardinal (IntSet.diff bvars_b bvars_a)
        and is_simpl  = n_b <= n_a
        in
        if is_simpl ||  1 < n_a then
           Term_table.add a nargs (idx,pp,dat,is_simpl,nopen) c.forward
        else
          c.forward
      with Not_found -> c.forward

    and backward =
      let rec bwd (chain: (term list * term) list) =
        match chain with
          [] -> assert false
        | (premises,target)::tail ->
          let bvars_tgt = Term.bound_variables target nargs
          and n_tgt     = Term.nodes target
          in
          let ok,simpl =
            List.fold_left
              (fun (ok,simpl) p ->
                ok &&
                1 < n_tgt &&
                p<>target &&
                IntSet.subset (Term.bound_variables p nargs) bvars_tgt,
                simpl && (Term.nodes p) <= n_tgt)
              (true,true)
              premises
          in
          if ok then
            Term_table.add target nargs (idx,pp,dat,simpl) c.backward
          else
            bwd tail
      in
      bwd  (Term.implication_chain t (impid+nargs))
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

