open Support
open Container
open Type
open Term
open Proof
open Term_table


module Assertion_context: sig

  type t
  val  count: t -> int
  val  has:   term -> int -> t -> bool
  val  empty: t
  val  proof_pair: int -> t -> int * proof_pair
  val  add:   term -> proof_term -> int -> int -> t -> t
  val find:   term -> int -> t
    -> int * int * proof_pair * Term_sub.t
  val  forward: term -> int -> t
    -> (int * int * proof_pair * Term_sub.t * bool * bool) list
  val  backward: term  -> int -> t
    -> (int * int * proof_pair * Term_sub.t * bool) list

end = struct

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


  let proof_pair (idx:int) (c:t): int * proof_pair =
    assert (idx < count c);
    Term_table.data idx c.proved

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


  let implication_chain (t:term) (impid:int)
      : (term list * term) list =
    let rec chainr (t:term) (lst: (term list * term) list)
        : (term list * term) list =
      try
        let a,b = Term.binary_split t impid in
        let lst =
          List.map
            (fun (ps,tgt) -> a::ps,tgt)
            (chainr b lst)
        in
        ([a],b)::lst
      with Not_found ->
        lst
    in
    chainr t []


  let add (t:term) (pt:proof_term) (nargs:int) (impid:int) (c:t): t =
    let idx = Term_table.count c.proved
    and pp  = t,pt
    in
    (*Printf.printf "idx=%d to ass ctxt %s\n" idx (Term.to_string t);*)
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
            ((*Printf.printf "forward rule found simpl=%B closed=%B\n"
               is_simpl is_closed;*)
             Term_table.add a nargs (idx,pp,is_simpl,is_closed) c.forward)
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
              ((*Printf.printf "backward rule found simpl %B premises=%d\n"
                 simpl (List.length premises);*)
              Term_table.add target nargs (idx,pp,simpl) table)
            else
              table
          )
          c.backward
          (implication_chain t (impid+nargs))

        (*let lst = Term.binary_right t (impid+nargs) in
        match lst with
          [] | [_] -> c.backward
        | target::premises ->
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
              (Printf.printf "backward rule found simpl %B premises=%d\n"
                 simpl (List.length premises);
              Term_table.add target nargs (idx,pp,simpl) c.backward)
            else
              c.backward*)
      in
      let res =
        {proved  = proved;
         forward = forward;
         backward = backward}
      in
      (*Printf.printf "Proved item added, table ... \n";
      Term_table.write res.proved;*)
      res
    in

    let lst = Term_table.unify t nargs c.proved in
    match lst with
      [] ->
        add0 ()
    (*| (_,_,_,sub)::tl when not (Term_sub.is_injective sub) ->
        assert (tl=[]);
        add0 () *)
    | _ ->
        Printf.printf "duplicate\n";
        c

end







type descriptor = {
    names: int array;
    types: typ array;
    term:  term;
    nterm: term;
    chain: (term list * term) list;
    fwd_opt: term option;
    pt_opt: proof_term option}

type t  = {seq:           descriptor seq;
           mutable context: Assertion_context.t}


let count (at:t): int = Seq.count at.seq

let term (idx:int) (at:t): int * term =
  assert (idx < count at);
  let desc = Seq.elem at.seq idx in
  let nargs = Array.length desc.types in
  nargs,desc.nterm

let assertion_to_string
    (d:descriptor)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  "all"
  ^ (Class_table.arguments_to_string d.names d.types ct)
  ^ " "
  ^ (Feature_table.term_to_string d.term d.names ft)


let to_string
    (i:int)
    (ct:Class_table.t)
    (ft:Feature_table.t)
    (at:t): string =
  assert (i < Seq.count at.seq);
  assertion_to_string (Seq.elem at.seq i) ct ft



(* Public functions *)

let empty (): t =  {seq = Seq.empty ();
                    context = Assertion_context.empty}


let find_backward
    (t:term)
    (nb:int)
    (ft:Feature_table.t)
    (at:t)
    : (proof_pair * int) list =
  (* Find a list of proof pairs such that the term has the form

         'a=>b=>...=>t'         (the set of premises might be empty)

     The proof term has the form

         Specialize (Theorem idx, args)

     which proves ass[idx](args) = (a=>b=>...=>t)
   *)
  let write_list str lst =
    Printf.printf "backward list %s\n" str;
    Mylist.iteri
      (fun i ((t,pt),idx) ->
        Printf.printf " %d idx=%d %s\n"
          i idx
          (Feature_table.raw_term_to_string t nb ft)
      )
      lst
  in
  let lst =
    List.fold_left
      (fun lst (nargs,idx,(t,pt),sub,simpl) ->
        if simpl then
          let args = Term_sub.arguments nargs sub in
          let tt = Term.sub t args nb in
          ((tt,Specialize(Theorem idx,args)),idx)::lst
        else
          lst
      )
      []
      (Assertion_context.backward t nb at.context)
  in
  let lst =
    try
      let nargs,idx,(t,pt),sub = Assertion_context.find t nb at.context in
      let args = Term_sub.arguments nargs sub in
      let tt = Term.sub t args nb in
      ((tt,Specialize(Theorem idx,args)),idx)::lst
    with Not_found -> (*Printf.printf "  no direct match\n";*)
      lst
  in
  (*Printf.printf "%d backward rules found\n" (List.length lst);*)
  let res = ref []
  in
  begin
    Seq.iteri
      (fun i desc ->
        let n = Array.length desc.types in
        List.iter
          (fun (premises,target) ->
            (*if premises=[] then*)
              try
                let args,_ = Term.unify t nb target n in
                let tt = Term.sub desc.nterm args nb in
                res := ((tt,Specialize (Theorem i, args)),i) :: !res
              with Not_found ->
                ()
            (*else
              ()*)
          )
          desc.chain
      )
      at.seq
  end;
  (*Printf.printf "Term to match %s\n"
    (Feature_table.raw_term_to_string t nb ft);
  if (List.length !res) <> (List.length lst) then
    Printf.printf "!! Table and Context different !!\n";
  write_list "Table" !res;
  write_list "Context" lst;*)
  (*!res*)
  lst




let consequences (t:term) (nb:int) (ft:Feature_table.t) (at:t)
    :(proof_pair * int) list =
  (* The direct consequences of the term 't' in an enviroment with 'nb' bound
     variables, i.e. if the assertion table has a proved assertion of the form
     'a=>b' and 'a' can be unified with the term 't' and 'b' is not more
     complex than 'a' then 'b' transformed into the environment of term 't'
     is a direct consequence of 't'.

     direct consequences
         If

              ass[idx](args) = (t=>u)

         then the proof pair is

              t=>u, Specialize (Theorem idx, args)
   *)
  let write_list str lst =
    Printf.printf "%s\n" str;
    Mylist.iteri
      (fun i ((t,_),idx) ->
        Printf.printf "%d: idx=%d, %s\n" i idx
          (Feature_table.raw_term_to_string t nb ft)
      )
      lst
  in
  let lst =
    List.fold_left
      (fun lst (nargs,idx,(t,pt),sub,simpl,closed) ->
        if simpl && closed then
          let args = Term_sub.arguments nargs sub in
          let tt = Term.sub t args nb in
          ((tt,Specialize(Theorem idx,args)),idx)::lst
        else
          lst
      )
      []
      (Assertion_context.forward t nb at.context)
  in
  let res  = ref []
  in
  Seq.iteri
    (fun i desc ->
      let n = Array.length desc.types in
      begin
        match desc.fwd_opt with
          None -> ()
        | Some fwd ->
            try
              let args,_ = Term.unify t nb fwd n in
              let tt = Term.sub desc.nterm args nb in
              res := ((tt,Specialize (Theorem i, args)),i) :: !res
            with Not_found ->
              ()
      end
    )
    at.seq;
  (*Printf.printf "Term to match %s\n"
    (Feature_table.raw_term_to_string t nb ft);
  if (List.length !res) <> (List.length lst) then
    Printf.printf "!! Table and Context different !!\n";
  write_list "Table" !res;
  write_list "Context" lst;*)
  (*!res*)
  lst







let put_assertion
    (names: int array)
    (types: typ array)
    (term:  term)
    (pt_opt: proof_term option)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  let nb  = Array.length types in
  let nterm = Feature_table.normalize_term term nb ft in
  at.context <-
    Assertion_context.add nterm
      (match pt_opt with None -> Axiom nterm | Some pt -> pt)
      nb
      (Feature_table.implication_index ft)
      at.context;
  let chn = Feature_table.implication_chain nterm nb ft in
  assert (chn<>[]);
  let chn2 =
    List.filter
      (fun (premises,target) ->
        let bvars_tgt = Term.bound_variables target nb
        and n_tgt     = Term.nodes target
        in
        List.for_all
          (fun p ->
           (p<>target) &&
            let bvars = Term.bound_variables p nb
            and n     = Term.nodes p
            in
            n <= n_tgt &&  (* Has to be refined to allow distributivity *)
            IntSet.subset bvars bvars_tgt
          )
          premises
      )
      chn
  in
  let fwd_opt =
    try
      let a,b = Feature_table.split_implication nterm nb ft in
      let bvars_a = Term.bound_variables a nb
      and bvars_b = Term.bound_variables b nb
      and n_a     = Term.nodes a
      and n_b     = Term.nodes b
      and distributes a b = false (* Algorithm needed for distributivity *)
      in
      if n_b <= n_a && a<>b && IntSet.subset bvars_b bvars_a then
        ((*Printf.printf "Simplification rule found\n";*)
         Some a)
      else if (Term.depth a) = (Term.depth b)
          && distributes a b then
        None
      else
        None
    with Not_found ->
      None
  in
  if (Seq.count at.seq) < (Assertion_context.count at.context) then
    Seq.push
      at.seq
      {names    = names;
       types    = types;
       term     = term;
       nterm    = nterm;
       pt_opt   = pt_opt;
       chain    = chn2;
       fwd_opt  = fwd_opt}
  else
    Printf.printf "Duplicate, do not enter in at.seq\n"




let put_axiom
    (names: int array)
    (types: typ array)
    (term:  term)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  (* Put an axiom into the table *)
  put_assertion names types term None ft at


let put_proved
    (names: int array)
    (types: typ array)
    (term:  term)
    (pt:    proof_term)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  (* Put a proved assertion into the table *)
  put_assertion names types term (Some pt) ft at


let print (ct:Class_table.t) (ft:Feature_table.t) (at:t): unit =
  Seq.iter
    (fun desc -> Printf.printf "%s\n" (assertion_to_string desc ct ft))
    at.seq
