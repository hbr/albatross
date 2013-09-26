open Support
open Container
open Type
open Term
open Proof
open Term_table


module Context: sig
  type t
  val  count: t -> int
end = struct
  type t = {
      proved:  proof_pair Term_table.t;
      forward: (term * proof_term) Term_table.t;
                (* conclusion b,
                   proof term of the implication a=>b *)
      backward: (term list * proof_term) Term_table.t
                (* premises [a,b,...],
                   proof term of the implication a=>b=>...=>z *)
    }

  let count (c:t): int = Term_table.count c.proved
end







type descriptor = {
    names: int array;
    types: typ array;
    term:  term;
    nterm: term;
    chain: (term list * term) list;
    fwd_opt: term option;
    elim_opt: term option; (* !!! *)
    pt_opt: proof_term option}

type t  = {seq:           descriptor seq;
           mutable table: proof_term Term_table.t}


let count (at:t): int = Seq.count at.seq

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

let empty (): t =  {seq = Seq.empty (); table = Term_table.empty }


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
  !res

(*
exception Assertion_found of int * term array

let find (t:term) (nb:int) (at:t): int * term array =
  (* Find for the term 't' which comes from an environment with 'nb'
     bound variables in the assertion table 't' the
          idx:   index of the assertion in 't'
          args:  the arguments

     so that t = ass[idx] args
   *)
  try
    Seq.iteri
      (fun i desc ->
        let n = Array.length desc.types in
        List.iter
          (fun (premises,target) ->
            if premises=[] then
              try
                let args,_ = Term.unify t nb target n in
                raise (Assertion_found (i,args));
              with Not_found ->
                ()
            else
              ()
          )
          desc.chain
      )
      at.seq;
    raise Not_found
  with
    Assertion_found (idx,args) ->
      idx,args
*)




let consequences (t:term) (nb:int) (ft:Feature_table.t) (at:t)
    :(proof_pair * int) list * (term * int * term array * int) list =
  (* The direct consequences of the term 't' in an enviroment with 'nb' bound
     variables, i.e. if the assertion table has a proved assertion of the form
     'a=>b' and 'a' can be unified with the term 't' and 'b' is not more
     complex than 'a' then 'b' transformed into the environment of term 't'
     is a direct consequence of 't'.

     a) direct consequences
         If

              ass[idx](args) = (t=>u)

         then the proof pair is

              t=>u, Specialize (Theorem idx, args)

     b) eliminations

          There is a an assertion variable i and arguments args so
          that

          for all c
              args.(nb_ass-1-i ) <- c
              ass[idx](args) = (t => ... => c)

          ass[idx], i, args, idx
   *)
  let res  = ref []
  and res2 = ref []
  in
  begin
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
        end;
        begin
          match desc.elim_opt with
            None -> ()
          | Some elim ->
              try
                let args,arbitrary = Term.unify t nb elim n in
                match arbitrary with
                  [tgt_var] ->
                    res2 :=
                      ((Seq.elem at.seq i).term, i, args, tgt_var)
                      :: !res2
                | _ ->
                    assert false (* Cannot happen *)
              with Not_found ->
                ()
        end
      )
      at.seq
  end;
  !res, !res2







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
  at.table <- Term_table.add nterm nb
      (match pt_opt with None -> Axiom nterm | Some pt -> pt)
      at.table;
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
        (Printf.printf "Simplification rule found\n";
         Some a)
      else if (Term.depth a) = (Term.depth b)
          && distributes a b then
        None
      else
        None
    with Not_found ->
      None
  in

  let elim_opt =
    let premises,target = List.hd (List.rev chn)
    in
    match premises with
      [] -> None
    | p0::tl -> begin
        let bvars_p0, fvars_p0  = Term.split_variables p0 nb
        and bvars_tgt,fvars_tgt = Term.split_variables target nb
        in
        let elim_vars (): IntSet.t =
          List.fold_left
            (fun set p ->
              IntSet.diff set (Term.free_variables p nb))
                (IntSet.diff fvars_p0 fvars_tgt)
            tl
        in
        match target with
          Variable i_tgt when
            not (IntSet.mem i_tgt bvars_p0)
              && (IntSet.cardinal bvars_p0) + 1 = nb
              && not (IntSet.is_empty (elim_vars ()))
          ->
            begin
              (Printf.printf "Elimination rule found\n";
               Some p0)
            end
        | _ ->
            None
    end
  in

  Seq.push
    at.seq
    {names    = names;
     types    = types;
     term     = term;
     nterm    = nterm;
     pt_opt   = pt_opt;
     chain    = chn2;
     fwd_opt  = fwd_opt;
     elim_opt = elim_opt}




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
