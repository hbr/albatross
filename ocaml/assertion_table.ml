open Support
open Container
open Type
open Term
open Proof


type descriptor = {
    names: int array;
    types: typ array;
    term:  term;
    nterm: term;
    chain: (term list * term) list;
    fwd_opt: term option;
    pt_opt: proof_term option}

type t  = {seq: descriptor seq}


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

let empty (): t =  {seq = Seq.empty () }

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
                let args,flags = Term.unify t nb target n in
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






let consequences (t:term) (nb:int) (ft:Feature_table.t) (at:t)
    :(proof_pair* int) list =
  (* The direct consequences of the term 't' in an enviroment with 'nb' bound
     variables, i.e. if the assertion table has a proved assertion of the form
     'a=>b' and 'a' can be unified with the term 't' and 'b' is not more
     complex than 'a' then 'b' transformed into the environemt of term 't'
     is a direct consequence of 't'.

     If

          ass[idx](args) = (t=>u)

     then the proof pair is

          t=>u, Specialize (Theorem idx, args)
   *)
  let res = ref []
  in
  begin
    Seq.iteri
      (fun i desc ->
        let n = Array.length desc.types in
        match desc.fwd_opt with
          None -> ()
        | Some fwd ->
            try
              let args,flags = Term.unify t nb fwd n in
              let tt = Term.sub desc.nterm args nb in
              res := ((tt,Specialize (Theorem i, args)),i) :: !res
            with Not_found ->
              ()
      )
      at.seq
  end;
  !res







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
      in
      if n_b <= n_a && a<>b && IntSet.subset bvars_b bvars_a then
        Some a
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
    | p0::_ ->
        let bvars_p0  = Term.bound_variables p0 nb
        and bvars_tgt = Term.bound_variables target nb
        in
        let bvars_union = IntSet.union bvars_p0 bvars_tgt in
        (* Still need to check that there is a function eliminated *)
        if (IntSet.cardinal bvars_union) = nb then
          ((*Printf.printf "Elimination rule found\n";*)
           None)
        else
          None
  in
  Seq.push
    at.seq
    {names  = names;
     types  = types;
     term   = term;
     nterm  = nterm;
     pt_opt = pt_opt;
     chain  = chn2;
     fwd_opt= fwd_opt}




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
