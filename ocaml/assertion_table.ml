open Support
open Container
open Type
open Term
open Proof
open Term_table


type header = int array * typ array

type descriptor = {
    names: int array;
    types: typ array;
    term:  term;
    nterm: term;
    chain: (term list * term) list;
    fwd_opt: term option;
    pt_opt: proof_term option}

type t  = {seq:           descriptor seq;
           mutable context: header General_context.t}


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
                    context = General_context.empty}


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
      (fun lst (nargs,idx,(t,pt),_,sub,simpl) ->
        if simpl then
          let args = Term_sub.arguments nargs sub in
          let tt = Term.sub t args nb in
          ((tt,Specialize(Theorem idx,sub)),idx)::lst
        else
          lst
      )
      []
      (General_context.backward t nb at.context)
  in
  (*let res = ref []
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
  end;*)
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
      (fun lst (nargs,idx,(t,pt),_,sub,simpl,nopen) ->
        if simpl && (nopen=0) then
          let args = Term_sub.arguments nargs sub in
          let tt = Term.sub t args nb in
          ((tt,Specialize(Theorem idx,sub)),idx)::lst
        else
          lst
      )
      []
      (General_context.forward t nb at.context)
  in
  (*let res  = ref []
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
    at.seq;*)
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
    General_context.add
      nterm
      (match pt_opt with None -> Axiom nterm | Some pt -> pt)
      (names,types)
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
  if (Seq.count at.seq) < (General_context.count at.context) then
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
