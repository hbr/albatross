open Support
open Container
open Type
open Term
open Proof


type descriptor = {
    names: int array;
    types: typ array;
    term:term;
    chain: (term list * bool * term) list;
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
    : (proof_pair * int * bool ) list =
  (* Find a list of proof pairs such that the term has the form

         'a=>b=>...=>t'         (the set of premises might be empty)

     The proof term has the form

         Specialize (Theorem idx, args)

     which proves ass[idx](args) = (a=>b=>...=>t)
   *)
  let res = ref [] in
  begin
    Seq.iteri
      (fun i desc ->
        let n = Array.length desc.types in
        List.iter
          (fun (premises,simpl,target) ->
            try
              let args,flags = Term.unify t nb target n in
              let tt = Term.sub desc.term args nb in
              res := ((tt,Specialize (Theorem i, args)),i,simpl) :: !res
            with Not_found ->
              ()
          )
          desc.chain
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
  let chn = Feature_table.implication_chain term nb ft in
  let chn2 =
    List.filter
      (fun (premises,target) ->
        let bvars_tgt = Term.bound_variables target nb in
        List.for_all
          (fun p ->
            (p<>target) &&
            let bvars = Term.bound_variables p nb in
            IntSet.subset bvars bvars_tgt
          )
          premises
      )
      chn
  in
  let chn3 =
    List.map
      (fun (premises,target) ->
        let n_tgt = Term.nodes target in
        premises,
        List.for_all
          (fun p -> (Term.nodes p)<=n_tgt)
          premises,
        target
      )
      chn2
  in
  Seq.push
    at.seq
    {names = names;
     types = types;
     term  = term;
     pt_opt = pt_opt;
     chain  = chn3}




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
