open Support
open Container
open Type
open Term
open Proof


type descriptor = {names: int array; types: typ array;
                   term:term; pt_opt: proof_term option}

type t  = {seq: descriptor seq}




let assertion_to_string
    (d:descriptor)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  "all"
  ^ (Class_table.arguments_to_string d.names d.types ct)
  ^ " "
  ^ (Feature_table.term_to_string d.term d.names ft)





(* Public functions *)

let empty (): t =  {seq = Seq.empty () }

let find_backward
    (t:term)
    (nb:int)
    (at:t)
    : proof_pair list =
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
        try
          let n = Array.length desc.types in
          let args = Term.unify t nb desc.term n in
          Printf.printf "idx = %d, t1 = %s, t2 = %s\n"
            i (Term.to_string t) (Term.to_string desc.term);
          Printf.printf "args = [%s]\n"
            (String.concat "," (List.map Term.to_string (Array.to_list args)));
          res := (t,Specialize (Theorem i, args)) :: !res;
          ()
        with
          Not_found -> ()
      )
      at.seq
  end;
  !res



let put_axiom
    (names: int array)
    (types: typ array)
    (term:  term)
    (at:t)
    : unit =
  (* Put an axiom into the table *)
  Seq.push at.seq {names=names; types=types; term=term; pt_opt=None}


let put_proved
    (names: int array)
    (types: typ array)
    (term:  term)
    (pt: proof_term)
    (at:t)
    : unit =
  (* Put a proved assertion into the table *)
  Seq.push at.seq {names=names; types=types; term=term; pt_opt=Some pt}


let print (ct:Class_table.t) (ft:Feature_table.t) (at:t): unit =
  Seq.iter
    (fun desc -> Printf.printf "%s\n" (assertion_to_string desc ct ft))
    at.seq
