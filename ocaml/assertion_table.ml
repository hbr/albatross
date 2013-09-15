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
