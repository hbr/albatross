open Container
open Type
open Term
open Proof
open Support 

type descriptor = {names: int array; types: typ array; term:term}

type t  = {seq: descriptor seq}

let empty () = {seq = Seq.empty () }

let put
    (entlst: entities list withinfo)
    (bdy:feature_body)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at:t): unit =
  let argnames,argtypes = Class_table.arguments entlst ct in
  match bdy with
    _, _, None ->
      error_info entlst.i "Assertion must have an ensure clause"
  | rlst_opt, imp_opt, Some elst ->
      let rlst = match rlst_opt with None -> [] | Some l -> l
      and axiom,clst =
        match imp_opt with
          None -> false,[]
        | Some Impdeferred ->
            not_yet_implemented entlst.i "Deferred assertions"
        | Some Impbuiltin -> (
            true,[]
           )
        | Some Impevent ->
            error_info entlst.i "Assertion cannot be an event"
        | Some (Impdefined (Some locs,is_do,cmp)) ->
            not_yet_implemented entlst.i "Local variables in assertions"
        | Some (Impdefined (None,is_do,cmp)) ->
            if is_do then
              error_info entlst.i "Assertion cannot have do block"
            else
              false,cmp
      in
      if axiom then
        match rlst with
          [] -> 
            List.iter
              (fun ie ->
                let term = Feature_table.term ie argnames argtypes ct ft in
                let _ = Term.normalize argtypes term in
                Seq.push at.seq {names=argnames; types=argtypes; term=term})
              elst
        | _ ->
            not_yet_implemented entlst.i "axioms with preconditions"
      else
        not_yet_implemented entlst.i "proved assertions"



let assertion_to_string 
    (d:descriptor)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  let nargs = Array.length d.names in
  assert (nargs = (Array.length d.types));
  let args = Array.init 
      nargs 
      (fun i ->
        (ST.string d.names.(i))
        ^ ":"
        ^ (Class_table.type2string d.types.(i) 0 ct))
  in
  "all" 
  ^ (
    if nargs=0 then " "
    else "(" ^ (String.concat "," (Array.to_list args)) ^ ") " 
   )
  ^ (Feature_table.term_to_string d.term d.names ft)

let print (ct:Class_table.t) (ft:Feature_table.t) (at:t): unit =
  Seq.iter 
    (fun desc -> Printf.printf "%s\n" (assertion_to_string desc ct ft))
    at.seq
