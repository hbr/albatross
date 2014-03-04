open Support
open Container
open Term
open Proof
open Term_table


type t  = {mutable table: unit General_context.t}


let count (at:t): int = General_context.count at.table


(* Public functions *)

let empty (): t =  {table = General_context.empty}


let find_backward
    (t:term)
    (nb:int)
    (at:t)
    : (proof_pair * int) list =
  (* Find a list of proof pairs such that the term has the form

         'a=>b=>...=>t'         (the set of premises might be empty)

     The proof term has the form

         Specialize (Theorem idx, args)

     which proves ass[idx](args) = (a=>b=>...=>t)
   *)
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
      (General_context.backward t nb at.table)
  in
  lst




let consequences (t:term) (nb:int) (at:t)
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
      (General_context.forward t nb at.table)
  in
  lst







let put_assertion
    (term:  term)
    (nb: int)
    (pt_opt: proof_term option)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  let nterm = Feature_table.normalize_term term nb ft in
  at.table <-
    General_context.add
      nterm
      (match pt_opt with None -> Axiom nterm | Some pt -> pt)
      ()
      nb
      Feature_table.implication_index
      at.table
