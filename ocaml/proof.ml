open Type
open Term
open Container

let _ = ArrayedSet.test ()

type term =
    Variable    of int
  | Application of term * term
  | Lambda      of typ * term


module Proof = struct
  type proof_term =
      Assumption    of term
    | Premise       of term  * proof_term
    | MP            of proof_term * proof_term       (* a => (a=>b) => b *)
    | Generalize    of proof_term * int
    | Theorem       of int
    | Specialize    of proof_term * term list
    | Fold          of proof_term * term  (* Fold a function with new term *)
    | Unfold        of proof_term * term  (* Unfold a function with new term *)


  exception Failed_proof
      
  type proof =
      {type_context: type_context;
       assumptions:  term array;
       term:         term;
       proof_term:   proof_term}

  let check_proof (p:proof) =
    match p.proof_term with
      Assumption t ->
        ((Array.length p.assumptions) = 1) &&
        (p.assumptions.(0) = t)
    | Premise (t,pt) ->
        assert false
    | MP (t,u) ->
        assert false
    | Generalize (t,i) ->
        assert false
    | Theorem i ->
        assert false
    | Specialize (t,l) ->
        assert false
    | Fold (pt,t) ->
        assert false
    | Unfold (pt,t) ->
        assert false
        
end
        
        

(* The proof finder maintains a set of proofs together with the proved theorem 

   The proved theorem is the theorem itself + a list of assumptions which occur
   within the corresponding proof + a typing context

   A proof with assumptions can be (partially) discharged by feeding in
   the proofs of the assumptions.

*)


(* Usage

   Assumption a:                               [a] a
   Premise (a,Assumption a):                   []  a=>a

   MP (Assumption a) (Assumption a=>b):        [a,a=>b] b
   Premise(a=>b, MP ... ):                     [a]      (a=>b) => b
   Premise(a,Premise(a=>b,MP ...))             []       a => (a=>b) => b

   Premise (b,Assumption a):                   [a]   b=>a
   Premise (a,Premise(b,Assumption a))         []    a => b => a

   0: MP(Assumption a,Assumption b=>c)         [a,b=>c]      c
   1: MP(Assumption a,Assumption a=>b=>c)      [a,a=>b=>c]   b=>c
   2: MP(Assumption b, 1)                      [b,a,a=>b=>c] c
   3: Premise(a,MP(Assumption b,1))            [b,a=>b=>c]   a=>c
   4: Premise(b,3)                             [a=>b=>c]     b=>a=>c
   5: Premise(a=>b=>c,4)                       []            (a=>b=>c)=>b=>a=>c



*)




module Commands = struct
  type command =
      Enter
    | MP of term
    | Premise of term list
    | Remove
    | Resolve
    | Induction of int
    | Contradiction of term
end
