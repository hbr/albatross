open Container
open Term
open Type

exception Failed_proof

type proof_term =
    Axiom         of term
  | Assume        of term
  | Discharge     of term  * proof_term  (* discharge assumption as premise *)
  | MP            of proof_term * proof_term       (* a => (a=>b) => b *)
  | Generalize    of proof_term * int
  | Theorem       of int
  | Specialize    of proof_term * term array


type proof_pair = term * proof_term



module Proof: sig
end = struct

  type proof =
      {assumptions:  term array;
       assertion:    term;         (* The proved assertion *)
       proof_term:   proof_term    (* The term which proves the assertion under
                                      the assumptions *)
     }

(* Usage

   Assumption a:                               [a] a
   Discharge (a,Assumption a):                 []  a=>a

   MP (Assumption a) (Assumption a=>b):        [a,a=>b] b
   Discharge(a=>b, MP ... ):                   [a]      (a=>b) => b
   Discharge(a,Discharge(a=>b,MP ...))         []       a => (a=>b) => b

   Discharge (b,Assumption a):                 [a]   b=>a
   Discharge (a,Discharge(b,Assumption a))     []    a => b => a

   0: MP(Assumption a,Assumption b=>c)         [a,b=>c]      c
   1: MP(Assumption a,Assumption a=>b=>c)      [a,a=>b=>c]   b=>c
   2: MP(Assumption b, 1)                      [b,a,a=>b=>c] c
   3: Discharge(a,MP(Assumption b,1))          [b,a=>b=>c]   a=>c
   4: Discharge(b,3)                           [a=>b=>c]     b=>a=>c
   5: Discharge(a=>b=>c,4)                     []            (a=>b=>c)=>b=>a=>c

   0: Assumption a=>false                      [a=>false]  a=>false
   1: Fold (not a) (Assumption a=>false)       [a=>false]  not a
   2: Discharge (a=>false,1) []                []          (a=>false) => not a


*)


end



(* The proof finder maintains a set of proofs together with the proved theorem

   The proved theorem is the theorem itself + a list of assumptions which occur
   within the corresponding proof + a typing context

   A proof with assumptions can be (partially) discharged by replacing
   assumptions by proofs.

   Partial proof: A set of assumptions, a set of assertions with proofs which
   are a consequence of the assumptions and a set of proofs of the goal which
   contain not yet proved assumptions.

   A partial proof is complete if one of its proofs of the goal has no
   unproved assumptions (i.e. no assumptions besides the ones which are the
   introduced assumptions of the partial proof). By discharging the introduced
   assumptions a complete proof of the goal is obtained.

   The proof finder maintains a set of partial proofs. Each step the proof
   finder adds some new partial proofs by its built in rules. The procedure
   ends if one of the partial proofs is completed or no more partial proofs
   can be added to the set.

   The following rules can be used to add new partial proofs:

   - An unproved assumption of a goal is identical with one of the already
     proved assertions on the stack

   - An unproved assumption can be proved by an already proved assertion of
     the global context.

   - An unproved assumption can be replaced by other assumptions using the
     modus ponens rule with the already proved assertions on the stack of the
     form a=>b=>c=>...=>z and z being the unproved assumption.

   - An unproved assumption can be replaced by other assumptions using the
     modus ponens rule with the already proved global assertions of the form
     a=>b=>...=>z and z being the unproved assertion and a,b,... satisfying
     the termination rule.

*)



(* Contexts

We have a toplevel context which contains all classes and functions. I.e. we
have a class and a type context. If we enter a proof we need to shift the
bound variables of the proof into the type context. So we can have a whole
stack of type contexts. The types are found inside out i.e the variable 0 is
the innermost binding and soon.

*)




module Commands = struct
  open Term
  type command =
      Enter
    | MP of term
    | Premise of term list
    | Remove
    | Resolve
    | Induction of int
    | Contradiction of term
end
