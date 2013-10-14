open Term
open Proof

type 'a t

val  count: 'a t -> int
    (* Number of proved assertions in the context *)


val  has:   term -> int -> 'a t -> bool
    (* Is the term with nargs arguments in the context? *)


val  empty: 'a t
    (* The empty context *)


val  add:   term -> proof_term -> 'a -> int -> int -> 'a t -> 'a t
    (* Add a term with a proof term with nargs arguments and implication id
       to the context *)


val  forward: term -> int -> 'a t
  -> (int * int * proof_pair * 'a * Term_sub.t * bool * int) list
  (* The list of forward rules for a term with nargs arguments in the
     context:

     Result: nargs: number of formal arguments of 'a=>b'
             idx:   index of 'a=>b'
             pp:    proof pair of 'a=>b'
             sub:   substitution if applied to 'a' yields the term
             simpl: is simplification rule
             nopen: 'sub' applied to 'b' does leave 'nopen' args open
   *)


val  backward: term  -> int -> 'a t
  -> (int * int * proof_pair * 'a * Term_sub.t * bool) list
  (* The list of backward rules for a term with nargs arguments in the
     context:

     Return:  nargs:  number of formal arguments of 'a=>b=>...=>z'
              idx:    index of 'a=>b=>...=>z'
              pp:     proof pair of 'a=>b=>...=>z'
              sub:    substitution if applied to 'z' yields 't'
              simpl:  is simplification rule
   *)

