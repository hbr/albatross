open Term
open Proof

type t

val  count: t -> int
    (* Number of proved assertions in the context *)


val  has:   term -> int -> t -> bool
    (* Is the term with nargs arguments in the context? *)


val  empty: t
    (* The empty context *)


val  add:   term -> proof_term -> int -> int -> t -> t
    (* Add a term with a proof term with nargs arguments and implication id
       to the context *)


val  forward: term -> int -> t
  -> (int * int * proof_pair * Term_sub.t * bool * int) list
  (* The list of forward rules for a term with nargs arguments in the
     context:

     Result: nargs: number of formal arguments of 'a=>b'
             idx:   index of 'a=>b'
             pp:    proof pair of 'a=>b'
             sub:   substitution if applied to 'a' yields the term
             simpl: is simplification rule
             nopen: 'sub' applied to 'b' does leave 'nopen' args open
   *)


val  backward: term  -> int -> t
  -> (int * int * proof_pair * Term_sub.t * bool) list
  (* The list of backward rules for a term with nargs arguments in the
     context:

     Return:  nargs:  number of formal arguments of 'a=>b=>...=>z'
              idx:    index of 'a=>b=>...=>z'
              pp:     proof pair of 'a=>b=>...=>z'
              sub:    substitution if applied to 'z' yields 't'
              simpl:  is simplification rule
   *)

