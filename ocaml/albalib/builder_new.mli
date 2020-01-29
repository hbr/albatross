open Fmlib





type pos = Character_parser.Position.t
type range = pos * pos


(* new builder *)
type required_type
type candidate_type

type problem =
  | Overflow of range
  | No_name of range
  | Not_enough_args of range * candidate_type list
  | None_conforms of range * required_type list * candidate_type list
  | No_candidate  of range * (required_type * candidate_type) list
  | Unused_bound of range
  | Cannot_infer_bound of range
  | Not_yet_implemented of range * string


val build: Ast.Expression.t
           -> Context.t
           -> ((Term.t * Term.typ) list, problem) result









module Print (P:Pretty_printer.SIG):
sig
  val required_type: required_type -> P.t
  val candidate_type: candidate_type -> P.t
end
