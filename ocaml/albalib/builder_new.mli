open Fmlib





type pos = Character_parser.Position.t
type range = pos * pos


(* new builder *)
type required_type
type candidate_type

type problem_description =
  | Overflow
  | No_name
  | Not_enough_args of candidate_type list
  | None_conforms of required_type list * candidate_type list
  | No_candidate  of (required_type * candidate_type) list
  | Incomplete_type of candidate_type list
  | Unused_bound
  | Cannot_infer_bound
  | Not_yet_implemented of string


type problem = range * problem_description


val build: Ast.Expression.t
           -> Context.t
           -> ((Term.t * Term.typ) list, problem) result









module Print (P:Pretty_printer.SIG):
sig
  val required_type: required_type -> P.t
  val candidate_type: candidate_type -> P.t
end
