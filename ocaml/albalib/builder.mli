open Fmlib
open Alba_core


type pos = Character_parser.Position.t
type range = pos * pos


type type_in_context = Build_context.type_in_context

type problem_description =
    | Overflow
    | No_name
    | Incomplete_type of type_in_context
    | Cannot_infer_bound
    | Not_a_function of type_in_context list
    | Wrong_type of (type_in_context * type_in_context) list
    | Wrong_base of type_in_context list * type_in_context list
    | Ambiguous of type_in_context list
    | Name_violation of string * string (* case, kind *)
    | Ambiguous_definition of int
    | Not_yet_implemented of string


type problem = range * problem_description

val build:
    Ast.Expression.t
    -> Context.t
    -> (Term.t * Term.typ, problem) result



val build_definition:
    Ast.Expression.definition
    -> Context.t
    -> (Term.t * Term.typ, problem) result



val add_definition:
    Ast.Expression.definition
    -> Context.t
    -> (Context.t, problem) result


val add_entry:
    Ast.Source_entry.t
    -> Context.t
    -> (Context.t, problem) result




module Print (P: Pretty_printer.SIG):
sig
    val description: problem_description -> P.t

    val print_with_source: string -> problem -> P.t

    val print_with_source_lines:
        string Segmented_array.t -> problem -> P.t
end
