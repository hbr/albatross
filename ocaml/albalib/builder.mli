open Fmlib
open Alba_core


type pos = Character_parser.Position.t
type range = pos * pos


type problem_description

type problem = range * problem_description

val build:
    Ast.Expression.t
    -> Context.t
    -> (Term.t * Term.typ, problem) result


module Print (P: Pretty_printer.SIG):
sig
    val description: problem_description -> P.t

    val print_with_source: string -> problem -> P.t

    val print_with_source_lines:
        string Segmented_array.t -> problem -> P.t
end
