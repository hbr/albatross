open Fmlib
open Alba_core


type pos = Character_parser.Position.t
type range = pos * pos


val build:
    Ast.Expression.t
    -> Context.t
    -> (Term.t * Term.typ, Build_problem.t) result



val build_definition:
    Ast.Expression.definition
    -> Context.t
    -> (Term.t * Term.typ, Build_problem.t) result



val add_definition:
    Ast.Expression.definition
    -> Context.t
    -> (Context.t, Build_problem.t) result


val add_entry:
    Ast.Source_entry.t
    -> Context.t
    -> (Context.t, Build_problem.t) result
