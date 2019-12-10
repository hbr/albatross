open Fmlib





type pos = Character_parser.Position.t
type range = pos * pos

type required
type actual


module Problem:
sig
  type t =
    | Overflow of range
    | No_name of range
    | Not_enough_args of range * int * actual list
    | None_conforms of range * required list * actual list
    | Not_yet_implemented of range * string
end


module Print (P:Pretty_printer.SIG):
sig
  val required: required -> P.t
  val actual:   actual -> P.t
end

val build: Parser_lang.Expression.t
           -> Context.t
           -> ((Term.t * Term.typ) list, Problem.t) result
