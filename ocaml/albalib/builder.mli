open Fmlib





type pos = Character_parser.Position.t
type range = pos * pos

type required
type actual


module Problem:
sig
  type t =
    | Overflow of pos * string
    | No_name of pos * string
    | Not_enough_args of pos * int * int * actual list
    | None_conforms of pos * int * required list * actual list
    | Not_yet_implemented of pos * int * string
end


module Print (P:Pretty_printer.SIG):
sig
  val required: required -> P.t
  val actual:   actual -> P.t
end

val build: Parser_lang.Expression.t
           -> Context.t
           -> ((Term.t * Term.typ) list, Problem.t) result
