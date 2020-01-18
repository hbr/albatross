open Fmlib
open Ast

type 'a located = 'a Character_parser.Located.t

type range = Character_parser.Position.t * Character_parser.Position.t





module Problem:
sig
  type t =
    | Operator_precedence of
        range
        * string * string (* the 2 operatos strings *)

    | Illegal_name of range * string (* expectation *)

    | Illegal_command of range * string list

    | Ambiguous_command of range * string list
end




module Command:
sig
  type t =
    | Evaluate of Expression.t
    | Type_check of Expression.t
    | Exit
    | Do_nothing
end



module Error: Generic_parser.ERROR with type expect = string
                                    and type semantic = Problem.t

type parser


val needs_more: parser -> bool
val has_ended:  parser -> bool
val initial:    parser

val put_char: parser -> char -> parser
val put_end:  parser -> parser

val result: parser -> Command.t option
val error:  parser -> Error.t
val line: parser -> int
val column: parser -> int
val position: parser -> Character_parser.Position.t
