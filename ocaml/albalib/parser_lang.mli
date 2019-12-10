open Fmlib

type 'a located = 'a Character_parser.Located.t

module Expression:
sig
  type operator = string * Operator.t


  type t =
    t0 Character_parser.Located.t

  and t0 =
    | Proposition
    | Any
    | Identifier of string
    | Number of string
    | Char of int
    | String of string
    | Operator of operator
    | Binary of t * operator located * t
    | Typed of t * t
    | Function of string located list * t
    | Parenthesized of t
end




module Problem:
sig
  type t =
    | Expect of string
    | Operator_precedence of string * string
end



module Context_msg:
sig
  type t =
    | Operand
end


module Dead_end: Character_parser.DEAD_END with type msg = Problem.t


type parser


val needs_more: parser -> bool
val has_ended:  parser -> bool
val initial:    parser

val put_char: parser -> char -> parser
val put_end:  parser -> parser

val result: parser -> (Expression.t option,Dead_end.t list) result
val line: parser -> int
val column: parser -> int
val position: parser -> Character_parser.Position.t
