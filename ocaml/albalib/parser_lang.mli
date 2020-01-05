open Fmlib

type 'a located = 'a Character_parser.Located.t

type range = Character_parser.Position.t * Character_parser.Position.t


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
    | Application of t * t list
    | Function of string located list * t
    | Parenthesized of t
end




module Problem:
sig
  type t =
    | Operator_precedence of
        range
        * string * string (* the 2 operatos strings *)

      | Unexpected_keyword of range * string (* expectation *)
end



module Context_msg:
sig
  type t =
    | Operand
end


module Error: Generic_parser.ERROR with type expect = string
                                    and type semantic = Problem.t

type parser


val needs_more: parser -> bool
val has_ended:  parser -> bool
val initial:    parser

val put_char: parser -> char -> parser
val put_end:  parser -> parser

val result: parser -> Expression.t option option
val error:  parser -> Error.t
val line: parser -> int
val column: parser -> int
val position: parser -> Character_parser.Position.t
