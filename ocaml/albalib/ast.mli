open Fmlib
open Alba_core

module Located = Character_parser.Located

module Position = Character_parser.Position

type range = Position.t * Position.t


module Expression:
sig
    type operator = string * Operator.t

    type argument_type =
        | Normal
        | Operand


    type t =
        t0 Located.t

    and t0 =
        | Proposition
        | Any
        | Identifier of string
        | Number of string
        | Char of int
        | String of string
        | Operator of operator
        | Typed of t * t                      (* exp, type *)
        | Application of t * (t * argument_type) list
        | Function of
            formal_argument list
            * t option                        (* result type *)
            * t                               (* defining expression *)
        | Product of formal_argument list * t
        | Where of t * definition list
        | List of t list

    and formal_argument =
        string Located.t * t option

    and definition =
        (string Located.t * formal_argument list * t option * t) Located.t


    type operand = operator Located.t list * t


    val to_list: t -> t0

    val binary: t
                -> (operator Located.t * t) list
                -> (t, range * string * string) result

    val find_unused_local: t -> definition list -> string Located.t option
end


module Operator_expression:
sig
    open Expression

    val make:
        operand
        -> (operator Located.t * operand) list
        -> (t, range * string * string) result
end


module Inductive:
sig
    type t
end
