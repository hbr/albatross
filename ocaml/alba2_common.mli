module Info:
sig
  type t =
    | Position of int * int
    | Unknown
end


module Operator:
sig
  type associativity =
    Left | Right | Nonassoc
  type t =
    | Plusop
    | Minusop
    | Timesop
    | Divideop
    | Modop
    | Caretop
    | Commaop
    | Colonop
    | Eqop
    | NEqop
    | Eqvop
    | NEqvop
    | LTop
    | LEop
    | GTop
    | GEop
    | Andop
    | Orop
    | Notop
    | Arrowop

  val normal_precedence: int
  val quantifier_precedence: int
  val highest_precedence: int

  val data: t -> string * int * associativity
end

module Feature_name:
sig
  type t =
    | Name of string
    | Operator of Operator.t
    | Bracket
  module Map: Map.S
end
