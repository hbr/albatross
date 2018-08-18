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
    | True
    | False
    | Number of int
  module Map: Map.S
end

val some_feature_name: string -> Feature_name.t option
val some_feature_operator: Operator.t -> Feature_name.t option
val some_feature_number: int -> Feature_name.t option
val some_feature_true:  Feature_name.t option
val some_feature_false: Feature_name.t option
