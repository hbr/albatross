module Info:
sig
  type t =
    | Position of int * int
    | Unknown
end

module Application_type:
sig
  type t =
    | First
    | First_implicit
    | Target
    | Binary
    | Unary
    | Implicit
    | Any
end

module Precedence:
sig
  type t

  val lowest :t
  val comma: t
  val argument_list:t
  val quantifier: t
  val arrow: t
  val disjunction: t
  val conjunction: t
  val negation: t
  val relop: t
  val addition: t
  val multiplication:t
  val exponentiation:t
  val application: t
  val dot: t
  val highest:t

  val lower_needs_parens: t -> t -> bool
  val left_needs_parens:  t -> t -> bool
  val right_needs_parens: t -> t -> bool
end


module Operator2:
sig
  type t
  val of_string: string -> t option
  val string: t -> string
  val precedence: t -> Precedence.t
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
    | Operator  of Operator.t
    | Operator2 of Operator2.t
    | Bracket
    | True
    | False
    | Number of int
  module Map: Map.S
end

val some_feature_name: string -> Feature_name.t option
val some_feature_bracket: Feature_name.t option
val some_feature_operator: Operator.t -> Feature_name.t option
val some_feature_number: int -> Feature_name.t option
val some_feature_true:  Feature_name.t option
val some_feature_false: Feature_name.t option
val some_feature_name_opt: string option -> Feature_name.t option
