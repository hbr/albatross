module Info =
  struct
    type t =
      | Position of int * int
      | Unknown
  end


module Operator =
  struct
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

    let normal_precedence:     int = 20
    let quantifier_precedence: int = 40
    let highest_precedence:    int = 1000

    let data (op:t): string * int * associativity =
      match op with
      | Commaop   -> ",",   10, Right
      | Colonop   -> ":",   30, Nonassoc
      (* Logical operators *)
      | Arrowop   -> "->",  50, Right
      | Orop      -> "or",  51, Right
      | Andop     -> "and", 52, Right
      | Notop     -> "not", 53, Nonassoc
      (* Relational operators *)
      | Eqop      -> "=",   60, Nonassoc
      | NEqop     -> "/=",  60, Nonassoc
      | Eqvop     -> "~",   60, Nonassoc
      | NEqvop    -> "/~",  60, Nonassoc
      | LTop      -> "<",   60, Nonassoc
      | LEop      -> "<=",  60, Nonassoc
      | GTop      -> ">",   60, Nonassoc
      | GEop      -> ">=",  60, Nonassoc
      (* Addition operators *)
      | Plusop    -> "+",   70, Left
      | Minusop   -> "-",   70, Left
      (* Multiplication operators *)
      | Timesop   -> "*",   80, Left
      | Divideop  -> "/",   80, Left
      | Modop     -> "mod", 80, Left
      (* Exponentiation operators *)
      | Caretop   -> "^",   90, Right
 end

module Feature_name =
  struct
    type t =
      | Name of string
      | Operator of Operator.t
      | Bracket
    module Map = Map.Make(
                     struct
                       type t0 = t (* Avoid cyclic error message *)
                       type t = t0
                       let compare = Pervasives.compare
                     end)
  end
