open Common

module Info =
  struct
    type t =
      | Position of int * int
      | Unknown
  end

module Application_type =
  struct
    type t =
      | First
      | First_implicit
      | Target
      | Binary
      | Unary
      | Implicit
      | Any
  end


module Precedence =
  struct
    type associativity =
      Left | Right | Nonassoc

    type precedence = int

    type t = precedence * associativity


    let lowest: t     =        0, Nonassoc
    let comma:  t     =       10, Right         (* a,b,c = a,(b,c) *)
    let argument_list: t =    11, Nonassoc
    let quantifier: t =       20, Nonassoc
    let arrow: t      =       30, Right
    let disjunction: t =      40, Right
    let conjunction: t =      50, Right
    let negation: t =         60, Nonassoc
    let relop: t =            70, Nonassoc
    let addition: t =         80, Left
    let multiplication: t =   90, Left
    let exponentiation:t =   100, Right
    let application: t =     110, Left          (* f(x)(y) = (f(x))(y) *)
    let dot: t =             120, Left          (* x.f.g = (x.f).g *)
    let highest: t =         130, Nonassoc


    let lower_needs_parens (upper:t) (lower:t): bool =
      let lower,_ = lower
      and upper,_ = upper
      in
      lower < upper

    let left_needs_parens (upper:t) (left:t): bool =
      let lprec,lass = left
      and uprec,uass = upper
      in
      lprec < uprec || (lprec = uprec && lass = Right)

    let right_needs_parens (upper:t) (right:t): bool =
      let rprec,rass = right
      and uprec,uass = upper
      in
      rprec < uprec || (rprec = uprec && rass = Left)

  end

module Operator2 =
  struct
    type t = string * Precedence.t

    let compare ((a,_):t) ((b,_):t): int =
      Pervasives.compare a b

    module Map = Finite_map.Make (String)

    let ops: t Map.t =
      List.fold_left
        (fun m (s,prec) -> Map.add s (s,prec) m)
        Map.empty
        ["+",   Precedence.addition;
         "-",   Precedence.addition;
         "*",   Precedence.multiplication;
         "/",   Precedence.multiplication;
         "mod", Precedence.multiplication;
         "^",   Precedence.exponentiation;

         "and", Precedence.conjunction;
         "or",  Precedence.disjunction;
         "not", Precedence.negation;

         "=",   Precedence.relop;
         "/=",  Precedence.relop;
         "~",   Precedence.relop;
         "/~",  Precedence.relop;
         "<",   Precedence.relop;
         ">",   Precedence.relop;
         "<=",  Precedence.relop;
         ">=",  Precedence.relop;


         "->",  Precedence.arrow;
         "=>",  Precedence.arrow;
        ]

    let of_string (s:string): t option =
      Map.maybe_find s ops

    let string (op:t): string =
      fst op

    let precedence (op:t): Precedence.t =
      snd op
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
      | Operator  of Operator.t
      | Operator2 of Operator2.t
      | Bracket
      | True
      | False
      | Number of int
    module Map = Map.Make(
                     struct
                       type t0 = t (* Avoid cyclic error message *)
                       type t = t0
                       let compare = Pervasives.compare
                     end)
  end

let some_feature_name (s:string): Feature_name.t option =
  Some (Feature_name.Name s)

let some_feature_bracket: Feature_name.t option =
  Some Feature_name.Bracket

let some_feature_operator (op:Operator.t): Feature_name.t option =
  Some (Feature_name.Operator op )

let some_feature_number (i:int): Feature_name.t option =
  Some (Feature_name.Number i)

let some_feature_true: Feature_name.t option =
  Some Feature_name.True

let some_feature_false: Feature_name.t option =
  Some Feature_name.False

let some_feature_name_opt (s:string option): Feature_name.t option =
  Option.(s >>= fun s -> some_feature_name s)
