type t


type leaning =
  | Left
  | Right
  | No


(** Precedence/associativity of colon ':' operator. *)
val colon: t

(** Precedence/associativity of relation operators. *)
val relation: t

(** Precedence/associativity of addition operators. *)
val addition: t


(** Precedence/associativity of multiplication operators. *)
val multiplication: t


(** Precedence/associativity of function application. *)
val application: t


(** [of_string op] computes the precedence information of the operator [op]
   given as a string. for unknow operators the highest precedence below
   function application and left associativity is returned. *)
val of_string: string -> t


(** [needs_parens lower is_left upper] decides if the lower operand [lower]
   used as a left or right operand (indicated by the flag [is_left]) for
   [upper] needs parentheses. *)
val needs_parens: t option -> bool -> t -> bool


(** [leaning op1 op2] decides if the expression [a op1 b op2 c] shall be
   parsed as left leaning [(a op1 b) op2 c] or right leaning [a op1 (b op2
   c)]. *)
val leaning: t -> t -> leaning
