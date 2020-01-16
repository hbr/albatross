open Fmlib
open Common

module Located = Character_parser.Located
type 'a located = 'a Located.t

module Position = Character_parser.Position

type range = Position.t * Position.t





module Expression = struct
  type operator = string * Operator.t

  type argument =
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
    | Typed of t * t
    | Application of t * (t * argument) list
    | Function of
        formal_argument list
        * t option                        (* result type *)
        * t                               (* defining expression *)

  and formal_argument =
    string Located.t * t option


  let make_binary (e1: t) (op: operator Located.t) (e2: t): t =
    let pos_start = Located.start e1
    and pos_end   = Located.end_ e2
    and op_str,_    = Located.value op
    in
    Located.make
      pos_start
      (if op_str = ":" then
         Typed (e1, e2)
       else
         Application (
          Located.map (fun (op_str,_) -> Identifier op_str) op,
          [ e1, Operand;
            e2, Operand]))
      pos_end


  let rec binary
            (e0:t)
            (rest: (operator Located.t * t) list)
          : (t, range * string * string) result
    (* Analyze the precedence and associativity of an operator expresssion

        e0 op1 e1 op2 e2 ... opn en

       where [e0] is given explicitly and the rest is given as a list

        [(op1,e1), (op2,e2), ...]
     *)
    =
    let module Res =
      Monad.Result
        (struct type t = range * string * string end)
    in
    match rest with
    | [] ->
       Ok e0

    | [op, e1] ->
       Ok (make_binary e0 op e1)

    | (op1,e1) :: (op2,e2) :: rest ->
       (* e0 op1 e1 op2 e2 rest *)
       let op1_string, op1_data = Located.value op1
       and op2_string, op2_data = Located.value op2
       in
       let cmp = Operator.compare op1_data op2_data in
       if cmp = 0 then
         match Operator.associativity op1_data with
         | Operator.No ->
            (* Error case: I cannot decide on how to parenthesize *)
            Error ((Located.start e0, Located.end_ e2), op1_string, op2_string)
         | Operator.Left ->
            (* (e1 op1 e2) op2 e2 rest *)
            binary (make_binary e0 op1 e1) ((op2,e2) :: rest)
         | Operator.Right ->
            (* e1 op1 (e2 op2 e2 rest) *)
            Res.map (make_binary e0 op1) (binary e1 ((op2,e2) :: rest))

       else if cmp = +1 then
         (* (e1 op1 e2) op2 e2 rest *)
         binary (make_binary e0 op1 e1) ((op2,e2) :: rest)

       else
         (* e0 op1 (e1 op2 e2 rest1) rest2 *)
         let rest2, rest3 =
           List.split_at
             (fun (op,_) ->
               Operator.precedence (snd (Located.value op))
               <= Operator.precedence op1_data)
             rest
         in
         Res.(binary e1 ((op2,e2) :: rest2)
              >>= fun e ->
              binary (make_binary e0 op1 e) rest3)
end









module Command =
  struct
    type t =
      | Evaluate of Expression.t
      | Type_check of Expression.t
      | Exit
      | Do_nothing
  end





module Problem =
  struct
    type t =
      | Operator_precedence of
          range
          * string * string (* the 2 operatos strings *)

      | Illegal_name of range * string (* expectation *)

      | Illegal_command of range * string list

      | Ambiguous_command of range * string list
  end

module P =
  Character_parser.Advanced (Unit) (Command) (String) (Problem) (String)
include P



let keywords: String_set.t =
  let open String_set in
  empty
  |> add "create"
  |> add "inspect"


let string (str: string): unit t =
  P.string str (fun i -> "'" ^ String.one str.[i] ^ "'")


let char (c:char): unit t =
  P.char c ("'" ^ String.one c ^ "'")


let whitespace_char: char t =
  P.whitespace_char "whitespace"


let line_comment: unit t =
  backtrackable (string "--") "\"--\""
  >>= fun _ ->
  skip_zero_or_more
    (expect
       (fun c -> c <> '\n')
       "any char except newline")
  >>= fun _ ->
  return ()


let multiline_comment: unit t =
  let rec to_end (): unit t =
    (char '-' >>= fun _ ->
     (char '}'
     <|> to_end ()))
    <|> (expect (fun _ -> true) "any char"
         >>= fun _ ->
         to_end ())
  in
  backtrackable
    (string "{-")
    "\"{-\""
  >>= fun _ ->
  to_end ()



let whitespace: int t =
  skip_zero_or_more
    ((map (fun _ -> ()) whitespace_char)
     <|> line_comment
     <|> multiline_comment)



let word_ws
      (start: char->bool)
      (inner: char->bool)
      (msg:   string)
    : string located t
  =
  located @@ word start inner msg
  |. whitespace
  >>= succeed


let identifier: string located t =
  word_ws
    Char.is_letter
    (fun c -> Char.is_letter c || Char.is_digit c || c = '_')
    "identifier"


let formal_argument_name: string located t =
  identifier >>= fun name_located ->
  let name = Located.value name_located in
  if String_set.mem name keywords
     || name = "Proposition"
     || name = "Any"
  then
    fail
      (Problem.Illegal_name (Located.range name_located, "<argument name>"))
  else
    return name_located


let number: string located t =
  word_ws
    Char.is_digit
    Char.is_digit
    "number"


let identifier_expression: Expression.t t =
  map
    (Located.map
       (fun s ->
         if s = "Proposition" then
           Expression.Proposition
         else if s = "Any" then
           Expression.Any
         else
           Expression.Identifier s
    ))
    (identifier >>= fun s ->
     if String_set.mem (Located.value s) keywords then
       fail (Problem.Illegal_name (Located.range s, "<identifier>"))
     else
       return s)


let number_expression: Expression.t t =
  map
    (Located.map (fun s -> Expression.Number s))
    number



let literal_string: Expression.t t =
  located (
      return
        (fun chars ->
          let chars = Array.of_list chars in
          let len   = Array.length chars in
          Expression.String (String.init len (fun i -> chars.(i))))
      |. char '"'
      |= zero_or_more
           (expect
              (fun c ->
                let i = Char.code c in
                Char.code ' ' <= i && i < 128 && c <> '"')
              "string character")
      |. char '"')
  |. whitespace


let literal_char: Expression.t t =
  located (
      return
        (fun c -> Expression.Char (Char.code c))
      |. char '\''
      |= expect
           (fun c -> c <> '\'' && c <> '\n')
           "character"
      |. char '\'')
  |. whitespace



let colon: unit t =
  backtrackable
    (char ':'
     |. not_followed_by (char '=') "not '='")
    "':'"


let assign: unit t =
  backtrackable
    (string ":=")
    "':='"


let operator: Expression.operator Located.t t =
  let op_chars = "+-^*/=~<>" in
  let len = String.length op_chars in
  let is_op_char c =
    String.find (fun op_char -> c = op_char) 0 op_chars < len
  in
  located
  @@ map
       (fun lst ->
         let op_str = String.of_list lst
         in
         op_str, Operator.of_string op_str)
       (one_or_more
          (expect
             is_op_char
             "operator character")
        <|> map (fun _ -> [':']) colon
        <?> "operator or ':'"
       )
  |. whitespace
  >>= succeed


let lonely_operator: Expression.t t =
  map
    (fun op_located ->
      Located.map (fun op -> Expression.Operator op) op_located)
    operator


let char_ws (c:char): unit t =
  char c |. whitespace


let rec expression (): Expression.t t =

  let result_type: Expression.t option t =
    optional
      (colon |. whitespace >>= expression)
  in

  let formal_argument: (string located * Expression.t option) t =
    (char_ws '(' >>= fun _ ->
     formal_argument_name >>= fun name ->
     colon |. whitespace >>= expression >>= fun typ ->
     char_ws ')' >>= fun _ ->
     return (name, Some typ)
    )
    <|> map (fun name -> name, None) formal_argument_name
  in

  let primary (): Expression.t t =
    identifier_expression
    <|> number_expression
    <|> literal_char
    <|> literal_string
    <|> ( ( char_ws '('
            >>= fun _ ->
            (* op_expression has to be encapsulated in a function,
               otherwise infinite recursion!! *)
            expression () <|> lonely_operator)
          |. char_ws ')'
        )
    <|> located
          (return (fun args rt exp -> Expression.Function (args, rt, exp))
           |. char_ws '\\'
           |= one_or_more formal_argument
           |= result_type
           |= (assign |. whitespace >>= expression))
    <?> "expression"
  in

  let application =
    primary () >>= fun f ->
    located (zero_or_more (primary ())) >>= fun args ->
    match Located.value args with
    | [] ->
       return f
    | arg_lst ->
        let arg_lst = List.map (fun arg -> arg, Expression.Normal) arg_lst in
        let pos1 = Located.start f
        and pos2 = Located.end_ args
        and f, arg_lst =
         match Located.value f with
         | Expression.Application (f0, arg_lst0) ->
             f0, arg_lst0 @ arg_lst
         | _ ->
             f, arg_lst
        in
        return
          (Located.make
             pos1
             (Expression.Application (f, arg_lst))
             pos2)
  in

  let operator_and_operand =
    return (fun op exp -> (op,exp))
    |= operator
    |= application
  in

  (* expression parsing *)
  application >>= fun e1 ->

  zero_or_more operator_and_operand >>= fun lst ->

  match Expression.binary e1 lst with
  | Ok e ->
     return e

  | Error (range, op1, op2) ->
     fail (Problem.Operator_precedence (range, op1, op2))



let commands: (string * Command.t t) list =
  ["evaluate",
   map (fun e -> Command.Evaluate e) (expression ());

   "exit", return Command.Exit;

   "typecheck",
   map (fun e -> Command.Type_check e) (expression ());
  ]


let find_command (cmd: string): (string * Command.t t) list =
  List.filter
    (fun (str, _) ->
      String.is_prefix cmd str)
  commands


let command_names (cs: (string * Command.t t) list): string list =
  List.map fst cs


let command: Command.t t =
  (char ':' >>= fun _ ->
   (identifier <?> "command")

   >>= fun cmd ->
   match find_command (Located.value cmd) with
   | [] ->
      fail
        (Problem.Illegal_command (Located.range cmd, command_names commands))

   | [_, arg_parser] ->
      arg_parser

   | lst ->
      fail
        (Problem.Ambiguous_command
           (Located.range cmd, command_names lst))
  )
  <|> (return
         (fun exp ->
           match exp with
           | None ->
              Command.Do_nothing
           | Some exp ->
              Command.Evaluate exp)
       |. whitespace
       |= optional (expression ()))


let initial: parser =
  make (command |. expect_end "end of command") ()
