open Fmlib
open Common
open Character_parser

type located_string = string Located.t
type 'a located = 'a Located.t


module Expression = struct
  type operator = string * Operator.t


  type t =
    t0 Located.t


  and t0 =
    | Identifier of string
    | Number of string
    | Char of int
    | String of string
    | Operator of operator
    | Binary of t * operator located * t
    | Parenthesized of t


    let rec binary
              (e1:t)
              (rest: (operator Located.t * t) list)
            : (t, string * string) result
      =
      let mk_bin e1 op e2 =
        let pos_start = Located.start e1
        and pos_end   = Located.end_ e2 in
        Located.make
          pos_start (Binary (e1,op,e2)) pos_end
      in
      match rest with
      | [] ->
         Ok e1

      | [op, e2] ->
         Ok (mk_bin e1 op e2)

      | (op1,e2) :: (op2,e3) :: rest ->
         (* e1 op1 e2 op2 e3 rest *)
         let op1_string, op1_data = Located.value op1
         and op2_string, op2_data = Located.value op2
         in
         match Operator.leaning op1_data op2_data with
         | Operator.Left ->
            (* (e1 op1 e2) op2 e3 rest *)
            binary (mk_bin e1 op1 e2) ((op2,e3) :: rest)

         | Operator.Right ->
            (* e1 op1 (e2 op2 e3 rest) *)
            let module Res =
              Monad.Result (struct type t = string * string end)
            in
            Res.map (mk_bin e1 op1) (binary e2 ((op2,e3) :: rest))

         | Operator.No ->
            (* Error case: I cannot decide on how to parenthesize *)
            Error (op1_string, op2_string)
end







module Final =
  struct
    type t = Expression.t option
  end






module Context_msg =
  struct
    type t =
      | Operand
  end







module Problem =
  struct
    type t =
      | Expect of string
      | Operator_precedence of string * string
  end

module P = Advanced (Unit) (Final) (Problem) (Context_msg)
include P


let whitespace: int t =
  P.whitespace (Problem.Expect "whitespace")


let char (c:char): unit t =
  char
    c
    (Problem.Expect (
         if c = '\'' then
           String.one c
         else
           "'" ^ String.one c ^ "'"))


let word_ws
      (start:char->bool)
      (inner:char->bool)
      (msg:Problem.t)
      (convert: string -> Expression.t0)
    : Expression.t t
  =
  return (fun loc_str -> Located.map convert loc_str)
  |= located @@ word start inner msg
  |. whitespace


let identifier: Expression.t t =
  word_ws
    Char.is_letter
    (fun c -> Char.is_letter c || Char.is_digit c || c = '_')
    (Problem.Expect "identifier")
    (fun str -> Expression.Identifier str)


let number: Expression.t t =
  word_ws
    Char.is_digit
    Char.is_digit
    (Problem.Expect "number")
    (fun str -> Expression.Number str)


let lang_string: Expression.t t =
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
              (Problem.Expect "string character"))
      |. char '"')
  |. whitespace


let lang_char: Expression.t t =
  located (
      return
        (fun c -> Expression.Char (Char.code c))
      |. char '\''
      |= expect
           (fun c -> c <> '\'' && c <> '\n')
           (Problem.Expect "character")
      |. char '\'')
  |. whitespace



let operator: Expression.operator Located.t t =
  let op_chars = "+-^*/=~<>" in
  let len = String.length op_chars in
  let is_op_char c =
    String.find (fun op_char -> c = op_char) 0 op_chars < len
  in
  located
  @@ map
       (fun lst ->
         let arr = Array.of_list lst in
         let op_str =
           String.init
             (Array.length arr)
             (fun i -> arr.(i))
         in
         op_str, Operator.of_string op_str)
       (one_or_more
          (expect
             is_op_char
             (Problem.Expect "operator character")))
  |. whitespace


let lonely_operator: Expression.t t =
  map
    (fun op_located ->
      Located.map (fun op -> Expression.Operator op) op_located)
    operator


let char_ws (c:char): unit t =
  char c |. whitespace



let rec op_expression (): Expression.t t =
  let atomic (): Expression.t t =
    identifier
    <|> number
    <|> lang_char
    <|> lang_string
    <|> located
          (return
             (fun op_exp -> Expression.Parenthesized op_exp)
           |= (char_ws '('
               >>= fun _ ->
               (* op_expression has to be encapsulated in a function,
                  otherwise infinite recursion!! *)
               op_expression () <|> lonely_operator)
           |. char_ws ')'
          )
  in
  let operator_and_operand =
    return (fun op exp -> (op,exp))
    |= operator
    |= in_context Context_msg.Operand (atomic ())
  in

  atomic () >>= fun e1 ->

  zero_or_more operator_and_operand >>= fun lst ->

  match Expression.binary e1 lst with
  | Ok e ->
     return e

  | Error (op1,op2) ->
     fail (Problem.Operator_precedence (op1,op2))


let initial: parser =
  make
    (return identity
     |. whitespace
     |= optional @@ op_expression ()
     |. expect_end (Problem.Expect "end of command"))
    ()
