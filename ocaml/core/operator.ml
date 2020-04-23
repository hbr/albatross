open Fmlib
open Common

type assoc =
  | Left
  | Right
  | No



type t =
  int * assoc (* Invariant: The same precedence leads to the same assoc
                 i.e. the precedence is the key to the operator group which
                 are considered equivalent. *)


let where             = (10,   Left)
let assign            = (20,   Right)

let comma             = (30,   Right)
let colon             = (40,   Right)
let arrow             = (50,   Right)
let push_arg          = (55,   Left)
let pull_arg          = (56,   Right)
let relation          = (60,   No)
let addition          = (70,   Left)
let multiplication    = (80,   Left)
let exponentiation    = (90,   Right)

let unknown           = (100,  Left)
let application       = (200,  Left)

(* Precedences:

    expression                  parse               requirement
    --------------------------------------------------------------
    exp: A -> B                 exp: (A -> B)       colon < arrow

    \x := exp: T                \x := (exp: T)      assign < colon

    \x y := x => y              \x y := (x => y)

*)



let map: (int * assoc) String_map.t
  =
  let open String_map in
  empty
  |> add ","  comma
  |> add "->" arrow
  |> add "=>" arrow
  |> add ":=" assign
  |> add ":"  colon
  |> add "|>" push_arg
  |> add "<|" pull_arg
  |> add "="  relation
  |> add "/=" relation
  |> add "<"  relation
  |> add ">"  relation
  |> add "<=" relation
  |> add ">=" relation
  |> add "+"  addition
  |> add "-"  addition
  |> add "*"  multiplication
  |> add "/"  multiplication
  |> add "^"  exponentiation


let of_string (op:string): t =
  match
    String_map.maybe_find op map
  with
  | None ->
     unknown

  | Some d ->
     d



let compare ((prec1,_): t) ((prec2,_): t): int =
  Stdlib.compare prec1 prec2


let precedence = fst

let associativity = snd


let needs_parens
      (lower: t option)
      (is_left:bool)
      (upper: t)
    : bool
  =
  match lower with
  | None ->
     false

  | Some (low_prec, low_assoc) ->
     let prec, assoc = upper
     in
     assert (prec <> low_prec || low_assoc = assoc);

     prec > low_prec
     || (prec = low_prec  (* because of the invariant lower and upper have the
                             same associativity. *)
         && (match assoc with
             | No -> true

             | Left ->
                not is_left

             | Right ->
                is_left))
