open Fmlib


let bruijn_convert (i:int) (n:int): int =
  assert (i < n);
  n - i - 1


module Value =
  struct
    type t =
      | Int of int (* int32? *)
      | Char of int
      | String of string
      | Unary of (t -> t)
      | Binary of (t -> t -> t)


    let int_value str =
      let len = String.length str
      in
      let rec value i v =
        if i = len then
          Some (Int v)
        else
          let v1 = v * 10 + (Char.code str.[i] - Char.code '0') in
          if v1 < v then
            None
          else
            value (i+1) v1
      in
      value 0 0

    let number_values (str:string): t list =
      match int_value str with
      | None ->
         []
      | Some v ->
         [v]

    let int_binary (f:int -> int -> int): t =
      Binary
        (fun a b ->
          match a, b with
          | Int a, Int b ->
             Int (f a b)
          | _ ->
             assert false (* Illegal call *)
        )

    let string_binary (f:string -> string -> string): t =
      Binary
        (fun a b ->
          match a, b with
          | String a, String b ->
             String (f a b)
          | _ ->
             assert false (* Illegal call *)
        )


    let int_plus: t =
      int_binary (+)

    let int_minus: t =
      int_binary (-)

    let int_times: t =
      int_binary ( * )

    let string_concat: t =
      string_binary (^)

    let apply (f:t) (a:t): t =
      match f with
      | Unary f ->
         f a
      | Binary f ->
         Unary (f a)
      | _ ->
         assert false
  end






module Sort =
  struct
    type t =
      | Proposition
      | Any of int

    let is_sub (s1:t) (s2:t): bool =
      match s1, s2 with
      | Proposition, Proposition | Proposition, Any _ ->
         true
      | Any i, Any j ->
         i <= j
      | _, _ ->
         false

    let is_super (s1:t) (s2:t): bool =
      is_sub s2 s1
  end







type appl =
  | Normal
  | Binary



type t =
  | Sort of Sort.t

  | Variable of int

  | Appl of t * t * appl

  (*| Lam of typ * t*)

  | Pi of string * typ * t

  | Value of Value.t
and typ = t


let proposition: t =
  Sort Sort.Proposition

let any: t =
  Sort (Sort.Any 0)


let char (code:int): t =
  Value (Value.Char code)


let string (s:string): t =
  Value (Value.String s)


let up_from (delta:int) (start:int) (t:t): t =
  let rec up t nb =
    match t with
    | Sort _ | Value _ ->
       t

    | Variable i when i < nb + start->
       Variable i

    | Variable i ->
       Variable (i + delta)

    | Appl (f, a, mode) ->
       Appl (up f nb, up a nb, mode)

    | Pi (nme, tp, t ) ->
       Pi (nme,
           up tp nb,
           up t (nb + 1))

  in
  up t 0


let up (delta:int) (t:t): t =
  assert (0 <= delta);
  if delta = 0 then
    t
  else
    up_from delta 0 t




let down_from (delta:int) (start:int) (t:t): t option =
  assert (0 <= delta);
  let rec down t nb =
    let open Option in
    match t with
    | Sort _ | Value _ ->
       Some t

    | Variable i when i < nb + start->
       Some (Variable i)

    | Variable i when i < nb + start + delta ->
       None

    | Variable i ->
       Some (Variable (i - delta))

    | Appl (f, a, mode) ->
       down f nb >>= fun f ->
       down a nb >>= fun a ->
       Some (Appl (f, a , mode))

    | Pi (nme, tp, t ) ->
       down tp nb >>= fun tp ->
       down t (nb + 1) >>= fun t ->
       Some (Pi (nme, tp, t))
  in
  down t 0


let down (delta:int) (t:t): t option =
  down_from delta 0 t


let substitute (f:int -> t) (t:t): t =
  let rec sub t nb =
    match t with
    | Sort _ | Value _ ->
        t

    | Variable i when i < nb ->
       t

    | Variable i ->
       up nb (f @@ i - nb)

    | Appl (f, a, mode) ->
       Appl (sub f nb, sub a nb, mode)

    | Pi (nme, tp, t) ->
       Pi (nme, sub tp nb, sub t (nb + 1))
  in
  sub t 0



let apply (f:t) (a:t): t =
  substitute
    (fun i ->
      if i = 0 then
        a
      else
        Variable (i - 1))
    f



let rec application (f:t) (nargs:int) (mode:appl): t =
  if nargs = 0 then
    f
  else
    application
      (Appl (f, Variable (nargs - 1), mode))
      (nargs - 1)
      mode
