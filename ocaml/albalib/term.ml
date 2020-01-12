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


    let int_value (str: string): t option =
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


module Lambda_info =
  struct
    type t = {
        name:  string;    (* name of the argument *)
        typed: bool;      (* false: user has not given type information for
                             the argument '\ x: RT := exp' *)
      }
    let name (i:t): string =
      i.name

    let is_anonymous (i:t): bool =
      i.name = "_"

    let is_typed (i:t): bool =
      i.typed

    let typed (name: string): t =
      {name; typed = true}

    let untyped (name: string): t =
      {name; typed = false}
  end

module Pi_info =
  struct
    type t = {
        name:  string; (* name of the argument *)
        arrow: bool;   (* user has written 'A -> B' instead of 'all (nme:A):
                          R' *)
        typed: bool    (* false, if user has given no type information 'all x:
                          R' *)
      }

    let name (i:t): string =
      i.name

    let is_anonymous (i:t): bool =
      i.name = "_"

    let is_arrow (i:t): bool =
      i.arrow

    let is_typed (i:t): bool =
      i.typed

    let arrow: t =
      {name = "_"; arrow = true; typed = true}

    let typed (name: string) : t =
      {name; arrow = false; typed = true}

    let untyped (name: string) : t =
      {name; arrow = false; typed = false}

  end


type appl =
  | Normal
  | Implicit
  | Binary



type t =
  | Sort of Sort.t

  | Variable of int

  | Typed of t * typ

  | Appl of t * t * appl

  | Lambda of typ * t * Lambda_info.t

  | Pi of typ * typ * Pi_info.t

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


let number_values (s:string): t list =
  List.map (fun v -> Value v) (Value.number_values s)

let up_from (delta:int) (start:int) (t:t): t =
  let rec up t nb =
    match t with
    | Sort _ | Value _ ->
       t

    | Variable i when i < nb + start->
       Variable i

    | Variable i ->
       Variable (i + delta)

    | Typed (e, tp) ->
       Typed (up e nb, up tp nb)

    | Appl (f, a, mode) ->
       Appl (up f nb, up a nb, mode)

    | Lambda (tp, exp, info) ->
       Lambda (up tp nb,
               up exp (nb + 1),
               info)

    | Pi (tp, rt, info) ->
       Pi (up tp nb,
           up rt (nb + 1),
           info)

  in
  up t 0


let up (delta:int) (t:t): t =
  assert (0 <= delta);
  if delta = 0 then
    t
  else
    up_from delta 0 t


let up1 (t: t): t =
  up 1 t




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

    | Typed (e, tp) ->
       down e nb  >>= fun e ->
       down tp nb >>= fun tp ->
       Some (Typed (e, tp))

    | Appl (f, a, mode) ->
       down f nb >>= fun f ->
       down a nb >>= fun a ->
       Some (Appl (f, a , mode))

    | Lambda (tp, exp, info ) ->
       down tp nb >>= fun tp ->
       down exp (nb + 1) >>= fun exp ->
       Some (Lambda (tp, exp, info))

    | Pi (tp, t, info ) ->
       down tp nb >>= fun tp ->
       down t (nb + 1) >>= fun t ->
       Some (Pi (tp, t, info))
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

    | Typed (e, tp) ->
       Typed (sub e nb, sub tp nb)

    | Appl (f, a, mode) ->
       Appl (sub f nb, sub a nb, mode)

    | Lambda (tp, exp, info) ->
       Lambda (sub tp nb, sub exp (nb + 1), info)

    | Pi (tp, rt, info) ->
       Pi (sub tp nb, sub rt (nb + 1), info)
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



let fold_free_variables (s: 'a) (f: int -> 'a -> 'a) (t: t): 'a =
  let rec fold s t nb =
    match t with
    | Value _ ->
       s

    | Sort _ ->
       s

    | Variable i when i < nb ->
       s

    | Variable i ->
       f (i - nb) s

    | Typed (e, tp) ->
       fold (fold s e nb) tp nb

    | Appl (f, a, _) ->
       fold (fold s f nb) a nb

    | Lambda (tp, exp, _) ->
       fold (fold s tp nb) exp (nb + 1)

    | Pi (tp, rt, _) ->
       fold (fold s tp nb) rt (nb + 1)
  in
  fold s t 0
