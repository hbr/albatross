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





module Application_info =
struct
    type t =
      | Normal
      | Implicit
      | Binary
end








(* ----------------------------------------------------------- *)
(* Term                                                        *)
(* ----------------------------------------------------------- *)


type t =
  | Sort of Sort.t

  | Variable of int

  | Typed of t * typ

  | Appl of t * t * Application_info.t

  | Lambda of typ * t * Lambda_info.t

  | Pi of typ * typ * Pi_info.t

  | Value of Value.t

and typ = t

and formal_argument = string * typ

and inductive = {
    base_count: int;
    n_up: int;
    parameters: formal_argument list;
    types: (formal_argument * formal_argument array) array}



let proposition: t =
    Sort Sort.Proposition

let any: t =
    Sort (Sort.Any 0)

let any_uni (uni: int): t =
    Sort (Sort.Any uni)

let char (code:int): t =
    Value (Value.Char code)


let string (s:string): t =
    Value (Value.String s)


let number_values (s:string): t list =
  List.map (fun v -> Value v) (Value.number_values s)


let variable i: t =
    Variable i


let application (f: t) (a: t): t =
    Appl (f, a, Application_info.Normal)


let lambda (name: string) (tp: typ) (exp: t): t =
    assert (name <> "");
    Lambda (tp, exp, Lambda_info.typed name)


let lambda_untyped (name: string) (tp: typ) (exp: t): t =
    assert (name <> "");
    Lambda (tp, exp, Lambda_info.untyped name)


let product (name: string) (arg_tp: typ) (result_tp: typ): t =
    assert (name <> "");
    let info =
        if name = "_" then
            Pi_info.arrow
        else
            Pi_info.typed name
    in
    Pi (arg_tp, result_tp, info)


let product_untyped (name: string) (arg_tp: typ) (result_tp: typ): t =
    assert (name <> "");
    assert (name <> "_");
    Pi (arg_tp, result_tp, Pi_info.untyped name)


let arrow (arg_tp: typ) (result_tp: typ): t =
    product "_" arg_tp result_tp


let lambda_in (fargs: formal_argument list) (exp: t): t =
    List.fold_right
        (fun (name, arg_tp) ->
            lambda name arg_tp)
        fargs
        exp


let product_in (fargs: formal_argument list) (result_tp: t): t =
    List.fold_right
        (fun (name, arg_tp) ->
            product name arg_tp)
        fargs
        result_tp




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

    | Pi (tp, rt, info ) ->
       down tp nb >>= fun tp ->
       down rt (nb + 1) >>= fun rt ->
       Some (Pi (tp, rt, info))
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



let rec apply_nargs (f:t) (nargs:int) (mode: Application_info.t): t =
  if nargs = 0 then
    f
  else
    apply_nargs
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




(* ----------------------------------------------------------- *)
(* Index to level conversion                                   *)
(* ----------------------------------------------------------- *)


let rec to_index (n: int) (term: t): t =
    match term with
    | Value _ | Sort _ ->
        term

    | Variable i ->
        Variable (bruijn_convert i n)

    | Appl (f, arg, info) ->
        Appl (to_index n f,
              to_index n arg,
              info)

    | Typed (term, typ) ->
        Typed (to_index n term,
               to_index n typ)

    | Lambda (typ, exp, info) ->
        Lambda (to_index n typ,
                to_index (n + 1) exp,
                info)

    | Pi (typ, rtyp, info) ->
        Pi (to_index n typ,
            to_index (n + 1) rtyp,
            info)


let to_level = to_index



(* ----------------------------------------------------------- *)
(* Inductive                                                   *)
(* ----------------------------------------------------------- *)

  module Inductive =
  struct
    let make_simple_inductive
        (base_count: int)
        (parameters: formal_argument list)
        (typ: formal_argument)
        (constructors: formal_argument list)
        : inductive
        =
        {base_count;
         n_up = 0;
         parameters;
         types = [| typ, Array.of_list constructors|]}

    type term = t

    type t =
        | Type of int * inductive
        | Constructor of int * int * inductive


    let is_simple (ind: inductive): bool =
        Array.length ind.types = 1

    module Type =
    struct
        type t = int * inductive

        let simple (ind: inductive): t =
            assert (is_simple ind);
            0, ind
    end

    let typ (ind: inductive): t =
        Type (0, ind)


    let constructor (i: int) (ind: inductive): t =
        assert (is_simple ind);
        Constructor (0, i, ind)
  end
