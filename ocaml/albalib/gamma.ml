open Fmlib
open Common


module Pi_info = Term.Pi_info

module Lambda_info = Term.Lambda_info

type name =
  | Normal of string
  | Binary_operator of string * Operator.t


type definition =
  | No
  | Builtin of Term.Value.t
  | Definition of Term.t


type entry = {
    name: name;
    typ: Term.typ;
    definition: definition
  }


type t = entry Segmented_array.t


let bruijn_convert (i:int) (n:int): int =
  n - i - 1



let count (c:t): int =
  Segmented_array.length c



let is_valid_index (i:int) (c:t): bool =
  0 <= i && i < count c


let index_of_level (i:int) (c:t): int =
  bruijn_convert i (count c)


let level_of_index (i:int) (c:t): int =
  bruijn_convert i (count c)


let entry (i:int) (c:t): entry =
  assert (is_valid_index i c);
  Segmented_array.elem i c


let raw_type_at_level (i:int) (c:t): Term.typ =
  (entry i c).typ


let type_at_level (i:int) (c:t): Term.typ =
  let cnt = count c in
  Term.up (cnt - i) (entry i c).typ


let term_at_level (i:int) (c:t): Term.t =
  Term.Variable (level_of_index i c)


let string_of_name (name:name): string =
  match name with
  | Normal str | Binary_operator (str, _) ->
     str


let name_of_level (i:int) (c:t): name =
    (entry i c).name


let name_of_index0 (i:int) (c:t): name =
  (entry (bruijn_convert i (count c)) c).name


let name_at_level (level: int) (gamma: t): string =
    match (Segmented_array.elem level gamma).name with
    | Binary_operator (str, _ ) -> str
    | Normal str -> str



let name_of_index (i: int) (gamma: t): string =
  match name_of_index0 i gamma with
  | Binary_operator (str, _ ) -> str
  | Normal str -> str



let empty: t =
  Segmented_array.empty


let push (name:name) (typ:Term.typ) (definition:definition) (c:t): t =
    Segmented_array.push
      {name; typ; definition}
      c


let push_local (nme:string) (typ: Term.typ) (c:t): t =
  push (Normal nme) typ No c


let push_unnamed (typ: Term.typ) (c: t): t =
  push_local " " typ c


let remove_last (n: int) (c: t): t =
  Segmented_array.remove_last n c


let add_entry (name:name) (typ:Term.typ*int) (def:definition) (c:t): t =
  let typ,n = typ
  and cnt = count c
  in
  assert (n <= cnt);
  let typ = Term.up (cnt - n) typ
  in
  push name typ def c


let int_level    = 0
let char_level   = 1
let string_level = 2


let binary_type (level:int): Term.typ * int =
  Pi (Variable 0,
      Pi (Variable 1,
          Variable 2,
          Pi_info.arrow),
      Pi_info.arrow),
  (level + 1)


let int_type (c:t) =
  Term.Variable (index_of_level int_level c)


let char_type (c:t) =
  Term.Variable (index_of_level char_level c)


let string_type (c:t) =
  Term.Variable (index_of_level string_level c)


let standard (): t =
  (* Standard context. *)
  empty

  |> add_entry (Normal "Int") (Term.any ,0) No

  |> add_entry (Normal "Character") (Term.any, 0) No

  |> add_entry (Normal "String") (Term.any, 0) No

  |> add_entry
       (Binary_operator ("+", Operator.of_string "+"))
       (binary_type int_level)
       (Builtin Term.Value.int_plus)

  |> add_entry
       (Binary_operator ("-", Operator.of_string "-"))
       (binary_type int_level)
       (Builtin Term.Value.int_minus)

  |> add_entry
       (Binary_operator ("*", Operator.of_string "*"))
       (binary_type int_level)
       (Builtin Term.Value.int_times)

  |> add_entry
       (Binary_operator ("+", Operator.of_string "+"))
       (binary_type string_level)
       (Builtin Term.Value.string_concat)

  |> add_entry
       (* List: Any -> Any *)
       (Normal "List")
       (Term.(Pi (any, any, Pi_info.arrow)), 0)
       No

  |> add_entry
       (* (=) (A: Any): A -> A -> Proposition *)
       (Binary_operator ("=", Operator.of_string "="))
       (Term.(
          Pi (any,
              Pi (Variable 0,
                  (Pi (Variable 1,
                       proposition,
                       Pi_info.arrow)),
                  Pi_info.arrow),
              Pi_info.typed "A")),
        0)
       No

  |> add_entry
       (* identity: all (A: Any): A -> A :=
            \ A x := x *)
       (Normal "identity")
       (Term.(
          Pi (any,
              Pi (Variable 0,
                  Variable 1,
                  Pi_info.arrow),
              Pi_info.typed "A")),
        0)
       (Definition
          (Term.(
             Lambda (any,
                     Lambda (Variable 0,
                             Variable 0,
                             Lambda_info.typed "x"),
                     Lambda_info.typed "A"))))

    |> add_entry
        (* true: Proposition *)
        (Normal "true")
        (Term.proposition, 0)
        No

    |> add_entry
        (* false: Proposition *)
        (Normal "false")
        (Term.proposition, 0)
        No

    |> add_entry
        (* (=>) (a b: Proposition): Proposition := a -> b *)
        (Binary_operator ("=>", Operator.of_string "=>"))
        (Term.(
            Pi (proposition,
                Pi (proposition, proposition, Pi_info.arrow),
                Pi_info.arrow)),
        0)
        (Definition
            Term.(
                Lambda (
                    proposition,
                    Lambda (proposition,
                            Pi (Variable 1,
                                Variable 1,
                                Pi_info.arrow),
                            Lambda_info.typed "b"),
                    Lambda_info.typed "a")
            )
        )


let type_of_value (v: Term.Value.t) (c: t): Term.typ =
  let open Term in
  match v with
  | Value.Int _ ->
      int_type c

  | Value.Char _ ->
      char_type c

  | Value.String _ ->
      string_type c

  | Value.Unary _ | Value.Binary _ ->
      assert false (* Illegal call! *)


let type_of_sort (s: Term.Sort.t): Term.typ =
  let open Term in
  let open Sort in
  match s with
  | Proposition ->
      Sort (Any 0)

  | Any i ->
      Sort (Any (i + 1))


let type_of_variable (i: int) (c: t): Term.typ =
  type_at_level (level_of_index i c) c


let type_of_term (t:Term.t) (c:t): Term.typ =
  let rec typ t c =
    let open Term in
    match t with
    | Sort s ->
        type_of_sort s

    | Value v ->
        type_of_value v c

    | Variable i ->
        type_of_variable i c

    | Typed (_, tp) ->
       tp

    | Appl (f, a, _) ->
       (match typ f c with
        | Pi (_, rt, _) ->
           apply rt a
        | _ ->
           assert false (* Illegal call! Term is not welltyped. *)
       )

    | Lambda (tp, exp, info) ->
       let c_inner = push_local (Lambda_info.name info) tp c in
       let rt      = typ exp c_inner
       in
       Pi (tp, rt, Pi_info.typed (Lambda_info.name info))

    | Pi (tp, rt, info) ->
       let name = Pi_info.name info in
       (match
          typ tp c, typ rt (push_local name tp c)
        with
        | Sort s1, Sort s2 ->
          let open Sort in
          (match s1, s2 with
            | Proposition, Any i ->
              Sort (Any i)

            | Any i, Any j ->
              Sort (Any (max i j))

            | _, Proposition ->
              Sort Proposition
          )

        | _, _ ->
           assert false (* Illegal call: term is not welltyped! *)
       )
  in
  typ t c



let definition_term (c: t) (idx: int): Term.t option =
  match
    (entry (level_of_index idx c) c).definition
  with
  | Definition def ->
     Some def

  | _ ->
     None



let compute (t:Term.t) (c:t): Term.t =
  let open Term in
  let rec compute term steps c =
    match term with
    | Sort _ | Value _ ->
        term, steps

    | Variable i ->
       (match (entry (level_of_index i c) c).definition with
        | No ->
            term, steps

        | Builtin v ->
           Term.Value v, steps + 1

        | Definition def ->
           def, steps + 1
       )

    | Typed (e, _ ) ->
       compute e steps c

    | Appl (Value f, Value arg, _) ->
        Value (Value.apply f arg), steps + 1

    | Appl (Value f, arg, mode) ->
        let arg, new_steps = compute arg steps c in
        if steps < new_steps then
          compute (Appl (Value f, arg, mode)) new_steps c
        else
          Appl (Value f, arg, mode), steps

    | Appl (Lambda (_, exp, _), arg, _) ->
        compute (apply exp arg) (steps + 1) c

    | Appl (Variable i, arg, mode) ->
      let f, new_steps = compute (Variable i) steps c in
      if steps < new_steps then
        compute (Appl (f, arg, mode)) new_steps c
      else
        term, new_steps

    | Appl (f, arg, mode) ->
        let f, new_steps = compute f steps c in
        if steps < new_steps then
          compute (Appl (f, arg, mode)) new_steps c
        else
          term, new_steps

    | Lambda _ ->
        term, steps

    | Pi (arg_tp, res_tp, info) ->
        let c_inner = push_local (Pi_info.name info) arg_tp c in
        let res_tp, new_steps = compute res_tp steps c_inner in
        if steps < new_steps then
            compute (Pi (arg_tp, res_tp, info)) new_steps c
        else
            term, steps
  in
  fst (compute t 0 c)


let key_split
      (t: Term.t)
      (args: (Term.t * Term.appl) list)
      (c: t)
    : Term.t * (Term.t * Term.appl) list
  =
  let rec split t args =
    match t with
    | Term.Variable i ->
       (match definition_term c i with
        | None ->
           t, args
        | Some def ->
           split def args)

    | Term.Appl (Term.Lambda (_, exp, _), arg, _) ->
       split (Term.apply exp arg) args


    | Term.Appl (f, arg, mode) ->
       split f ((arg, mode) :: args)

    | Term.Typed (term, _) ->
        term, args

    | _ ->
       t, args
  in
  split t args


let key_normal (t: Term.t) (c: t): Term.t =
  let key, args = key_split t [] c in
  List.fold_left
    (fun res (arg, mode) ->
      Term.Appl (res, arg, mode))
    key
    args


let is_subtype (_: Term.typ) (_: Term.typ) (_: t): bool =
  assert false (* nyi *)


let rec typecheck (term: Term.t) (c: t): Term.typ option =
  let open Term in
  match term with
  | Sort s ->
      Some (type_of_sort s)

  | Value v ->
      Some (type_of_value v c)

  | Variable i ->
      Some (type_of_variable i c)

  | Appl (f, arg, _ ) ->
      Option.(
        typecheck f c >>= fun f_type ->
        typecheck arg c >>= fun arg_type ->
        let key, args = key_split f_type [] c in
        ( match key, args with
          | Pi (tp, rt, _ ), []  when is_subtype arg_type tp c ->
              Some (apply rt arg)
          | _ ->
              None ))

  | Typed (_, _ ) ->
      assert false (* nyi *)

  | Lambda (_, _, _ ) ->
      assert false (* nyi *)

  | Pi (_, _, _) ->
      assert false (* nyi *)


let add_vars_from (level: int) (t: Term.t) (c: t) (set: Int_set.t): Int_set.t =
  Term.fold_free_variables
    set
    (fun i set ->
      let j = level_of_index i c in
      if j < level then
        set
      else
        Int_set.add j set)
    t



let signature (c: t) (tp: Term.typ): Signature.t =
  let rec split c tp lst =
    match key_normal tp c with
    | Term.Pi (arg_tp, res_tp, _ ) ->
       let c_inner = push_unnamed arg_tp c in
       split c_inner res_tp ((c, arg_tp, tp) :: lst)

    | _ ->
       c, tp, lst
  in
  let c_inner, res_tp, args = split c tp []
  and cnt = count c
  in
  let nargs = count c_inner - cnt
  and set = add_vars_from cnt res_tp c_inner Int_set.empty
  in
  let _, _, sign =
    List.fold_left
      (fun (i, set, sign) (c, arg_tp, tp) ->
        assert (0 < i);
        let i = i - 1 in
        let implicit = Int_set.mem (cnt + i) set
        and set = add_vars_from cnt arg_tp c set
        in
        let sign = Signature.push sign tp arg_tp implicit in
        i, set, sign)
      (nargs, set, Signature.make cnt nargs res_tp)
      args
  in
  sign
