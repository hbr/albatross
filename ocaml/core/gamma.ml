open Fmlib


module Pi_info = Term.Pi_info

module Lambda_info = Term.Lambda_info

module Sequence = Segmented_array


type definition =
  | Axiom
  | Assumption
  | Builtin_type of string
  | Builtin of string * Term.Value.t
  | Definition of Term.t
  | Inductive_type of int * int
  | Constructor of int * int * int


type entry = {
    name: string;
    typ: Term.typ;
    definition: definition
  }


type t = {
        entries: entry Sequence.t;
        inductives: (int * Inductive.t) Sequence.t;
}


let empty: t =
    {
        entries = Sequence.empty;
        inductives = Sequence.empty;
    }



let bruijn_convert (i:int) (n:int): int =
  n - i - 1



let count (c:t): int =
    Sequence.length c.entries


let count_inductive (c: t): int =
    Sequence.length c.inductives


let is_valid_index (i:int) (c:t): bool =
  0 <= i && i < count c


let index_of_level (i:int) (c:t): int =
  bruijn_convert i (count c)


let level_of_index (i:int) (c:t): int =
  bruijn_convert i (count c)


let level_forall (p: int -> bool) (term: Term.t) (c: t): bool =
    Term.forall
        (fun level -> p (index_of_level level c))
        term


let level_has (p: int -> bool) (term: Term.t) (c: t): bool =
    Term.has
        (fun level -> p (index_of_level level c))
        term



let entry (level: int) (c: t): entry =
  assert (level < count c);
  Sequence.elem level c.entries


let raw_type_at_level (i:int) (c:t): Term.typ =
  (entry i c).typ


let type_at_level (i:int) (c:t): Term.typ =
  let cnt = count c in
  Term.up (cnt - i) (entry i c).typ



let variable_at_level (i:int) (c:t): Term.t =
    Term.Variable (index_of_level i c)



let name_at_level (level: int) (gamma: t): string =
    (entry level gamma).name


let name_of_index (i: int) (gamma: t): string =
    (entry (bruijn_convert i (count gamma)) gamma).name



let push (name: string) (typ: Term.typ) (definition: definition) (c: t): t =
    {c with
        entries =
            Sequence.push
                {name; typ; definition}
                c.entries;
    }


let push_local (nme: string) (typ: Term.typ) (c:t): t =
    push nme typ Assumption c


let add_definition
    (name: string) (typ: Term.typ) (def: Term.t) (c: t)
    : t
=
    push name typ (Definition def) c





let add_entry (name: string) (typ:Term.typ*int) (def:definition) (c:t): t =
    let typ,n = typ
    and cnt = count c
    in
    assert (n <= cnt);
    let typ = Term.up (cnt - n) typ
    in
    push name typ def c



let add_axiom (name: string) (typ: Term.typ) (c: t): t =
    push
        name
        typ
        Axiom
        c



let add_builtin_type (descr: string) (name: string) (typ: Term.typ) (c: t): t =
    push
        name
        typ
        (Builtin_type descr)
        c



let add_inductive (ind: Inductive.t) (c: t): t =
    let cnti0 = count_inductive c
    and cnt0  = count c
    and ntypes = Inductive.count_types ind
    in
    let open Common.Interval in
    let c1 =
        fold
            c
            (fun i ->
                let name, typ = Inductive.ith_type i ind in
                push
                    name
                    (Term.up i typ)
                    (Inductive_type (cnti0, i))
            )
            0 ntypes
    in
    let c2 =
        fold
            c1
            (fun i c ->
                let nprevious =
                    Inductive.count_previous_constructors i ind
                in
                fold
                    c
                    (fun j ->
                        let name, typ =
                            Inductive.constructor i j ind
                        in
                        push
                            name
                            (Term.up (nprevious + j) typ)
                            (Constructor (cnti0, i, j))
                    )
                    0 (Inductive.count_constructors i ind)
            )
            0 ntypes
    in
    { c2 with
        inductives =
            Sequence.push (cnt0, ind) c.inductives;
    }


let inductive_at_level (level: int) (c: t): Inductive.t =
    let i =
        match (Sequence.elem level c.entries).definition with
        | Inductive_type (i, _) ->
            i
        | Constructor (i, _, _) ->
            i
        | _ ->
            assert false (* Illegal call! *)
    in
    let cnt0, ind = Sequence.elem i c.inductives in
    Inductive.up (count c - cnt0) ind



let int_level    = 0
let char_level   = 1
let string_level = 2
let eq_level     = 8


let proposition_start_level = 12
let true_offset    = 0
let false_offset   = 1
let impl_offset    = 2
let exfalso_offset = 3
let leibniz_offset = 4

let true_level     = proposition_start_level + true_offset
let false_level    = proposition_start_level + false_offset
let impl_level     = proposition_start_level + impl_offset
let exfalso_level  = proposition_start_level + exfalso_offset
let leibniz_level  = proposition_start_level + leibniz_offset
let _ =
    true_level
    , false_level
    , impl_level
    , exfalso_level
    , leibniz_level


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
  let open Term
  in
  empty

  |> (* 0 *) add_entry "Int" (Term.any ,0) (Builtin_type "int_type")

  |> (* 1 *) add_entry "Character" (Term.any, 0) (Builtin_type "char_type")

  |> (* 2 *) add_entry "String" (Term.any, 0) (Builtin_type "string_type")

  |> (* 3 *) add_entry
       "+"
       (binary_type int_level)
       (Builtin ("int_plus", Term.Value.int_plus))

  |> (* 4 *) add_entry
       "-"
       (binary_type int_level)
       (Builtin ("int_minus", Term.Value.int_minus))

  |> (* 5 *) add_entry
       "*"
       (binary_type int_level)
       (Builtin ("int_times", Term.Value.int_times))

  |> (* 6 *) add_entry
       "+"
       (binary_type string_level)
       (Builtin ("string_concat", Term.Value.string_concat))

  |> (* 7 *) add_entry
       (* List: Any -> Any *)
       "List"
       (Term.(Pi (any, any, Pi_info.arrow)), 0)
       Axiom

  |> (* 8 *) add_entry (* 8 *)
       (* (=) (A: Any): A -> A -> Proposition *)
       "="
       (Term.(
          Pi (any,
              Pi (Variable 0,
                  (Pi (Variable 1,
                       proposition,
                       Pi_info.arrow)),
                  Pi_info.arrow),
              Pi_info.typed "A")),
        0)
       Axiom

  |> (* 9 *) add_entry
       (* identity: all (A: Any): A -> A :=
            \ A x := x *)
       "identity"
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

    |> (* 10 *) (* (|>) (A: Any) (a: A) (B: Any) (f: A -> B): B := f a *)
        (let biga = Variable 0
         and a    = Variable 1
         and bigb = Variable 2
         and f    = Variable 3
         in
         let args = ["A", any;
                     "a", biga;
                     "B", any;
                     "f", arrow biga bigb]
         in
         let typ = product_in args bigb
         and def = lambda_in args (application f a)
         in
         add_entry
            "|>"
            (to_index 0 typ, 0)
            (Definition (to_index 0 def))
        )

    |> (* 11 *) (* (<|) (A: Any) (B: Any) (f: A -> B) (a: A): B := f a *)
        (let biga = Variable 0
         and bigb = Variable 1
         and f    = Variable 2
         and a    = Variable 3
         in
         let args = ["A", any;
                     "B", any;
                     "f", arrow biga bigb;
                     "a", biga]
         in
         let typ = product_in args bigb
         and def = lambda_in args (application f a)
         in
         add_entry
            "<|"
            (to_index 0 typ, 0)
            (Definition (to_index 0 def))
        )

    |> (* 12 *) add_entry
        (* true: Proposition *)
        "true"
        (Term.proposition, 0)
        Axiom

    |> (* 13 *) add_entry
        (* false: Proposition *)
        "false"
        (Term.proposition, 0)
        Axiom

    |> (* 14 *) (* (=>): all (a b: Proposition): Proposition := a -> b *)
       (let typ =
            product "_"
                proposition
                (product "_" proposition proposition)
        and def =
            let a = Variable 0
            and b = Variable 1 in
            to_index 0
                (lambda "a" proposition
                   (lambda "b" proposition
                        (arrow a b)))
        in
        add_entry
            "=>" (typ,0) (Definition def)
        )

    |> (* 15 *)
       (* ex_falso: all (a: Proposition): false => a *)
    (
        let n =
            proposition_start_level + exfalso_offset
        in
        let typ =
            product
                "a"
                proposition
                (binary
                    (Variable false_level)
                    (Variable impl_level)
                    (Variable n))
        in
        add_entry "ex_falso" (to_index n typ, n) Axiom
    )




     (* 16 *)
     (* leibniz (A: Any) (f: A -> Proposition)
               (a b: A)
               : a = b => f a => f b *)
    |>  (let n = eq_level + 1 in
         let biga = Variable (n + 0)
         and f    = Variable (n + 1)
         and a    = Variable (n + 2)
         and b    = Variable (n + 3)
         and eq   = Variable eq_level
         in
         let args = ["A", any;
                     "f", arrow biga proposition;
                     "a", biga;
                     "b", biga;
                     "eq", binary
                            a
                            (implicit_application eq biga)
                            b;
                     "fa", application f a]
         in
         let typ = product_in args (application f b)
         in
         add_entry
            "leibniz" (to_index n typ, n)
            Axiom
        )



let type_of_literal (v: Term.Value.t) (c: t): Term.typ =
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




let type_of_variable (i: int) (c: t): Term.typ =
  type_at_level (level_of_index i c) c




let definition_term (idx: int) (c: t): Term.t option =
    let level = level_of_index idx c
    in
    match
      (entry level c).definition
    with
    | Definition def ->
       Some (Term.up (count c - level) def)

    | _ ->
       None



let compute (t:Term.t) (c:t): Term.t =
  let open Term in
  let rec compute term steps c =
    match term with
    | Sort _ | Value _ ->
        term, steps

    | Variable i ->
        let level = level_of_index i c in
        (
            match (entry level c).definition with
            | Axiom | Assumption | Builtin_type _ ->
                term, steps

            | Builtin (_, v) ->
               Term.Value v, steps + 1

            | Definition def ->
               Term.up (count c - level) def,
               steps + 1

            | Inductive_type _ | Constructor _ ->
                term, steps
        )

    | Typed (e, _ ) ->
       compute e (steps + 1) c

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

    | Where (_, _, exp, def) ->
        compute (apply exp def) (steps + 1) c
  in
  fst (compute t 0 c)
