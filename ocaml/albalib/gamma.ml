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


let transfer (c0:t) (c1:t) (t:Term.t): Term.t =
  let cnt0,cnt1 = count c0, count c1 in
  assert (cnt0 <= cnt1);
  Term.up (cnt1 - cnt0) t


let string_of_name (name:name): string =
  match name with
  | Normal str | Binary_operator (str, _) ->
     str


let name_of_level (i:int) (c:t): name =
  (entry i c).name


let name_of_index (i:int) (c:t): name =
  (entry (bruijn_convert i (count c)) c).name


let operator_data
      (t:Term.t) (c:t)
    : string * Operator.t
  =
  match t with
  | Term.Variable index ->
     (match name_of_index index c with
      | Binary_operator (str, data) ->
         str, data

      | Normal str ->
         Printf.printf "operator data <%s>\n" str;
         assert false (* Illegal call! *)
     )

  | _ ->
     assert false (* Illegal call! *)



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
                             Lambda_info.untyped "x"),
                     Lambda_info.untyped "A"))))


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


let type_of_term (t:Term.t) (c:t): Term.typ =
  let rec typ t c =
    let open Term in
    match t with
    | Sort s ->
        type_of_sort s

    | Value v ->
        type_of_value v c

    | Variable i ->
       type_at_level (level_of_index i c) c


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



let rec compute (t:Term.t) (c:t): Term.t =
  let open Term in
  match t with
  | Sort _ ->
     t

  | Value _ ->
     t

  | Variable i ->
     (match (entry (level_of_index i c) c).definition with
      | No ->
         t

      | Builtin v ->
         Term.Value v

      | Definition def ->
         def
     )

  | Typed (e, _ ) ->
     compute e c

  | Appl (Lambda (_, exp, _ ), a, _) ->
     compute (Term.apply exp a) c

  | Appl (f, a, mode) ->
     let a, f = compute a c, compute f c in
     (match f, a with
      | Value vf, Value va ->
         Value (Value.apply vf va)
      | _ ->
         Appl (f, a, mode))

  | Lambda _ ->
     t

  | Pi _ ->
     t


let rec push_arguments
          (nargs:int)
          (tp:Term.typ)
          (c:t)
        : (t * Term.typ) option =
  assert (0 <= nargs);
  if nargs = 0 then
    Some (c, tp)

  else
    match tp with
    | Pi (tp, rt, info) ->
       let name = Term.Pi_info.name info in
       push_arguments
         (nargs - 1)
         rt
         (push_local name tp c)

    | _ ->
       None



let key_split
      (c: t)
      (t: Term.t)
      (args: (Term.t * Term.appl) list)
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

    | _ ->
       t, args
  in
  split t args


let key_normal (c: t) (t: Term.t): Term.t =
  let key, args = key_split c t [] in
  List.fold_left
    (fun res (arg, mode) ->
      Term.Appl (res, arg, mode))
    key
    args




let add_vars_from (level: int) (t: Term.t) (c: t) (set: Int_set.t): Int_set.t =
  Term.fold_free_variables
    set
    (fun i set ->
      let j = level_of_index i c in
      if i < level then
        set
      else
        Int_set.add j set)
    t



let signature (c: t) (tp: Term.typ): Signature.t =
  let rec split c tp lst =
    match key_normal c tp with
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














(* ---------------------------------------

   Pretty Printing

   ---------------------------------------
 *)
module Pretty (P:Pretty_printer.SIG) =
  (* Operator printing:

         Appl (Appl (+ , a), b)   -> a + b  or  (+) a b

         Appl (f, a)              -> f a
   *)
  struct
    type pr_result =
      Operator.t option * P.t

    type print0 = Term.t -> t -> P.t

    type print  = Term.t -> t -> pr_result

    let rec split_lambda
              (t: Term.t)
              (c: t)
            : (Lambda_info.t * Term.typ * t) list * Term.t * t =
      match t with
      | Lambda (tp, exp, info) ->
         let lst, exp_inner, c_inner =
           split_lambda exp (push_local (Lambda_info.name info) tp c)
         in
         (info, tp, c) :: lst, exp_inner, c_inner
      | _ ->
         [], t, c


    let rec split_pi
              (t:Term.t)
              (c:t)
            : (string * Term.typ * t) list * Term.t * t =
      match t with
      | Pi (tp, t, info) when not (Pi_info.is_arrow info) ->
         let lst, t_inner, c_inner =
           split_pi t (push_local (Pi_info.name info) tp c)
         in
         (Pi_info.name info, tp, c) :: lst, t_inner, c_inner
      | _ ->
         [], t, c


    let print_sort: Term.Sort.t -> pr_result = function
      | Proposition ->
         None, P.string "Proposition"

      | Any i ->
         let str =
           if i = 0 then
             "Any"
           else
             "Any(" ^ string_of_int i ^ ")"
         in
         None,
         P.string str


    let print_value: Term.Value.t -> pr_result = function
      | Term.Value.Int i ->
         None,
         P.string (string_of_int i)

      | Term.Value.Char i ->
         None,
         P.(char '\'' <+> char (Char.chr i) <+> char '\'')

      | Term.Value.String str ->
         None,
         P.(char '"' <+> string str <+> char '"')

      | Term.Value.Unary _ | Term.Value.Binary _ ->
         None,
         P.(string "<function>")


    let parenthesize
          (pr:P.t)
          (lower: Operator.t option)
          (is_left: bool)
          (upper: Operator.t)
        : P.t
      =
      if Operator.needs_parens lower is_left upper then
        P.(chain [char '('; pr; char ')'])

      else
        pr


    let two_operands
          (a: Term.t) (b:Term.t) (upper: Operator.t)
          (print: print)
          (c:t)
        : P.t * P.t =
      let a_data, a_pr = print a c
      and b_data, b_pr = print b c in
      parenthesize a_pr a_data true upper,
      parenthesize b_pr b_data false upper



    let formal_arguments
          (args: ('a * Term.typ * t) list)
          (map: 'a -> string * bool)
          (print: print0)
        : P.t =
      let open P in
      let args =
        List.map
          (fun (a, tp, c) ->
            let name, typed = map a in
            if typed then
              char '('
              <+> string name
              <+> string ": "
              <+> print tp c
              <+> char ')'
            else
              string name)
          args
      in
      chain_separated args (group space)


    let rec print (t:Term.t) (c:t): pr_result =
      let raw_print t c =
        snd (print t c)
      in
      let print_name_type name tp c =
        P.(char '('
           <+> (if name = "" then char '_' else string name)
           <+> char ':'
           <+> snd (print tp c)
           <+> char ')')
      in
      match t with
      | Sort s ->
         print_sort s

      | Variable i ->
         None,
         P.string
           (if is_valid_index i c then
              match name_of_index i c with
              | Normal str ->
                 str

              | Binary_operator (str, _) ->
                 "(" ^ str ^ ")"
            else
              "<invalid>")

      | Typed (e, tp) ->
         let e_pr, tp_pr = two_operands e tp Operator.colon print c in
         Some Operator.colon,
         P.(group (chain [e_pr; char ':'; space; tp_pr]))

      | Appl ( Appl (op, a, Binary), b, _ ) ->
         (* a op b *)
         let op_str, op_data = operator_data op c in
         let a_pr, b_pr = two_operands a b op_data print c
         in
         Some op_data,
         P.(chain [a_pr;
                   group space;
                   string op_str;
                   char ' ';
                   b_pr])

      | Appl (op, a, Binary) ->
         (* (a op) ???? Postfix operator? *)
         let a_data, a_pr = print a c
         and op_str, op_data =
           operator_data op c
         in
         let a_pr =
           parenthesize a_pr a_data true op_data
         in
         None,
         P.(char '('
            <+> a_pr
            <+> char ' '
            <+> string op_str
            <+> char ')')

      | Appl (_, _, _) ->
         assert false  (* nyi *)

      | Lambda (tp, exp, info) ->
         let arg_lst, exp_inner, c_inner =
           split_lambda exp (push_local (Lambda_info.name info) tp c)
         in
         let args =
           formal_arguments
             ((info, tp, c) :: arg_lst)
             Lambda_info.(fun info -> name info, is_typed info)
             raw_print
         and exp_inner = raw_print exp_inner c_inner
         in
         Some Operator.lambda,
         P.(string "\\ "
            <+> args
            <+> string " := "
            <+> exp_inner)

      | Pi (tp, rt, info) when Pi_info.is_arrow info ->
         let c_inner = push_local "_" tp c in
         let tp_data, tp_pr = print tp c
         and rt_data, rt_pr = print rt c_inner
         and op_data = Operator.of_string "->"
         in
         let tp_pr =
           parenthesize tp_pr tp_data true op_data
         and rt_pr =
           parenthesize rt_pr rt_data false op_data
         in
         Some op_data,
         P.(chain [tp_pr;
                   group space;
                   string "->";
                   char ' ';
                   rt_pr])

      | Pi (tp, t, info) ->
         let nme = Term.Pi_info.name info in
         let lst, t_inner, c_inner =
           split_pi t (push_local nme tp c)
         in
         None,
         P.(chain [List.fold_left
                     (fun pr (nme,tp,c) ->
                       pr
                       <+> char ' '
                       <+> print_name_type nme tp c
                     )
                     (string "all "
                      <+> print_name_type nme tp c)
                     lst;
                   string ": ";
                   snd @@ print t_inner c_inner])

      | Value v ->
         print_value v

    let print (t:Term.t) (c:t): P.t =
      snd (print t c)
  end (* Pretty *)




let string_of_term (t:Term.t) (c:t): string =
  let module PP = Pretty_printer.Pretty (String_printer) in
  let module P = Pretty (PP) in
  String_printer.run
    (PP.run 0 80 80 (P.print t c))
