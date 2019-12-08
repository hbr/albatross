open Fmlib
open Common


type name =
  | Normal of string
  | Binary_operator of string * Operator.t


type definition =
  | No
  | Builtin of Term.Value.t


type entry = {
    name: name;
    typ: Term.typ;
    definition: definition
  }


type t = {
    gamma: entry Segmented_array.t;
    substitutions: (Term.t * int) option array
  }


let bruijn_convert (i:int) (n:int): int =
  n - i - 1



let count (c:t): int =
  Segmented_array.length c.gamma



let is_valid_index (i:int) (c:t): bool =
  0 <= i && i < count c


let index_of_level (i:int) (c:t): int =
  bruijn_convert i (count c)


let level_of_index (i:int) (c:t): int =
  bruijn_convert i (count c)


let entry (i:int) (c:t): entry =
  assert (is_valid_index i c);
  Segmented_array.elem i c.gamma


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
  {gamma = Segmented_array.empty;
   substitutions = [||]}


let push (name:name) (typ:Term.typ) (definition:definition) (c:t): t =
  {c with
    gamma =
      Segmented_array.push
        {name; typ; definition}
        c.gamma}


let push_local (nme:string) (typ: Term.typ) (c:t): t =
  push (Normal nme) typ No c


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
  let open Term in
  Pi ("_",
      Variable 0,
      Pi ("_",
          Variable 1,
          Variable 2)),
  (level + 1)


let int_type (c:t) =
  Term.Variable (index_of_level int_level c)


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


module Pretty (P:Pretty_printer.SIG) =
  (* Operator printing:

         Appl (Appl (+ , a), b)   -> a + b  or  (+) a b

         Appl (f, a)              -> f a
   *)
  struct
    type pr_result =
      Operator.t option * P.t


    let rec pi_args
              (t:Term.t)
              (c:t)
            : (string * Term.typ * t) list * Term.t * t =
      match t with
      | Pi (nme, tp, t) ->
         let lst, t_inner, c_inner =
           pi_args t (push_local nme tp c)
         in
         (nme, tp, c) :: lst, t_inner, c_inner
      | _ ->
         [], t, c


    let print_sort: Term.Sort.t -> pr_result = function
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


    let rec print (t:Term.t) (c:t): pr_result =
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

      | Appl ( Appl (op, a, Binary), b, _ ) ->
         let a_data, a_pr = print a c
         and b_data, b_pr = print b c
         and op_str, op_data =
           operator_data op c
         in
         let a_pr =
           parenthesize a_pr a_data true op_data
         and b_pr =
           parenthesize b_pr b_data false op_data
         in
         Some op_data,
         P.(chain [a_pr;
                   char ' ';
                   string op_str;
                   char ' ';
                   b_pr])

      | Appl (op, a, Binary) ->
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
         assert false

      | Pi (nme, tp, t) ->
         let lst, t_inner, c_inner = pi_args t (push_local nme tp c)
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



let type_of_term (t:Term.t) (c:t): Term.typ =
  let rec typ t c =
    let open Term in
    match t with
    | Sort (Sort.Any i) ->
       Sort (Sort.Any (i+1))

    | Value v ->
       (match v with
        | Value.Int _ ->
           Variable (index_of_level int_level c)

        | Value.Char _ ->
           Variable (index_of_level char_level c)

        | Value.String _ ->
         Variable (index_of_level string_level c)

        | Value.Unary _ | Value.Binary _ ->
           assert false (* Illegal call! *)
       )
    | Variable i ->
       type_at_level (level_of_index i c) c

    | Appl (f, a, _) ->
       (match typ f c with
        | Pi (_, _, t) ->
           apply t a
        | _ ->
           assert false (* Illegal call! Term is not welltyped. *)
       )

    | Pi (name, tp, t) ->
       (match
          typ tp c, typ t (push_local name tp c)
        with
        | Sort (Sort.Any i), Sort (Sort.Any j) ->
           Sort (Sort.Any (max i j))
        | _ ->
           assert false (* nyi other product combinations. *)
       )
  in
  typ t c



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
     )
  | Appl (f, a, mode) ->
     let a, f = compute a c, compute f c in
     (match f, a with
      | Value vf, Value va ->
         Value (Value.apply vf va)
      | _ ->
         Appl (f, a, mode))

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
    | Pi (name, tp, t) ->
       push_arguments
         (nargs - 1)
         t
         (push_local name tp c)

    | _ ->
       None
