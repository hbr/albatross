open Fmlib
open Common

open Term


module type GAMMA =
sig
 type t
  val is_valid_index: int -> t -> bool
  val name_of_index: int -> t -> string
  val push_local: string -> Term.typ -> t -> t
end



module Pretty (Gamma: GAMMA) (P: Pretty_printer.SIG) =
  struct
    open Gamma

    type pr_result =
      Operator.t option * P.t

    type print0 = Term.t -> Gamma.t -> P.t

    type print  = Term.t -> Gamma.t -> pr_result


    let split_application (term: Term.t): Term.t * Term.t list =
      let rec split term arg_lst =
        match term with
        | Appl (f, arg, _ ) ->
            split f (arg :: arg_lst)
        | _ ->
            term, arg_lst
      in
      split term []

    let rec split_lambda
              (t: Term.t)
              (c: Gamma.t)
            : (Lambda_info.t * Term.typ * Gamma.t) list * Term.t * t =
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
          ((lower,pr): Operator.t option * P.t)
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
      parenthesize (print a c) true upper,
      parenthesize (print b c) false upper



    let formal_arguments
          (args: ('a * Term.typ * Gamma.t) list)
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


    let rec print (t:Term.t) (c:Gamma.t): pr_result =
      let raw_print t c =
        snd (print t c)
      in
      let print_name_type name tp c =
        P.(char '('
           <+> (if name = "" then char '_' else string name)
           <+> string ": "
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
              let name = name_of_index i c in
              assert (0 < String.length name);
              let c0 = name.[0] in
              if Char.is_letter c0 || c0 = '_' then
                name
              else
                "(" ^ name ^ ")"
            else
              "<invalid>")

      | Typed (e, tp) ->
         let e_pr, tp_pr = two_operands e tp Operator.colon print c in
         Some Operator.colon,
         P.(group (chain [e_pr; char ':'; space; tp_pr]))

      | Appl ( Appl (op, a, Binary), b, _ ) ->
         (* a op b *)
          let op_string =
            let op,_ = split_application op in
            match op with
            | Variable i when is_valid_index i c ->
                name_of_index i c
            | _ ->
              "<invalid operator>"
          in
          let op_data = Operator.of_string op_string
          in
          let a_pr, b_pr = two_operands a b op_data print c
          in
          Some op_data,
          P.(chain [a_pr;
                    group space;
                    string op_string;
                    char ' ';
                    b_pr])

      | Appl (f, _, Implicit) ->
          print f c

      | Appl (f, a, _) ->
          Some Operator.application,
          P.( parenthesize (print f c) true Operator.application
              <+> char ' '
              <+> parenthesize (print a c) false Operator.application )

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
         let c_inner = push_local "_" tp c
         and op_data = Operator.of_string "->"
         in
         let tp_pr =
           parenthesize (print tp c) true op_data
         and rt_pr =
           parenthesize (print rt c_inner) false op_data
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

    let print (t:Term.t) (c: Gamma.t): P.t =
      snd (print t c)
  end (* Pretty *)


module String_print (Gamma:GAMMA) =
  struct
    let string_of_term (t:Term.t) (c: Gamma.t): string =
      let module PP = Pretty_printer.Pretty (String_printer) in
      let module P = Pretty (Gamma) (PP) in
      String_printer.run
        (PP.run 0 80 80 (P.print t c))
      end

let string_of_term (t:Term.t) (c: Gamma.t): string =
  let module SP = String_print (Gamma) in
  SP.string_of_term t c
