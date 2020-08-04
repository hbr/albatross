open Fmlib
open Common


type name_violation =
    | Upper_for_proposition
    | Lower_for_type
    | Upper_for_object


let strings_of_violation
    : name_violation -> string * string
=
    function
    | Upper_for_proposition ->
        "Upper", "proposition"
    | Lower_for_type ->
        "Lower", "type or type constructor"
    | Upper_for_object ->
        "Upper", "object or function"




module type GAMMA =
sig
    type t

    val count: t -> int
    val is_valid_index: int -> t -> bool
    val name_of_index: int -> t -> string
    val push_local: string -> Term.typ -> t -> t
    val type_of_literal:    Value.t -> t -> Term.typ
    val type_of_variable: int -> t -> Term.typ
    val definition_term: int -> t -> Term.t option
end







module Signature =
struct
    type t = {
        typ: Term.typ;      (* Result type *)
        typ_n: Term.typ;    (* Result type normalized *)
        is_sort: bool;
        args: (
            Term.typ         (* Original type *)
            * Term.typ       (* Argument type type *)
            * Term.Pi_info.t
        ) array;
    }


    let is_sort typ =
        match typ with
        | Term.Sort _ ->
            true
        | _ ->
            false


    let make (typ:Term.typ) (typ_n: Term.typ): t =
        {
            typ;
            typ_n;
            is_sort = is_sort typ_n;
            args = [||];
        }

    let has_arguments (sign: t): bool =
        Array.length sign.args > 0


    let push
            (arg: Term.typ)
            (typ: Term.typ) (typ_n: Term.typ)
            (info: Term.Pi_info.t)
            (sign: t)
        : t
        =
        {
            typ;
            typ_n;
            is_sort = is_sort typ_n;
            args =
                Array.push
                    (sign.typ, arg, info)
                    sign.args;
        }


    let typ (sign: t): Term.typ =
        if Array.length sign.args = 0 then
            sign.typ
        else
            let typ, _, _ = sign.args.(0) in
            typ


    let argument_type (sign: t): Term.typ =
        assert (has_arguments sign);
        let _, arg_typ, _ = sign.args.(0) in
        arg_typ


    let normal (sign: t): Term.typ =
        sign.typ_n


    let is_sort (nargs: int) (sign: t): bool =
        nargs = Array.length sign.args
        &&
        sign.is_sort
end







module Make (Gamma: GAMMA) =
struct
    include Gamma

    module String_print = Term_printer.String_print (Gamma)
    let string_of_term (t: Term.t) (c: t): string =
        String_print.string_of_term t c
    let _ = string_of_term


    let key_split
          (t: Term.t)
          (c: t)
        : Term.t * (Term.t * Term.Application_info.t) list
      =
      let rec split t args =
        let open Term in
        match t with
        | Variable i ->
           (match definition_term i c with
            | None ->
               t, args
            | Some def ->
               split def args)

        | Lambda (_, exp, _) ->
            (
                match args with
                | [] ->
                    t, args

                | (arg, _) :: args ->
                    split Term.(apply exp arg) args
            )

        | Appl (f, arg, mode) ->
           split f ((arg, mode) :: args)

        | Typed (term, _) ->
            split term args

        | Where (_, _, exp, def) ->
            split (apply exp def) args

        | _ ->
           t, args
      in
      split t []




    let key_normal (t: Term.t) (c: t): Term.t =
        let key, args = key_split t c in
        List.fold_left
            (fun res (arg, mode) ->
              Term.Appl (res, arg, mode))
            key
            args


    let rec normalize_pi (typ: Term.typ) (c: t): Term.typ =
        let open Term in
        match key_normal typ c with
        | Pi (tp, res, info) ->
            Pi (
                tp,
                normalize_pi
                    res
                    (push_local (Pi_info.name info) tp c),
                info
            )
        | typ ->
            typ



    let rec normalize (term: Term.t) (c: t): Term.t =
        let normalize_key key c =
            let open Term in
            match key with
            | Lambda (tp, exp, info) ->
                Lambda (
                    normalize tp c,
                    normalize exp (push_local (Lambda_info.name info) tp c),
                    info
                )

            | Pi (tp, res, info) ->
                Pi (
                    normalize tp c,
                    normalize res
                        (push_local (Pi_info.name info) tp c),
                    info
                )

            | _ ->
                key
        in
        let key, args = key_split term c in
        List.fold_left
            (fun res (arg, mode) ->
                Term.Appl (res, normalize arg c, mode))
            (normalize_key key c)
            args



    let type_of_term (t: Term.t) (c: t): Term.typ =
        let rec typ t c =
            let open Term in
            match t with
            | Sort s ->
                type_of_sort s

            | Value v ->
                type_of_literal v c

            | Variable i ->
                type_of_variable i c

            | Typed (_, tp) ->
               tp

            | Appl (f, a, _) ->
               (match key_normal (typ f c) c with
                | Pi (_, rt, _) ->
                   apply rt a
                | _ ->
                   assert false (* Illegal call! Term is not welltyped. *)
               )

            | Lambda (tp, exp, info) ->
                let c_inner = push_local (Lambda_info.name info) tp c in
                let rt      = typ exp c_inner
                in
                let info =
                    if has_variable 0 rt then
                        Pi_info.typed (Lambda_info.name info)
                    else
                        Pi_info.arrow
                in
                Pi (tp, rt, info)

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

            | Where (name, tp, exp, def) ->
                typ (expand_where name tp exp def) c
        in
        typ t c



    let split_type
        (typ: Term.typ)
        (c: t)
        : (Term.Pi_info.t * Term.typ) list * Term.typ
    =
        let rec split args typ c =
            let open Term in
            match key_normal typ c with
            | Pi (arg, res, info) ->
                split
                    ((info, arg) :: args)
                    res
                    (push_local (Pi_info.name info) arg c)

            | typ ->
                List.rev args, typ
        in
        split [] typ c



    let split_kind
        (k: Term.typ)
        (c: t)
        : ((Term.Pi_info.t * Term.typ) list * Sort.t) option
    =
        let args, res = split_type k c in
        let open Term in
        match res with
        | Sort s ->
            Some (args, s)
        | _ ->
            None



    let sort_of_kind (k: Term.typ) (c:t): Sort.t option =
        Option.map
            snd
            (split_kind k c)


    let is_kind (k: Term.typ) (c: t): bool =
        Option.has (sort_of_kind k c)



    let check_naming_convention
        (name: string)
        (typ: Term.typ)
        (c: t)
        : (unit, name_violation) result
    =
        (* [check_naming_convention name sort]. Check, if [name] satisfies the
        naming convention for a type of sort [sort]. If yes, return [Ok ()]. If
        not return the name violation. *)
        let is_lower, is_upper =
            if String.length name > 0 then
                let c = name.[0] in
                Char.is_lower c, Char.is_upper c
            else
                false, false
        in
        match sort_of_kind typ c with
        | Some (Sort.Any _) ->
            (* Must be upper case *)
            if is_lower then
                Error  Lower_for_type
            else
                Ok ()

        | Some Sort.Proposition ->
            (* Must be lower case *)
            if is_upper then
                Error Upper_for_proposition
            else
                Ok ()
        | None ->
            (* proof or object, must be lower case *)
            if is_upper then
                Error Upper_for_object
            else
                Ok ()


    let signature (typ: Term.typ) (c: t): Signature.t =
        let typ_n = key_normal typ c in
        let sign = Signature.make typ typ_n in
        let rec make sign c =
            match Signature.normal sign with
            | Pi (arg, res, info ) ->
                let c1 = push_local (Term.Pi_info.name info) arg c in
                let res_n = key_normal res c1 in
                make (Signature.push arg res res_n info sign) c1
            | _ ->
                sign
        in
        make sign c
end
