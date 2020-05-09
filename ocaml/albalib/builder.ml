open Fmlib
open Common
open Alba_core


module Parser     = Parser_lang
module Expression = Ast.Expression
module Position   = Character_parser.Position


type pos = Position.t

type range = pos * pos

module Located =
  Character_parser.Located



type type_in_context = Build_context.type_in_context


type problem_description =
    | Overflow
    | No_name
    | Incomplete_type of type_in_context
    | Cannot_infer_bound
    | Not_a_function of type_in_context list
    | Wrong_type of (type_in_context * type_in_context) list
    | Wrong_base of type_in_context list * type_in_context list
    | Ambiguous of type_in_context list
    | Name_violation of string * string (* case, kind *)
    | Ambiguous_definition of int
    | Not_yet_implemented of string

let dummy str = Not_yet_implemented str
let _ = dummy




let description_of_type_in_context
    (nargs: int)
    (lst: (type_in_context * type_in_context) list)
    : problem_description
    =
    if 0 < nargs then
        Not_a_function (List.map snd lst)
    else
        Wrong_type lst


type problem = range * problem_description





module Name_map = Name_map
module Result = Monad.Result (struct type t = problem end)
module List_fold = List.Monadic_fold (Result)
module Interval_monadic = Interval.Monadic (Result)
module Algo = Gamma_algo.Make (Gamma)


type t = {
    names: Name_map.t;
    base:  Gamma.t;
    bcs:   Build_context.t list;
}

let count_base (builder: t): int =
    Gamma.count builder.base




let push_bound (name: string) (builder: t): t =
    {builder with
        names = Name_map.add_local name builder.names}


let set_names (names: Name_map.t) (builder: t): (t, problem) result =
    Ok {builder with names}


let make (c: Context.t): t =
    {
        names = Context.name_map c;
        base  = Context.gamma c;
        bcs   = [Build_context.make (Context.gamma c)]
    }





type 'a build_monad =
    t -> ('a, problem) result



let map_bcs_list (f: Build_context.t -> Build_context.t) (builder: t): t =
    {builder with bcs = List.map f builder.bcs}



let map_bcs0
    (f: Build_context.t -> ('a, 'b) result)
    (g: 'b list -> problem)
    : 'a list build_monad
    =
    fun builder ->
    let lst, errors =
        List.fold_left
            (fun (lst, errors)  bc ->
                match f bc with
                | Ok a ->
                    a :: lst, errors
                | Error problem ->
                    lst, problem :: errors)
            ([], [])
            builder.bcs
    in
    if lst <> [] then
        Ok lst
    else
        Error (g errors)





let map_bcs
    (f: Build_context.t -> (Build_context.t, 'a) result)
    (g: 'a list -> problem)
    : t build_monad
    =
    fun builder ->
    Result.map
        (fun bcs -> {builder with bcs})
        (map_bcs0 f g builder)



let next_formal_argument
    (name: string Located.t)
    (typed: bool)
    (builder: t)
    : t
    =
    let str = Located.value name
    in
    map_bcs_list
        (Build_context.next_formal_argument name typed)
        builder
    |> push_bound str



let check_formal_arguments
    (fargs: Expression.formal_argument list)
    : t build_monad
    =
    map_bcs
        (Build_context.Product.check (List.length fargs))
        (fun lst ->
            let i_min =
                List.fold_left
                    (fun i_min i -> min i_min i)
                    (List.length fargs)
                    lst
            in
            let name, _ = List.nth_strict i_min fargs in
            Located.range name, Cannot_infer_bound)


let end_product
    (range: range)
    (nargs_outer: int)
    (nargs_inner: int)
    : t build_monad
    =
    map_bcs
        (Build_context.Product.end_ nargs_outer nargs_inner)
        (fun lst ->
            range,
            description_of_type_in_context nargs_outer lst)



let base_candidates
    (range: range)
    (candidates: Term.t list)
    (nargs: int)
    : t build_monad
    =
    fun builder ->
    let candidates, _ =
        List.fold_right
            (fun term (candidates, variant) ->
                (term, variant) :: candidates,
                variant + 1)
            candidates
            ([], 0)
    in
    let bcs =
        List.(
            builder.bcs >>= fun bc ->
            candidates  >>= fun (term, variant) ->
            Option.to_list
                (Build_context.base_candidate
                    range variant term nargs bc))
    in
    if bcs = [] then
        let acts =
            List.map
                (fun (term, _) ->
                    [],
                    Algo.type_of_term term builder.base,
                    builder.base)
                candidates
        and reqs =
            List.map Build_context.required_type_in_context builder.bcs
        in
        if 0 < nargs then
            Error (range, Not_a_function acts)
        else
            Error (range, Wrong_base (reqs, acts))
    else
        Ok {builder with bcs}



let rec build0
    (exp: Expression.t)
    (nargs: int)
    : t build_monad
    =
    fun builder ->
    let open Expression in
    let range = Located.range exp in
    match
        Located.value exp
    with
    | Number str ->
        let lst = Term.number_values str in
        if lst = [] then
            Error (range, Overflow)
        else
            base_candidates range lst nargs builder

    | Char code ->
        base_candidates range [Term.char code] nargs builder

    | String str ->
        base_candidates range [Term.string str] nargs builder

    | Proposition ->
        base_candidates range [Term.proposition] nargs builder

    | Any ->
        base_candidates range [Term.any] nargs builder

    | Identifier name | Operator (name, _) ->
        let cnt_base = count_base builder in
        (
            match Name_map.find name builder.names with
            | [] ->
                Error (range, No_name)

            | [level] when cnt_base <= level ->
                map_bcs
                    (Build_context.bound (level - cnt_base) nargs)
                    (fun lst ->
                        range,
                        description_of_type_in_context nargs lst)
                    builder

            | lst ->
                base_candidates
                    range
                    (List.map
                        (fun level -> Gamma.variable_at_level level builder.base)
                        lst)
                    nargs
                    builder
        )

    | Typed (exp, tp) ->
        let open Result in
        (map_bcs_list Build_context.Typed.start builder
        |> build0 tp 0)
        >>= fun builder ->
        (map_bcs_list Build_context.Typed.expression builder
        |> build0 exp 0)
        >>=
        map_bcs
            (Build_context.Typed.end_ nargs)
            (fun lst ->
                range,
                description_of_type_in_context nargs lst)

    | Product (fargs, res) ->
        let open Result
        in
        let names = builder.names
        in
        build_signature
            fargs
            (Some res)
            (map_bcs_list Build_context.Product.start builder)
        >>=
        check_formal_arguments fargs
        >>=
        end_product range nargs (List.length fargs)
        >>= set_names names


    | Application (f, args) ->
        let open Result in
        (*  Get a position number for each argument and the total number of
            arguments. *)
        let nargs, args =
            List.fold_right
                (fun (arg, mode) (n,args) -> n + 1, (n,arg,mode) :: args)
                args
                (0, [])
        in
        (* Build the function term. *)
        build0
            f
            nargs
            (map_bcs_list
                (Build_context.Application.start nargs)
                builder)
        >>=
        (* Build the arguments. *)
        List_fold.fold_left
            (fun (n, arg, mode) builder ->
                let mode =
                    match mode with
                    | Ast.Expression.Normal ->
                        Term.Application_info.Normal
                    | Ast.Expression.Operand ->
                        assert (nargs = 1 || nargs = 2);
                        if nargs = 2 then
                            Term.Application_info.Binary
                        else
                            Term.Application_info.Unary
                in
                build0 arg 0 builder
                >>=
                map_bcs
                    (Build_context.Application.apply n mode)
                    (fun lst ->
                        (fst range, Located.end_ arg),
                        description_of_type_in_context n lst)
            )
            args


    | Function (fargs, res, exp) ->
        let open Result in
        let names = builder.names in
        build_signature
            fargs
            res
            (map_bcs_list Build_context.Lambda.start builder)
        >>= fun builder ->
        Ok (map_bcs_list Build_context.Lambda.inner builder)
        >>= fun builder ->
        build0 exp 0 builder
        >>=
        map_bcs
            (Build_context.Lambda.end_
                nargs
                (List.length fargs)
                (res <> None))
            (fun lst ->
                range,
                description_of_type_in_context nargs lst)
        >>= set_names names

    | Where (exp, defs) ->
        let open Result in
        let rec build_where defs builder =
            match defs with
            | [] ->
                build0 exp 0 builder
            | def :: defs ->
                let name, _, _, _ =
                    Located.value def
                in
                let str = Located.value name
                and names = builder.names
                in
                build_where
                    defs
                    (map_bcs_list
                        (Build_context.Where.start name)
                        builder
                    |> push_bound str)
                >>=
                map_bcs
                    Build_context.Where.end_inner
                    (fun lst -> range, description_of_type_in_context 1 lst)
                >>= set_names names
                >>=
                build_definition0 def
                >>=
                map_bcs
                    (Build_context.Where.end_ nargs)
                    (fun lst -> range, description_of_type_in_context 0 lst)

        in
        build_where defs builder

    | List _ ->
        Error (range, Not_yet_implemented "Literal list")


and build_formal_argument
    ((name, tp): Expression.formal_argument)
    : t build_monad
    =
    fun builder ->
    let next typed builder = next_formal_argument name typed builder
    in
    match tp with
    | None ->
        Ok (next false builder)
    | Some tp ->
        Result.map (next true) (build0 tp 0 builder)


and build_signature
    (fargs: Expression.formal_argument list)
    (res: Expression.t option)
    : t build_monad
    =
    fun builder ->
    let open Result in
    List_fold.fold_left
        build_formal_argument
        fargs
        builder
    >>= fun builder ->
    match res with
    | None ->
        Ok builder
    | Some res ->
        build0 res 0 builder


and build_definition0
    (def: Expression.definition)
    : t build_monad
=
    let open Expression
    in
    let name, fargs, res_tp, def_exp =
        Located.value def
    in
    if fargs = [] && res_tp = None then
        build0 def_exp 0
    else if fargs = [] then
        build0
            Located.(make
                (start name)
                (Typed (def_exp, Option.value res_tp))
                (end_ name))
        0
    else
        build0
            Located.(make
                (start name)
                (Function (fargs, res_tp, def_exp))
                (end_ name))
            0






let check_ambiguity
    (c: Context.t)
    (builder: t)
    : (Build_context.t, problem) result
    =
    match builder.bcs with
    | [] ->
        assert false (* Cannot happen! *)
    | _ :: _ :: _ ->
        let range, base_terms =
            Build_context.find_last_ambiguous builder.bcs
        in
        Error (
            range,
            Ambiguous (
                List.map
                    (fun (_, typ) ->
                        [], typ, Context.gamma c)
                    base_terms
            )
        )
    | [bc] ->
        Ok bc



let check_formal_arguments
    (bc: Build_context.t)
    : (Build_context.t, problem) result
    =
    match Build_context.find_first_untyped_formal bc with
    | None ->
        Ok bc

    | Some range ->
        Error (range, Cannot_infer_bound)


let check_name_violations
    (bc: Build_context.t)
    : (Build_context.t, problem) result
    =
    match Build_context.find_first_name_violation bc with
    | None ->
        Ok bc

    | Some (range, case, kind) ->
        Error (range, Name_violation (case, kind))



let check_incomplete
    (range: range)
    (bc: Build_context.t)
    : (Term.t * Term.typ, problem) result
    =
    match Build_context.final bc with
    | Error err ->
        Error (range, Incomplete_type err)

    | Ok (_, term, typ) ->
        Ok (term, typ)



let build
      (exp: Ast.Expression.t)
      (c: Context.t)
    : (Term.t * Term.typ, problem) result
    =
    let open Result in
    build0 exp 0 (make c)
    >>=
    check_ambiguity c
    >>=
    check_formal_arguments
    >>=
    check_name_violations
    >>=
    check_incomplete (Located.range exp)



let build_definition
    (def: Ast.Expression.definition)
    (c: Context.t)
    : (Term.t * Term.typ, problem) result
=
    let open Fmlib.Result in
    build_definition0 def (make c)
    >>=
    check_ambiguity c
    >>=
    check_formal_arguments
    >>=
    check_name_violations
    >>=
    check_incomplete (Located.range def)



let add_definition
    (def: Ast.Expression.definition)
    (context: Context.t)
    : (Context.t, problem) result
=
    let open Fmlib.Result in
    let name, _, _, _ = Located.value def
    in
    build_definition def context
    >>=
    (   fun (term, typ) ->
        match
            Algo.check_naming_convention
                (Located.value name)
                typ
                (Context.gamma context)
        with
        | Ok () ->
            Ok (term, typ)
        | Error violation ->
            let case, kind = Gamma_algo.strings_of_violation violation
            in
            Error (Located.range name, Name_violation (case, kind))
    )
    >>= fun (term, typ) ->
    match
        Context.add_definition
            (Located.value name)
            typ
            term
            context
    with
    | Error duplicate ->
        Error (Located.range name, Ambiguous_definition duplicate)

    | Ok context ->
        Ok context








(* ----------------------------------------------------------------------- *)
(* Printing of Problems *)
(* ----------------------------------------------------------------------- *)

module Print (P: Pretty_printer.SIG) =
struct
    module PP = Term_printer.Pretty (Gamma) (P)


    let type_or_types (l: 'a list): P.t =
        match l with
        | [_] ->
            P.wrap_words "the type"
        | _ :: _ :: _ ->
            P.wrap_words "one of the types"
        | _ ->
            assert false (* Illegal call! *)

    let typ (holes: int list) (tp: Term.typ) (gamma: Gamma.t): P.t =
        let tp = PP.print tp gamma in
        let open P in
        match holes with
        | [] ->
            tp
        | _ ->
            let holes =
                char '['
                <+>
                list_separated
                    (char ',' <+> group space)
                    (List.map
                        (fun level ->
                            let v = Gamma.variable_at_level level gamma
                            and vtp = Gamma.type_at_level level gamma in
                            PP.print v gamma <+> char ':' <+> char ' '
                            <+> PP.print vtp gamma)
                        holes)
                <+> char ']'
            in
            tp
            <+>
            nest 4 (
                cut
                <+> string "unknown: "
                <+> holes)

    let type_list (lst: type_in_context list): P.t =
        let open P in
        nest 4
            (list_separated
                cut
                (List.map
                    (fun (holes, tp, gamma) ->
                        (typ holes tp gamma))
                    lst))

    let wrong_type
        (reqs: type_in_context list)
        (acts: type_in_context list)
        : P.t
        =
        let open P in
        wrap_words "I was expecting a term which has"
        <+> group space
        <+> type_or_types reqs
        <+> cut <+> cut
        <+> type_list reqs
        <+> cut <+> cut
        <+> wrap_words "and the highlighted term has"
        <+> group space
        <+> type_or_types acts
        <+> cut <+> cut
        <+> type_list acts
        <+> cut <+> cut



    let description (descr: problem_description): P.t =
        let open P in
        match descr with
        | Overflow ->
            wrap_words "The number does not fit into a machine word" <+> cut
        | No_name ->
            string "I cannot find this name or operator" <+> cut
        | Cannot_infer_bound ->
            wrap_words "I cannot infer a type for this variable" <+> cut
        | Incomplete_type tp  ->
            wrap_words "I cannot infer a complete type of the expression. \
                        Only the incomplete type"
            <+> cut <+> cut
            <+> type_list [tp]
            <+> cut <+> cut
            <+> wrap_words "This usually happens if I cannot infer the types \
                            of some bound variables."
            <+> cut

        | Not_a_function lst ->
            assert (lst <> []);
            wrap_words "I was expecting a function which can be applied to \
                        arguments. But the expression has"
            <+> group space
            <+> type_or_types lst
            <+> cut <+> cut
            <+> type_list lst
            <+> cut <+> cut
            <+> wrap_words "which is not a function type." <+> cut

        | Wrong_type lst ->
            assert (lst <> []);
            let reqs, acts = List.split lst in
            wrong_type reqs acts

        | Wrong_base (reqs, acts) ->
            wrong_type reqs acts

        | Ambiguous types ->
            wrap_words
                "This term is ambigous. It can have the following types."
            <+> cut <+> cut
            <+> type_list types
            <+> cut <+> cut
            <+> wrap_words
                "Please give me more type information to infer a unique type."
            <+> cut

        | Name_violation (case, kind) ->
            if case = "Upper" then
                wrap_words
                    "This identifier must not start with an upper case letter. \
                    Identifiers starting with upper case letters are allowed \
                    only for types and type constructors. \
                    The highlighted identifier is a"
                <+> group space
                <+> string kind
                <+> cut
            else
                wrap_words
                    "This identifier must not start with a lower case letter. \
                    Identifiers starting with lower case letters are allowed \
                    only for object variables, proofs and propositions. \
                    But the highlighted identifier is a"
                <+> group space
                <+> string kind
                <+> cut

        | Ambiguous_definition _ ->
            wrap_words
                "There is already a definition with the same name and \
                the same signature. Remember that there can be multiple \
                definitions with the same name only if they have \
                different signatures."
                <+> cut


        | Not_yet_implemented str ->
            char '<' <+> string str <+> char '>'
            <+> group space
            <+> wrap_words "is not yet implemented"


    let print_with_source
        (src: string) ((range, desc): problem)
        : P.t
        =
        let module P0 = Printer.Make (P) in
        let open P in
        P0.print_error_header "TYPE"
        <+>
        P0.print_source src range []
        <+>
        description desc
        <+> cut


    let print_with_source_lines
        (lines: string Segmented_array.t)
        ((range, desc): problem)
        : P.t
        =
        let module P0 = Printer.Make (P) in
        let open P in
        P0.print_error_header "TYPE"
        <+>
        P0.print_source_lines lines range []
        <+>
        description desc
        <+> cut
end
