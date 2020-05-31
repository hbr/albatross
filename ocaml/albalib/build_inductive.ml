open Fmlib
open Common

open Alba_core
open Ast



module Result =
    Fmlib.Result.Make (Build_problem)

module Interval_monadic =
    Interval.Monadic (Result)

module List_monadic =
    List.Monadic (Result)

module Algo =
    Gamma_algo.Make (Gamma)


type 'a result2 = ('a, Build_problem.t) result

type params_located = (string Located.t * Term.typ) array




let (>>=) = Result.(>>=)



let build_type_or_any
    (name: string Located.t)
    (typ: Expression.t option)
    (c: Context.t)
    : Term.typ result2
=
    match typ with
    | None ->
        Ok Term.any
    | Some typ ->
        Build_expression.build_named_type name typ c






let check_params
    (params0: Inductive.params)
    (name: string Located.t)
    (params: params_located)
    (context: Context.t)
    : unit result2
=
    (* [params0] are the paramters of the first type in the family.

        Check that a subsequent type [name,params] has the same set of
        parameters, i.e. same number, same names and same types.
    *)
    let nparams = Array.length params0 in
    if nparams <> Array.length params then
        Error (
            Located.range name,
            Build_problem.Wrong_parameter_count nparams
        )
    else
        Interval_monadic.(
            fold
                (fun i context ->
                    let name,  typ  = params.(i)
                    and name0, typ0 = params0.(i)
                    in
                    if Located.value name <> name0 then
                        Error (
                            Located.range name,
                            Build_problem.Wrong_parameter_name name0
                        )

                    else if Typecheck.equivalent
                        typ0
                        typ
                        (Context.gamma context)
                    then
                        Ok (
                            Context.push_local
                                (Located.value name)
                                typ
                                context
                        )

                    else
                        Error (
                            Located.range name
                            ,
                            Build_problem.Wrong_parameter_type (
                                typ0, Context.gamma context
                            )
                        )
                )
                0 nparams
                context
        )
        >>= fun _ ->
        Ok ()





let class_header
    (i: int)
    (inds: Source_entry.inductive array)
    (c0: Context.t)
    : (string Located.t * params_located * Inductive.Header.t) result2
=
    (* Analyze the [i]ith class header of the inductive family [inds].

         class Name (P0: PT0) (P1: PT1) ... : TP

    *)
    assert (i < Array.length inds);
    let (name, (params, kind_exp)), _ = inds.(i) in
    List_monadic.(
        fold_left
            (fun (name, param_typ) (lst,c1) ->
                build_type_or_any name param_typ c1
                >>=
                fun param_typ ->
                Ok (
                    (name, param_typ) :: lst,
                    Context.push_local
                        (Located.value name)
                        param_typ
                        c1
                )
            )
            params
            ([],c0)
    )
    >>= fun (params, c1) ->
    build_type_or_any name kind_exp c1
    >>= fun kind ->
    match
        Algo.split_kind kind (Context.gamma c1)
    with
    | None ->
        assert (kind_exp <> None);
        let range =
            Located.range (Option.value kind_exp)
        in
        Error (range, Build_problem.No_inductive_type)
    | Some (args, sort) ->
        let name_str = Located.value name
        in
        let params = Array.of_list (List.rev params)
        and header =
            Inductive.Header.make name_str kind args sort
        in
        let params1 =
            Array.map (fun (name,typ) -> Located.value name, typ) params
        in
        if
            Context.can_add_global
                name_str
                (Inductive.Header.kind params1 header)
                c0
        then
            Ok (name, params, header)
        else
            Error (Located.range name, Build_problem.Ambiguous_definition)






let class_headers
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : (Inductive.params * Inductive.Header.t array) result2
=
    assert (0 < Array.length inds);
    class_header 0 inds context
    >>=
    fun (name0, params0, header0) ->
    let params0 =
        Array.map (fun (name, typ) -> Located.value name, typ) params0
    in
    Interval_monadic.fold
        (fun i (set, lst) ->
            class_header i inds context
            >>=
            fun (name, params, header) ->
            check_params params0 name params context
            >>= fun _ ->
            let name_str = Located.value name in
            if String_set.mem name_str set then
                Error(Located.range name, Build_problem.Duplicate_inductive)
            else
                Ok (String_set.add name_str set, header :: lst)
        )
        1
        (Array.length inds)
        (String_set.singleton (Located.value name0), [])
    >>= fun (_, lst) ->
    Ok (params0, Array.of_list (header0 :: List.rev lst))





let push_params
    (ntypes: int)
    (params: Inductive.params)
    (context: Context.t)
    : Context.t
=
    Array.foldi_left
        (fun context iparam (name,typ) ->
            Context.push_local
                name
                (Term.up_from ntypes iparam typ)
                context)
        context
        params





let push_types
    (params: Inductive.params)
    (headers: Inductive.Header.t array)
    (context: Context.t)
    : Context.t
=
    let _, context =
        Array.fold_left
            (fun (i,context) header ->
                let open Inductive.Header in
                i + 1,
                Context.add_axiom
                    (name header)
                    (Term.up i (kind params header))
                    context
            )
            (0,context)
            headers
    in
    context










let fold_type
    (argf: 'a -> Term.typ -> Gamma.t -> 'a result2)
    (resf: 'a -> Term.typ -> Gamma.t -> 'b result2)
    (a: 'a)
    (typ: Term.typ)
    (gamma: Gamma.t) :
    'b result2
=
    let rec fold a typ gamma =
        let open Term
        in
        match Algo.key_normal typ gamma with
        | Pi (arg, res, info) ->
            argf a arg gamma
            >>=
            fun a ->
            fold a res (Gamma.push_local (Pi_info.name info) arg gamma)

        | res ->
            resf a res gamma
    in
    fold a typ gamma







let positive_occurrences
    (p: int -> bool)
    (typ: Term.typ)
    (gamma: Gamma.t)
    : (int * int) list option
=
    (* [typ] is the final type of the argument type of a contructor argument.
    Check that all types of the inductive family do not occur or occur only
    positively (directly or nested) as [I a1 a2 ...] where none of the I's
    appears in any ai.

    Return [None]

        - if [I] occurs as [I a1 a2 ...] and [I] occurs within some [ai].

        - if [typ] does not start with a variable and some [I] occurs in [typ].

    Return list of pairs (level, iparam)

        - [I] occurs indirectly in [level] as [iparam] argument.
    *)
    let rec collect typ lst =
        let f, args = Algo.key_split typ gamma in
        match f with
        | Variable i ->
            let level = Gamma.level_of_index i gamma in
            if p level then
                if List.exists
                    (fun (arg, _) ->
                        Gamma.level_has p arg gamma)
                    args
                then
                    None
                else
                    Some lst
            else
                (* check indirect occurrences in args *)
                let module LMon = List.Monadic (Option) in
                LMon.foldi_left
                        (fun k (arg,_) lst ->
                            collect arg ((level,k) :: lst))
                        args
                        lst

        | _ ->
            if Gamma.level_has p f gamma then
                None
            else
                Some lst
    in
    collect typ []




let negative_parameter_occurrences
    (is_inductive: int -> bool)
    (param1: int)
    (param2: int)
    (typ: Term.typ)
    (gamma: Gamma.t)
    (negative_params: Int_set.t):
    Int_set.t
=
    (* [typ] is the final type of an argument type of a constructor of the
    inductive family.

    Collect all occurrences of the parameters which might not be strictly
    positive, i.e. if a parameter occurs within some application and it is not
    the application of a type of the inductive family or the parameter does not
    occur in the correct position.
    *)
    Common.Interval.fold
        negative_params
        (fun level_param set ->
            match
                positive_occurrences
                    (fun level -> level = level_param)
                    typ
                    gamma
            with
            | None ->
                set
            | Some lst ->
                if
                    List.for_all
                        (fun (level,iparam) ->
                            (   is_inductive level
                                && param1 + iparam = level_param)
                            ||
                            match Gamma.inductive_at_level level gamma with
                            | None ->
                                false
                            | Some ind ->
                                Inductive.is_param_positive iparam ind)
                        lst
                then
                    set
                else
                    Int_set.add (level_param - param1) set
        )
        param1 param2





let check_constructor_argument_result_type
    (is_inductive: int -> bool)
    (param1: int)
    (param2: int)
    (range: range)
    (negative_params: Int_set.t)
    (typ: Term.typ)
    (gamma: Gamma.t):
    Int_set.t result2
=
    (* [typ] is the final type of an argument type of a constructor of the
    inductive family.

    An inductive [I] type of the family either

    - does not appear
    - appears as [I a0 a1 ...] where I does not appear in [a0 a1 ...]
        - either immediately
        - or indirectly as I1 ... (I a0 a1 ...]) ...
    *)
    match positive_occurrences is_inductive typ gamma with
    | None ->
        Error (range, Build_problem.Not_positive)

    | Some lst ->
        let get_ind level = Gamma.inductive_at_level level gamma
        in
        match
            List.find
                (fun (level, iparam) ->
                    match get_ind level with
                    | None ->
                        true
                    | Some ind ->
                        Inductive.is_param_negative iparam ind)
                lst
        with
        | None ->
            Ok (
                negative_parameter_occurrences
                    is_inductive param1 param2
                    typ gamma
                    negative_params
            )

        | Some (level, iparam) ->
            match get_ind level with
            | None ->
                Error (range, Build_problem.Not_positive)
            | Some ind ->
                Error (
                    range,
                    Build_problem.Nested_negative (ind, iparam, gamma)
                )





let check_constructor_argument_type
    (is_inductive: int -> bool)
    (param1: int)
    (param2: int)
    (range: range)
    (negative_params: Int_set.t)
    (arg_typ: Term.typ)
    (gamma: Gamma.t) :
    Int_set.t result2
=
    fold_type
        (fun negative_params typ gamma ->
            if Gamma.level_has is_inductive typ gamma then
                Error (range, Build_problem.Negative)
            else
                Ok (
                    Term.fold_free
                        (fun idx set ->
                            let level = Gamma.level_of_index idx gamma in
                            if param1 <= level && level < param2 then
                                Int_set.add (level - param1) set
                            else
                                set
                        )
                        typ
                        negative_params
                )
        )
        (check_constructor_argument_result_type
            is_inductive
            param1 param2
            range)
        negative_params
        arg_typ
        gamma





let check_constructor_result_type
    (i: int)
    (cnt0: int)
    (params: Inductive.params)
    (headers: Inductive.Header.t array)
    (range: range)
    (negative_params: Int_set.t)
    (res: Term.typ)
    (gamma: Gamma.t) :
    Int_set.t result2
=
    if
        Inductive.Header.is_well_constructed
            i
            params
            headers
            Gamma.(count gamma - cnt0)
            res
    then
        Ok negative_params
    else
        Error (range, Build_problem.Wrong_type_constructed)





let check_constructor_type
    (i: int)
    (negative_params: Int_set.t)
    (params: Inductive.params)
    (headers: Inductive.Header.t array)
    (name: string Located.t)
    (typ: Term.typ)
    (c: Context.t)
    : (Int_set.t * Inductive.Constructor.t) result2
=
    let nparams = Array.length params
    and ntypes  = Array.length headers
    and range   = Located.range name
    in
    let cnt0 = Context.count c - nparams - ntypes in
    assert (0 <= cnt0);
    let is_inductive level =
        cnt0 <= level && level < cnt0 + ntypes
    in
    fold_type
        (check_constructor_argument_type
            is_inductive
            (cnt0 + ntypes)
            (cnt0 + ntypes + nparams)
            range)
        (check_constructor_result_type i (Context.count c) params headers range)
        negative_params
        typ
        (Context.gamma c)
    >>= fun negative_params ->
    Ok (negative_params, Inductive.Constructor.make (Located.value name) typ)





let one_constructor
    (i: int)                                      (* inductive type *)
    (negative_params: Int_set.t)
    (params: Inductive.params)
    (headers: Inductive.Header.t array)
    ((name, (fargs, typ))
        : Source_entry.named_signature)
    (c: Context.t)                                (* with types and params *)
    : (Int_set.t * Inductive.Constructor.t) result2
=
    (* Collect constructor arguments. *)
    let module Lst = List.Monadic (Result) in
    Lst.fold_left
        (fun (name, typ) (fargs, c) ->
            match typ with
            | None ->
                assert false  (* Illegal call! Parser has to prevent that. *)
            | Some typ ->
                Build_expression.build_named_type name typ c
                >>= fun typ ->
                let name = Located.value name in
                Ok (
                    (name, typ) :: fargs
                    ,
                    Context.push_local name typ c
                )
        )
        fargs
        ([], c)
    >>= fun (fargs, c1) ->
    (
    (* Analyze final type of the signature. *)
        match typ with
        | None ->
            (*  Must be the default inductive type. Only possible without
                indices. *)
            if
                Inductive.Header.has_index headers.(i)
            then
                Error (
                    Located.range name,
                    Build_problem.Missing_inductive_type
                )
            else
                Ok (Inductive.Header.default_type i params headers)

        | Some typ ->
            Build_expression.build_named_type name typ c1
    )
    >>= fun typ ->
    let typ =
        List.fold_left
            (fun res (name, typ) ->
                Term.(Pi (typ, res, Pi_info.typed name)))
            typ
            fargs
    in
    check_constructor_type i negative_params params headers name typ c





let one_constructor_set
    (i: int) (* inductive type *)
    (negative_params: Int_set.t)
    (params: Inductive.params)
    (headers: Inductive.Header.t array)
    (inds: Source_entry.inductive array)
    (c: Context.t)  (* with types and params *)
    : (Int_set.t * Inductive.Constructor.t array) result2
=
    let module Arr = Array.Monadic (Result) in
    Arr.fold_left
        (fun constructor (set, negative_params, lst) ->
            one_constructor i negative_params params headers constructor c
            >>= fun (negative_params, co) ->
            let name, _ = constructor in
            let name_str = Located.value name in
            if String_set.mem name_str set then
                Error (Located.range name, Build_problem.Duplicate_constructor)
            else
                Ok (String_set.add name_str set, negative_params, co :: lst)
        )
        (snd inds.(i))
        (String_set.empty, negative_params, [])
    >>= fun (_, negative_params, lst) ->
    Ok (negative_params, Array.of_list (List.rev lst))




let constructors
    (params: Inductive.params)
    (headers: Inductive.Header.t array)
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    let context1 =
        push_types params headers context
        |>
        push_params (Array.length headers) params
    in
    (* list of constructor sets with corresponding header a number of previous
    constructors. *)
    let module Arr = Array.Monadic (Result) in
    Arr.foldi_left
        (fun i header (n, negative_params, constructors) ->
            one_constructor_set i negative_params params headers inds context1
            >>= fun (negative_params, constructor_set) ->
            Ok (
                n + Array.length constructor_set
                ,
                negative_params
                ,
                Inductive.Type.make n header constructor_set :: constructors
            )
        )
        headers
        (0, Int_set.empty, [])
    >>=
    fun (_, negative_params, types) ->
    Ok Inductive.(make params negative_params (Array.of_list (List.rev types)))






let build
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    class_headers inds context
    >>= fun (params,headers) ->
    constructors params headers inds context
