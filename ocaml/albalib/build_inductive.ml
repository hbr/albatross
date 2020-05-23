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

(*
module Inductive =
struct
    type named_type = string * Term.typ

    type params = named_type array

    type typ =
        int                  (* Number of previous constructors *)
        *
        named_type           (* name and type of the inductive type *)
        *
        named_type array     (* names and types of the constructors *)

    type t =
        params
        *
        typ array


    let make
        (params: params)
        (types:  typ array)
        : t
    =
        params, types
end
*)


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






let class_header
    (i: int)
    (inds: Source_entry.inductive array)
    (c0: Context.t)
    : (range * params_located * Inductive.Header.t) result2
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
        Error (
            range,
            Build_problem.No_inductive_type
        )
    | Some (args, sort) ->
        Ok (
            Located.range name
            ,
            Array.of_list params
            ,
            Inductive.Header.make
                (Located.value name)
                kind
                args
                sort
        )






let check_params
    (params0: Inductive.params)
    (range: range)
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
            range,
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



let class_headers
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : (Inductive.params * Inductive.Header.t array) result2
=
    assert (0 < Array.length inds);
    class_header 0 inds context
    >>=
    fun (_, params0, header0) ->
    let params0 =
        Array.map (fun (name, typ) -> Located.value name, typ) params0
    in
    Interval_monadic.fold
        (fun i lst ->
            class_header i inds context
            >>=
            fun (range, params, header) ->
            check_params params0 range params context
            >>= fun _ ->
            Ok (header :: lst)
        )
        1
        (Array.length inds)
        []
    >>= fun lst ->
    Ok (params0, Array.of_list (header0 :: List.rev lst))





let push_params
    (params: Inductive.params)
    (context: Context.t)
    : Context.t
=
    Array.fold_left
        (fun context (name,typ) ->
            Context.push_local
                name
                typ
                context)
        context
        params




let prefix_params
    (params: Inductive.params)
    (typ: Term.typ)
    : Term.typ
=
    Array.fold_right
        (fun (name, typ) res ->
            Term.(Pi (typ, res, Pi_info.typed name)))
        params
        typ



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
                    (Term.up i (prefix_params params (kind header)))
                    context
            )
            (0,context)
            headers
    in
    context





let check_constructor
    (_: int)
    (_: int)
    (_: int)
    (_: string Located.t)
    (_: Term.typ)
    (_: Context.t)
    : Inductive.Constructor.t result2
=
    assert false




let one_constructor
    (i: int)                                      (* inductive type *)
    (ntypes: int)
    (nparams: int)
    ((name, (fargs, typ))
        : Source_entry.named_signature)
    (c: Context.t)                                (* with types and params *)
    : Inductive.Constructor.t result2
=
    let module Lst = List.Monadic (Result) in
    Lst.fold_left
        (fun (name, typ) (fargs, c) ->
            match typ with
            | None ->
                assert false  (* Illegal call! Parser to prevent that. *)
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
    match typ with
    | None ->
        assert false

    | Some typ ->
        Build_expression.build_named_type name typ c1
        >>= fun typ ->
        let typ: Term.typ =
            List.fold_left
                (fun res (name, typ) ->
                    Term.(Pi (typ, res, Pi_info.typed name)))
                typ
                fargs
        in
        check_constructor i ntypes nparams name typ c





let one_constructor_set
    (i: int)
    (ntypes: int)
    (nparams: int)
    (inds: Source_entry.inductive array)
    (c: Context.t)  (* with types and params *)
    : Inductive.Constructor.t array result2
=
    let module Arr = Array.Monadic (Result) in
    Arr.fold_left
        (fun constructor lst ->
            one_constructor i ntypes nparams constructor c
            >>= fun co ->
            Ok (co :: lst)
        )
        (snd inds.(i))
        []
    >>= fun lst ->
    Ok (Array.of_list (List.rev lst))




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
        push_params params
    and ntypes =
        Array.length headers
    and nparams =
        Array.length params
    in
    (* list of constructor sets with corresponding header a number of previous
    constructors. *)
    let module Arr = Array.Monadic (Result) in
    Arr.foldi_left
        (fun i header (n, constructors) ->
            one_constructor_set i ntypes nparams inds context1
            >>= fun constructor_set ->
            Ok (
                n + Array.length constructor_set
                ,
                Inductive.Type.make n header constructor_set :: constructors
            )
        )
        headers
        (0, [])
    >>=
    fun (_, types) ->
    Ok Inductive.(make params (Array.of_list types))






let build
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    class_headers inds context
    >>= fun (params,headers) ->
    constructors params headers inds context
