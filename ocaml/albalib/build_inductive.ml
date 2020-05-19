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



type 'a result2 = ('a, Build_problem.t) result

type params = (string Located.t * Term.typ) array

type header0 = string Located.t * params * Term.typ

type header = string Located.t * Term.typ (* type without params *)


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
    : header0 result2
=
    (* class Name (P0: PT0) (P1: PT1) ... : TP *)
    assert (i < Array.length inds);
    let (name, (params, typ_exp)), _ = inds.(i) in
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
    build_type_or_any name typ_exp c1
    >>= fun typ ->
    match Algo.sort_of_kind typ (Context.gamma c1) with
    | None ->
        assert (typ_exp <> None);
        let range =
            Located.range (Option.value typ_exp)
        in
        Error (
            range,
            Build_problem.No_inductive_type
        )
    | Some _ ->
        Ok (
            name,
            Array.of_list (List.rev params),
            typ
        )




let check_params
    (params0: params)
    (name: string Located.t)
    (params: params)
    (context: Context.t)
    : unit result2
=
    (* Check parameter count, names and types *)
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
                    if Located.value name <> Located.value name0 then
                        Error (
                            Located.range name,
                            Build_problem.Wrong_parameter_name
                                (Located.value name0)
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
                            Located.range name,
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
    : (params * header array) result2
=
    assert (0 < Array.length inds);
    class_header 0 inds context
    >>=
    fun (name0, params0, typ0) ->
    Interval_monadic.fold
        (fun i lst ->
            class_header i inds context
            >>=
            fun (name, params, typ) ->
            check_params params0 name params context
            >>= fun _ ->
            Ok ((name,typ) :: lst)
        )
        1
        (Array.length inds)
        []
    >>= fun lst ->
    Ok (params0, Array.of_list ((name0,typ0) :: List.rev lst))



let push_params
    (params: params)
    (context: Context.t)
    : Context.t
=
    Array.fold_left
        (fun context (name,typ) ->
            Context.push_local
                (Located.value name)
                typ
                context)
        context
        params



let prefix_params
    (params: params)
    (typ: Term.typ)
    : Term.typ
=
    Array.fold_right
        (fun (name, typ) res ->
            Term.(Pi (typ, res, Pi_info.typed (Located.value name))))
        params
        typ



let push_types
    (params: params)
    (headers: header array)
    (context: Context.t)
    : Context.t
=
    let _, context =
        Array.fold_left
            (fun (i,context) (name,typ) ->
                i + 1,
                Context.add_axiom
                    (Located.value name)
                    (Term.up i (prefix_params params typ))
                    context
            )
            (0,context)
            headers
    in
    context





let check_constructor
    (_: string Located.t)
    (_: Term.typ)
    (_: Context.t)
    : (string * Term.typ) result2
=
    assert false




let one_constructor
    (_: int)                                      (* inductive type *)
    ((name, (fargs, typ))
        : Source_entry.named_signature)
    (c: Context.t)                                (* with types and params *)
    : (string * Term.typ) result2
=
    let module Lst = List.Monadic (Result) in
    Lst.fold_left
        (fun (name, typ) (fargs, c) ->
            match typ with
            | None ->
                assert false  (* Illegal call! Parser must not allow that. *)
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
        check_constructor name typ c





let one_constructor_set
    (i: int)
    (inds: Source_entry.inductive array)
    (c: Context.t)  (* with types and params *)
    : (string *Term.typ) array result2
=
    let module Arr = Array.Monadic (Result) in
    Arr.fold_left
        (fun constructor lst ->
            one_constructor i constructor c
            >>= fun co ->
            Ok (co :: lst)
        )
        (snd inds.(i))
        []
    >>= fun lst ->
    Ok (Array.of_list (List.rev lst))




let constructors
    (params: params)
    (headers: header array)
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    let context1 =
        push_types params headers context |> push_params params
    in
    let module Arr = Array.Monadic (Result) in
    Arr.foldi_left
        (fun i header (n,constructors) ->
            one_constructor_set i inds context1
            >>= fun constructor_set ->
            let header =
                let name, typ = header in
                Located.value name, typ
            in
            Ok (
                n + Array.length constructor_set,
                (n, header, constructor_set) :: constructors
            )
        )
        headers
        (0, [])
    >>=
    fun (_, lst) ->
        let params =
            Array.map (fun (name,typ) -> Located.value name, typ) params
        and types =
            Array.of_list (List.rev lst)
        in
    Ok Inductive.(make params types)






let build
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    class_headers inds context
    >>= fun (params,headers) ->
    constructors params headers inds context
