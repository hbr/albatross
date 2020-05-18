open Fmlib
open Common

open Alba_core
open Ast



module Result = Fmlib.Result.Make (Build_problem)
module Interval_monadic = Interval.Monadic (Result)




module Inductive =
struct
    type t = unit
end


type 'a result2 = ('a, Build_problem.t) result

type params = Term.typ Located.t array

type header0 = string Located.t * params * Term.typ

type header = string Located.t * Term.typ


let (>>=) = Result.(>>=)



let class_header
    (i: int)
    (inds: Source_entry.inductive array)
    (_: Context.t)
    : header0 result2
=
    assert (i < Array.length inds);
    assert false



let check_params
    (params0: params)
    (params: params)
    (_: Context.t)
    : unit result2
=
    if Array.length params0 <> Array.length params then
        Error (assert false)
    else
        assert false



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
            check_params params0 params context
            >>= fun _ ->
            Ok ((name,typ) :: lst)
        )
        1
        (Array.length inds)
        []
    >>= fun lst ->
    Ok (params0, Array.of_list ((name0,typ0) :: List.rev lst))



let one_constructor_set
    (_: int)
    (_: header array)
    (_: Source_entry.inductive array)
    (_: Context.t)
    : Term.typ array result2
=
    assert false




let constructors
    (_: params)
    (headers: header array)
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    let module Arr = Array.Monadic (Result) in
    Arr.mapi
        (fun i header ->
            one_constructor_set i headers inds context
            >>= fun constructors ->
            Ok (header, constructors))
        headers
    >>= fun _ ->
    assert false



let build
    (inds: Source_entry.inductive array)
    (context: Context.t)
    : Inductive.t result2
=
    class_headers inds context
    >>= fun (params,headers) ->
    constructors params headers inds context
