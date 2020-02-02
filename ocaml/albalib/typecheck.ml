open Fmlib

module Algo = Gamma_algo.Make (Gamma_holes)

module Uni = Unifier.Make (Gamma_holes)


include Gamma_holes


let is_subtype (sub: Term.typ) (typ: Term.typ) (gh: t) : bool
    =
    Option.has (Uni.unify sub typ true gh)
let _ = is_subtype




let rec typecheck (term: Term.t) (c: t): Term.typ option =
    let open Term in
    let open Option in
    match term with
    | Sort s ->
        Some (type_of_sort s)

    | Value v ->
        Some (type_of_literal v c)

    | Variable i ->
        Some (type_of_variable i c)

    | Appl (f, arg, _ ) ->
        typecheck f c >>= fun f_type ->
        typecheck arg c >>= fun arg_type ->
        (
            match Algo.key_normal f_type c with
            | Pi (tp, rt, _ ) when is_subtype arg_type tp c ->
                Some (apply rt arg)
            | _ ->
              None
        )

    | Typed (exp, tp) ->
        typecheck exp c >>=
        fun exp_type ->
        typecheck tp c >>=
        fun tp_tp ->
        (   match tp_tp with
            | Sort _  when is_subtype exp_type tp c ->
                Some tp
            | _ ->
                None
        )

    | Lambda (_, _, _ ) ->
        assert false (* nyi *)

    | Pi (_, _, _) ->
        assert false (* nyi *)




let typecheck (term: Term.t) (gamma: Gamma.t): Term.typ option =
    typecheck term (make gamma)



let is_valid_context (_: Gamma.t): bool =
    assert false
