open Fmlib


module type HOLES =
sig
    include Gamma_algo.GAMMA

    val context: t -> Gamma.t

    val expand: Term.t -> t -> Term.t

    val is_hole: int -> t -> bool

    val value: int -> t -> Term.t option

    val fill_hole: int -> Term.t -> t -> t
end


module Make (GH: HOLES) =
struct
    module Algo = Gamma_algo.Make (GH)

    type t = {
        gh: GH.t;
        gamma: Gamma.t
    }

    let make (gh: GH.t): t =
        {gh; gamma = GH.context gh}

    let context (uc: t): GH.t =
        uc.gh


    let push (tp: Term.typ) (uc: t): t =
        {uc with gamma = Gamma.push_local "_" tp uc.gamma}


    let string_of_term (term: Term.t) (uc: t): string =
        Term_printer.string_of_term term uc.gamma
    let _ = string_of_term

    let delta (uc: t): int =
        Gamma.count uc.gamma - GH.count uc.gh

    let down (typ: Term.typ) (uc: t): Term.typ option =
        Term.down (delta uc) typ

    let is_hole (idx: int) (uc: t): bool =
        let nb = delta uc in
        if idx < nb then
            false
        else
            GH.is_hole (idx - delta uc) uc.gh

    let expand (term: Term.t) (uc: t): Term.t =
        let del = delta uc
        in
        Term.substitute
            (fun i ->
                if i < del then
                    Variable i
                else
                    match GH.value (i - del) uc.gh with
                    | None ->
                        Variable i
                    | Some term ->
                        Term.up del term)
            term



    let rec unify0
        (act: Term.typ)
        (req: Term.typ)
        (is_super: bool)
        (uc: t)
        : t option
        =
        let nb = delta uc
        in
        let set i typ =
            Option.(
                down typ uc
                >>= fun typ0 ->
                map
                    (fun uc ->
                        {uc with gh = GH.fill_hole (i - nb) typ0 uc.gh})
                    (unify0
                        (Gamma.type_of_term typ uc.gamma)
                        (Gamma.type_of_variable i uc.gamma)
                        true
                        uc))
        in
        let req = expand req uc
        and act = expand act uc
        in
        let req = Gamma.key_normal req uc.gamma
        and act = Gamma.key_normal act uc.gamma
        in
        let open Term
        in
        match act, req with
        | Variable i, Variable j ->
            if i = j then
                Some uc
            else if i < nb || j < nb then
                None
            else
                let iph = is_hole i uc
                and jph = is_hole j uc
                in
                if not (iph || jph) then
                    None
                else if iph && jph then
                    match set j act with
                    | None ->
                        set i req
                    | res ->
                        res
                else if iph then
                    set i req
                else if jph then
                    set j act
                else
                    assert false (* cannot happen, illegal path *)

        | Variable i, _ when is_hole i uc ->
            set i req

        | _, Variable j when is_hole j uc ->
            set j act

        | Sort act, Sort req
            when (is_super && Sort.is_super req act)
                 || (not is_super && req = act)
            ->
                Some uc

        | Appl (f_act, arg_act, _ ), Appl (f_req, arg_req, _) ->
            let open Option in
            unify0 f_act f_req false uc
            >>=
            unify0 arg_act arg_req false

        | Pi (act_arg, act_rt, _), Pi (req_arg, req_rt, _) ->
            Option.(
                unify0 act_arg req_arg false uc
                >>= fun uc ->
                unify0 act_rt req_rt is_super (push act_arg uc)
            )

        | Pi (_, _, _), _ ->
            assert false

        | _, _ ->
            None




    let unify
        (act: Term.typ)
        (req: Term.typ)
        (is_super: bool)
        (gh: GH.t)
        : GH.t option
        =
        Option.map
            (fun uc -> uc.gh)
            (unify0 act req is_super (make gh))

end
