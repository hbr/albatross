open Fmlib


module type HOLES =
sig
    include Gamma_algo.GAMMA

    val context: t -> Gamma.t

    val expand: Term.t -> t -> Term.t

    val is_hole: int -> t -> bool

    val value: int -> t -> Term.t option

    val fill_hole0: int -> Term.t -> bool -> t -> t
end


module Make (Gh: HOLES) =
struct

    module Uc =
    struct
        type locals = (string * Term.typ) array

        type t = {
            gh: Gh.t;
            locals: locals;
            stack: locals list;
        }


        let base (uc: t): Gh.t =
            uc.gh


        let nlocals (uc: t): int =
            Array.length uc.locals


        let count (uc: t): int =
            Gh.count uc.gh + nlocals uc


        let is_valid_index (idx: int) (uc: t): bool =
            idx < count uc


        let name_of_index (idx: int) (uc: t): string =
            assert (is_valid_index idx uc);
            if idx < nlocals uc then
                fst uc.locals.(Term.bruijn_convert idx (nlocals uc))
            else
                Gh.name_of_index (idx - nlocals uc) uc.gh


        let definition_term (idx: int) (uc: t): Term.t option =
            assert (is_valid_index idx uc);
            let nlocs = nlocals uc
            in
            if idx < nlocs then
                None
            else
                Option.map
                    (Term.up nlocs)
                    (Gh.definition_term (idx - nlocs) uc.gh)


        let type_of_variable (idx: int) (uc: t): Term.typ =
            assert (is_valid_index idx uc);
            let nlocs = nlocals uc
            in
            if idx < nlocs then
                Term.up
                    (idx + 1)
                    (snd uc.locals.(
                        Term.bruijn_convert idx (nlocals uc)))
            else
                Term.up
                    nlocs
                    (Gh.type_of_variable (idx - nlocs) uc.gh)


        let type_of_literal (lit: Term.Value.t) (uc: t): Term.typ =
            Term.up (nlocals uc) (Gh.type_of_literal lit uc.gh)


        let is_hole (idx: int) (uc: t): bool =
            let nlocs = nlocals uc in
            if idx < nlocs then
                false
            else
                Gh.is_hole (idx - nlocs) uc.gh

        let fill_hole
            (idx: int)
            (typ: Term.typ)
            (beta_reduce: bool)
            (uc: t)
            : t option
            =
            assert (is_hole idx uc);
            let nlocs = nlocals uc
            in
            Option.map
                (fun typ0 ->
                    {uc with
                        gh =
                            Gh.fill_hole0
                                (idx - nlocs)
                                typ0
                                beta_reduce
                                uc.gh})
                (Term.down nlocs typ)


        let expand (term: Term.t) (uc: t): Term.t =
            let nlocs = nlocals uc in
            Term.substitute_with_beta
                (fun i ->
                    if i < nlocs then
                        Variable i
                    else
                        match Gh.value (i - nlocs) uc.gh with
                        | None ->
                            Variable i
                        | Some term ->
                            Term.up nlocs term)
                term


        let make (gh: Gh.t): t =
            { gh; locals = [||]; stack = [] }


        let push (name: string) (typ: Term.typ) (uc: t): t =
            { uc with
                locals = Array.push (name,typ) uc.locals;
                stack  = uc.locals :: uc.stack;
            }


        let push_local = push


        let pop (uc: t): t =
            match uc.stack with
            | [] ->
                assert false (* Illegal call! *)
            | locals :: stack ->
                {uc with locals; stack}
    end (* Uc *)







    module Algo = Gamma_algo.Make (Uc)

    let string_of_term (t: Term.t) (uc: Uc.t): string =
        let module PP = Pretty_printer.Pretty (String_printer) in
        let module P = Term_printer.Pretty (Uc) (PP) in
        String_printer.run
            (PP.run 0 70 70 (P.print t uc))
    let _ = string_of_term







    type 'a t = Uc.t -> (Uc.t * 'a) option


    let succeed (a: 'a) : 'a t =
        fun uc -> Some (uc, a)


    let fail: 'a t =
        fun _ -> None


    let (>>=) (m: 'a t) (f: 'a -> 'b t): 'b t =
        fun uc ->
        match m uc with
        | None ->
            fail uc
        | Some (uc, a) ->
            f a uc

    let catch (m: 'a t) (f: unit -> 'a t): 'a t =
        fun uc ->
        match m uc with
        | None ->
            f () uc
        | _ as res ->
            res


    let push (name: string) (typ: Term.typ): unit t =
        fun uc -> Some (Uc.push name typ uc, ())


    let pop (): unit t =
        fun uc -> Some (Uc.pop uc, ())


    let nlocals: int t =
        fun uc -> Some (uc, Uc.nlocals uc)


    let is_hole (idx: int): bool t =
        fun uc ->
        Some (uc, Uc.is_hole idx uc)


    let is_hole_or_fail (idx: int): unit t =
        is_hole idx >>= fun flag ->
        if flag then
            succeed ()
        else
            fail


    let type_of_term (term: Term.t): Term.typ t =
        fun uc ->
        Some (uc, Algo.type_of_term term uc)


    let type_of_variable (idx: int): Term.typ t =
        fun uc ->
        Some (uc, Uc.type_of_variable idx uc)


    let key_normal (typ: Term.typ): Term.typ t =
        fun uc ->
        Some (
            uc,
            Algo.key_normal
                (Uc.expand typ uc)
                uc
        )


    let fill_hole (idx: int) (value: Term.typ) (beta_reduce: bool) (): unit t =
        fun uc ->
        Option.map
            (fun uc -> uc, ())
            (Uc.fill_hole idx value beta_reduce uc)


    let get_fterm (arg: Term.t) (typ: Term.typ) (): Term.t t =
        fun uc ->
        let arg_tp = Algo.type_of_term arg uc
        and exp =
            match arg with
            | Variable i ->
                Term.map
                    (fun j ->
                        if i = j then
                            0
                        else
                            j + 1)
                    typ
            | _ ->
                Term.up1 typ
        in
        Some (uc, Term.lambda "_" arg_tp exp)


    let in_pushed
        (name: string)
        (typ: Term.typ)
        (m: unit -> unit t)
        ()
        : unit t
        =
        push name typ
        >>= m
        >>= pop


    let rec unify0
        (act: Term.typ)
        (req: Term.typ)
        (is_super: bool)
        ()
        : unit t
        =
        let set i typ beta_reduce (): unit t =
            type_of_term typ   >>= fun act ->
            type_of_variable i >>= fun req ->
            unify0 act req true ()
            >>= fill_hole i typ beta_reduce
        in
        let set_if_hole i typ (): unit t =
            is_hole_or_fail i >>= set i typ false
        in
        let setF f arg typ: unit t =
            is_hole_or_fail f
            >>=
            get_fterm arg typ >>= fun fterm ->
            set f fterm true ()
        in
        key_normal act >>= fun act ->
        key_normal req >>= fun req ->
        let open Term
        in
        match act, req with
        | Sort act, Sort req
            when (is_super && Sort.is_super req act)
                 || (not is_super && req = act)
            ->
                succeed ()

        | Value act, Value req ->
            if Value.is_equal act req then
                succeed ()
            else
                fail

        | Appl (Variable f, arg, _), _  ->
            setF f arg req

        | _, Appl (Variable f, arg, _ ) ->
            setF f arg act

        | Appl (f_act, arg_act, _ ), Appl (f_req, arg_req, _) ->
            unify0 f_act f_req false ()
            >>=
            unify0 arg_act arg_req false

        | Pi (act_arg, act_rt, info), Pi (req_arg, req_rt, _) ->
            unify0 act_arg req_arg false ()
            >>= in_pushed
                    (Pi_info.name info)
                    act_arg
                    (unify0 act_rt req_rt is_super)

        | Variable i, Variable j ->
            if i = j then
                succeed ()
            else
                nlocals >>= fun nb ->
                if i < nb || j < nb then
                    fail
                else
                    is_hole i >>= fun i_hole ->
                    is_hole j >>= fun j_hole ->
                    if not (i_hole || j_hole) then
                        fail
                    else if i_hole && j_hole then
                        catch
                            (set j act false ())
                            (set i req false)
                    else if i_hole then
                        set i req false ()
                    else if j_hole then
                        set j act false ()
                    else
                        assert false (* cannot happen, illegal path *)

        | Variable i, _ ->
            set_if_hole i req ()

        | _, Variable j ->
            set_if_hole j act ()

        | _, _ ->
            fail





    let unify
        (act: Term.typ)
        (req: Term.typ)
        (is_super: bool)
        (gh: Gh.t)
        : Gh.t option
        =
        (*Printf.printf "\nnew unification (old unifier)\n";*)
        let res =
        Option.map
            (fun (uc,()) ->
                Uc.base uc)
            (unify0
                act
                req
                is_super
                ()
                (Uc.make gh))
        in
        match res with
        | Some _ ->
            res
        | None ->
            (*let string_of_term t =
                Term_printer.string_of_term t (Gh.context gh)
            in
            Printf.printf "failed act %s, req %s (%b)\n"
                (string_of_term act)
                (string_of_term req)
                is_super;*)
            res
end (* Make *)
