open Fmlib
open Common


module GAlgo = Gamma_algo.Make (Gamma_holes)

type term_n = Term.t * int

module Local =
struct
    type t =
        | Hole of term_n option
        | Bound of int  (* number of bound variable (counting upwards) *)

    let hole: t =
        Hole None

    let make_bound (n: int): t =
        Bound n

    let is_hole (loc: t): bool =
        match loc with
        | Hole _ ->
            true
        | Bound _ ->
            false

    let is_bound (loc: t): bool =
        not (is_hole loc)


    let value (loc: t): term_n option =
        match loc with
        | Hole value ->
            value
        | _ ->
            None

    let set_value (term_n: term_n) (loc: t): t =
        match loc with
        | Hole _ ->
            Hole (Some term_n)
        | _ ->
            assert false (* Illegal call! *)

    let bound_number (loc: t): int =
        match loc with
        | Bound n ->
            n
        | _ ->
            assert false (* Illegal call! *)
end



type entry =
    | Required_type of term_n
    | Built of term_n



type t = {
    base0: Gamma.t;
    base: Gamma.t;
    locals: Local.t array;
    bounds: (int * bool) array;          (* level of bound, is typed? *)
    stack: entry list;
    binders: (int * int) list; (* start bound, start local *)
}



let count (bc: t): int =
    Gamma.count bc.base


let count_locals (bc: t): int =
    Array.length bc.locals


let count_bounds (bc: t): int =
    Array.length bc.bounds


let count_base (bc: t): int =
    count bc - count_locals bc



let base (bc: t): Gamma.t =
    bc.base



let top_of_stack (bc: t): entry =
    match bc.stack with
    | top :: _ ->
        top
    | _ ->
        assert false (* Illegal call! *)



let string_of_term (term: Term.t) (bc: t): string =
    Term_printer.string_of_term term bc.base
let _ = string_of_term




let placeholder_name (cnt: int): string =
    "<" ^ string_of_int cnt ^ ">"



let term_of_term_n ((term,n): term_n) (bc: t): Term.t =
    Term.up (count bc - n) term



let required_type (bc: t): Term.typ =
    match top_of_stack bc with
    | Required_type (term_n) ->
        term_of_term_n term_n bc
    | _ ->
        assert false (* Illegal call! *)




let built_type (bc: t): Term.typ =
    match top_of_stack bc with
    | Built (term_n) ->
        Gamma.type_of_term (term_of_term_n term_n bc) bc.base
    | _ ->
        assert false (* Illegal call! *)




let local_of_index (idx: int) (bc: t): Local.t =
    let nlocs = count_locals bc
    in
    assert (idx < nlocs);
    bc.locals.(Term.bruijn_convert idx nlocs)




let is_hole (idx: int) (bc: t): bool =
    idx < count_locals bc
    && Local.is_hole (local_of_index idx bc)





let value (idx: int) (bc: t): Term.t option =
    let nlocs = count_locals bc
    in
    if nlocs <= idx then
        None
    else
        Option.map
            (fun (term, n) ->
                assert (n <= count bc);
                Term.up (count bc - n) term)
            (Local.value (local_of_index idx bc))




let expand (term: Term.t) (bc: t): Term.t =
    Term.substitute
        (fun i ->
            match value i bc with
            | None ->
                Variable i
            | Some term ->
                term)
        term




let fill_hole (idx: int) (value: Term.t) (bc: t): t =
    let cnt    = count bc
    and nlocs  = count_locals bc
    and locals = Array.copy bc.locals
    in
    let loc_level = Term.bruijn_convert idx nlocs
    in
    locals.(loc_level) <-
        Local.set_value (value, cnt) locals.(loc_level);
    let bc_new = {bc with locals}
    in
    for i = 0 to nlocs - 1 do
        if i <> loc_level then
            match Local.value locals.(i) with
            | None ->
                ()
            | Some term_n ->
                let term =
                    expand (term_of_term_n term_n bc_new) bc_new
                in
                locals.(i) <-
                    Local.set_value (term, cnt) locals.(i)
    done;
    {bc with locals}








module Unify =
struct
    type bc = t

    type t = {
        bc: bc;
        gamma: Gamma.t
    }

    let string_of_term (term: Term.t) (uc: t): string =
        Term_printer.string_of_term term uc.gamma
    let _ = string_of_term

    let delta (uc: t): int =
        Gamma.count uc.gamma - count uc.bc


    let down (typ: Term.typ) (uc: t): Term.typ option =
        Term.down (delta uc) typ

    let is_hole (idx: int) (uc: t): bool =
        is_hole (idx - delta uc) uc.bc

    let expand (term: Term.t) (uc: t): Term.t =
        let del = delta uc
        in
        Term.substitute
            (fun i ->
                if i < del then
                    Variable i
                else
                    match value (i - del) uc.bc with
                    | None ->
                        Variable i
                    | Some term ->
                        Term.up del term)
            term

    let push (tp: Term.typ) (uc: t): t =
        {uc with gamma = Gamma.push_local "_" tp uc.gamma}

    let unify
        (act: Term.typ)
        (req: Term.typ)
        (is_super: bool)
        (bc: bc)
        : bc option
        =
        let rec uni act req is_super uc =
            let nb = delta uc
            in
            let set i typ =
                Option.(
                    down typ uc
                    >>= fun typ0 ->
                    map
                        (fun uc ->
                            {uc with bc = fill_hole (i - nb) typ0 uc.bc})
                        (uni
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
                let iph = is_hole i uc
                and jph = is_hole j uc
                in
                if i = j then
                    Some uc
                else if i < nb || j < nb then
                    None
                else if not (iph || jph) then
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

            | Pi (act_arg, act_rt, _), Pi (req_arg, req_rt, _) ->
                Option.(
                    uni act_arg req_arg false uc
                    >>= fun uc ->
                    uni act_rt req_rt is_super (push act_arg uc)
                )

            | Pi (_, _, _), _ ->
                assert false

            | _, _ ->
                None
        in
        Option.map
            (fun uc -> uc.bc)
            (uni act req is_super {bc; gamma = bc.base})
end







let set_term (value: Term.t) (bc: t): t =
    match bc.stack with
    | Required_type _ :: rest ->
        {bc with stack = Built (value, count bc) :: rest}
    | _ ->
        assert false (* Illegal call! *)



let candidate (term: Term.t) (bc: t): t option =
    let act_typ = Gamma.type_of_term term bc.base
    and req_typ = required_type bc
    in
    Option.map
        (fun bc -> set_term term bc)
        (Unify.unify act_typ req_typ true bc)
        (*(unify req_typ true act_typ bc)*)




let base_candidate (term: Term.t) (bc: t): t option =
    let term =
        Term.up (count_locals bc) term
    in
    candidate term bc




let push_type (bc: t): t =
    (* Expecting a type as the next expression. *)
    {bc with
        stack = Required_type (Term.any_uni 1,0) :: bc.stack}




let push_typed (bc: t): t =
    (* Expecting a term whose required type is the last built expression. *)
    {bc with
        stack =
            match bc.stack with
            | Built typ_n :: _ ->
                Required_type typ_n :: bc.stack
            | _ ->
                assert false (* Illegal call! *)
    }




let make_typed (bc: t): Term.t * t =
    match bc.stack with
    | Built exp_n :: Built typ_n :: stack ->
        Term.Typed (
            term_of_term_n exp_n bc,
            term_of_term_n typ_n bc),
        {bc with stack}
    | _ ->
        assert false (* Illegal call! *)



let push_placeholder (uni: int) (bc: t): t =
    {bc with
        base =
            Gamma.push_local
                (placeholder_name (count_locals bc))
                Term.(any_uni uni)
                bc.base;

        locals = Array.push Local.hole bc.locals;
    }


let push_placeholder_for_term (uni: int) (bc: t): t =
    let bc = push_placeholder uni bc in
    {bc with
        stack =
            Required_type (Term.Variable 0, count bc)
            :: bc.stack
    }



let push_bound (name: string) (typed: bool) (typ: Term.typ) (bc: t): t =
    {bc with
        base = Gamma.push_local name typ bc.base;

        locals =
            Array.push
                (Local.make_bound (Array.length bc.bounds))
                bc.locals;

        bounds = Array.push (count bc, typed) bc.bounds;
    }



let start_function_application: t -> t =
    push_placeholder_for_term 1




let rec push_implicits (bc: t): t =
    match bc.stack with
    | Built f_n :: stack ->
        let open Gamma in
        let open Term in
        let f = term_of_term_n f_n bc in
        let tp = expand (type_of_term f bc.base) bc in
        (match key_normal tp bc.base with
            | Pi (arg_tp, res_tp, _ )
                when is_kind arg_tp bc.base
                    && has_variable 0 res_tp
                ->
                let name = placeholder_name (count_locals bc) in
                push_implicits
                    {bc with
                        base =
                            push_local name arg_tp bc.base;
                        locals =
                            Array.push Local.hole bc.locals;
                        stack =
                            Built
                                (Appl (up1 f,
                                       Variable 0,
                                       Application_info.Implicit),
                                 count bc.base + 1)
                            :: stack}
            | _ ->
                bc)
    | _ ->
        assert false (* Illegal call! *)




let push_argument (bc: t): t option =
    match bc.stack with
    | Built f_n :: _ ->
        let open Gamma in
        let open Term in
        let f = term_of_term_n f_n bc in
        let tp = expand (type_of_term f bc.base) bc in
        (match key_normal tp bc.base with
            | Pi (arg_tp, _, _ ) ->
                Some
                    {bc with
                        stack =
                            Required_type (arg_tp, count bc.base) :: bc.stack}
            | _ ->
                None)
    | _ ->
        assert false (* Illegal call! *)




let apply_argument (mode: Ast.Expression.argument_type) (bc: t): t =
    match bc.stack with
    | Built arg_n :: Built f_n :: stack ->
        let f =   expand (term_of_term_n f_n bc) bc
        and arg = expand (term_of_term_n arg_n bc) bc
        and mode =
            match mode with
            | Ast.Expression.Normal ->
                Term.Application_info.Normal
            | Ast.Expression.Operand ->
                Term.Application_info.Binary
        in
        {bc with
            stack =
                Built (Term.Appl (f, arg, mode), count bc)
                :: stack}
    | _ ->
        assert false (* Illegal call! *)



let start_binder (bc: t): t =
    {bc with
        binders = (count_bounds bc, count_locals bc) :: bc.binders}


let make_bound (level: int) (bc: t): Term.t * t =
    let cnt_base = count_base bc in
    assert (cnt_base <= level);
    assert (level < count bc);
    let bnd_level = level - cnt_base in
    Gamma.term_at_level
        (fst bc.bounds.(bnd_level))
        bc.base,
    bc



let check_bound (i: int) (nb: int) (bc: t): (t, unit) result =
    (* Check if the type of the i-th bound variable of the current binder, which
    has [nb] bound variables, is completely inferred.*)
    let module Result = Monad.Result (Unit) in
    let module Monadic = Term.Monadic ( Monad.Result (Unit) )
    in
    match bc.binders with
    | (_, cnt0) :: _ ->
        let level,_ = bc.bounds.(count_bounds bc - nb + i) in
        let cnt   = count bc in
        let typ   = expand (Gamma.type_at_level level bc.base) bc in
        Monadic.fold_free
            (fun idx bc ->
                if cnt - cnt0 <= idx then
                    Ok bc
                else
                    Error ())
            typ
            bc
    | _ ->
        assert false (* Illegal call! *)





let lambda_bound (_: t): t =
    assert false

let lambda_inner (_: t): t =
    assert false

let lambda_bound_typed (_: t): (t, Term.typ * t) result =
    assert false


let lambda_inner_typed (_: t): (t, Term.typ * t) result =
    assert false


let pi_bound (name: string) (bc: t): t =
    push_bound name false Term.(Variable 0) (push_placeholder 1 bc)


let pi_bound_typed (name: string) (bc: t): t =
    match bc.stack with
    | Built typ_n :: stack ->
        push_bound
            name
            true
            (term_of_term_n typ_n bc)
            {bc with stack}
    | _ ->
        assert false (* Illegal call! *)



let pi_make (bc: t): Term.typ * t =
    (* bounds = ... a:A, b:B, ...
       stack  = RT ...  *)
    match bc.stack, bc.binders with
    | Built res_tp_n             :: stack,
      (cnt_bounds0, cnt_locals0) :: binders
        ->
        let nb = Array.length bc.bounds - cnt_bounds0
        and cnt_locals_new = count_locals bc - cnt_locals0
        in
        let into nb tp =
            (* adapt references to bound variables into a new context. Must not
            contain any placeholders above [cnt_locals0], only to bound
            variables 0, ..., i-1 *)
            Term.substitute
                (fun idx ->
                    if cnt_locals_new <= idx then
                        Variable (idx + nb)
                    else
                        (let loc = local_of_index idx bc in
                         assert (Local.is_bound loc);
                         let bnd_no = Local.bound_number loc in
                         assert (bnd_no < nb);
                         Variable (Term.bruijn_convert bnd_no nb)))
                tp
        in
        let res_tp = expand (term_of_term_n res_tp_n bc) bc
        in
        let res =
            let rec make arg_no res_tp =
                if arg_no = nb then
                    into arg_no res_tp
                else
                    let res_tp = make (arg_no + 1) res_tp in
                    let open Term in
                    let level, typed = bc.bounds.(cnt_bounds0 + arg_no) in
                    let arg_tp =
                        into arg_no
                            (expand (Gamma.type_at_level level bc.base) bc)
                    and name = Gamma.name_at_level level bc.base
                    in
                    let mode =
                        if name = "_" then
                            Pi_info.arrow
                        else if typed then
                            Pi_info.typed name
                        else
                            Pi_info.untyped name
                    in
                    Pi (arg_tp, res_tp, mode)
            in
            make 0 res_tp
        in
        res,
        {bc with
            stack;
            binders}
    | _ ->
        assert false (* Illegal call! *)




let pop (bc: t): Term.t * t =
    match bc.stack with
    | Built res_n :: stack ->
        term_of_term_n res_n bc,
        {bc with stack}
    | _ ->
        assert false (* Illegal call! *)






let make (base: Gamma.t): t =
    push_placeholder_for_term
        2
        {base0 = base;
         base;
         locals = [||];
         bounds = [||];
         stack = [];
         binders = []}






let final (bc: t): Term.t * Term.typ * Gamma.t =
    match bc.stack with
    | [Built term_n] ->
        let term = expand (term_of_term_n term_n bc) bc in
        let typ  = expand (Gamma.type_of_term term bc.base) bc in
        let nlocs = count_locals bc
        in
        (match Term.down nlocs term, Term.down nlocs typ with
        | Some term, Some typ ->
            term, typ , bc.base0
        | _, _ ->
            let typ =
                Term.(substitute
                    (fun i ->
                        let term = Variable i in
                        if is_hole i bc then
                            Typed (
                                term,
                                expand (Gamma.type_of_term term bc.base) bc
                            )
                        else
                            term)
                    typ)
            in
            term, typ, bc.base
        )

    | _ ->
        assert false (* Illegal call! Not in final state. *)
