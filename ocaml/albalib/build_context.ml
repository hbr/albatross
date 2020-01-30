open Fmlib


type term_n = Term.t * int

module Local =
struct
    type t = {
        value: term_n option;
    }

    let make: t =
        {value = None;}

    let has_value (loc: t): bool =
        Option.has loc.value

    let value (loc: t): term_n option =
        loc.value

    let set_value (term_n: term_n) (_: t): t =
        {value = Some term_n}
end



type entry =
    | Required_type of term_n
    | Built of term_n



type t = {
    base0: Gamma.t;
    base: Gamma.t;
    locals: Local.t array;
    stack: entry list;
}


let count (bc: t): int =
    Gamma.count bc.base


let count_locals (bc: t): int =
    Array.length bc.locals



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




let is_inferable (idx: int) (bc: t): bool =
    idx < count_locals bc



let has_value (idx: int) (bc: t): bool =
    Local.has_value (local_of_index idx bc)



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




let set_inferable (idx: int) (value: Term.t) (bc: t): t =
    let cnt    = count bc
    and nlocs  = count_locals bc
    and locals = Array.copy bc.locals
    in
    let loc_level = Term.bruijn_convert idx nlocs
    in
    locals.(loc_level) <-
        Local.set_value (value, cnt) locals.(loc_level);
    {bc with locals}



let expand (term: Term.t) (bc: t): Term.t =
    Term.substitute
        (fun i ->
            match value i bc with
            | None ->
                Variable i
            | Some term ->
                term)
        term




let unify
    (req: Term.typ)     (* required type *)
    (is_super: bool)    (* required type can be supertype of actual type?  *)
    (act: Term.typ)     (* actual type *)
    (bc: t): t option
    =
    let rec uni req is_super act bc =
        let set_inferable i term =
            Option.map
                (set_inferable i term)
                (uni
                    (Gamma.type_of_variable i bc.base)
                    true
                    (Gamma.type_of_term term bc.base)
                    bc)
        in
        let req = Gamma.key_normal req bc.base
        and act = Gamma.key_normal act bc.base
        in
        let open Term
        in
        match req, act with
        | Sort req, Sort act
            when (is_super && Sort.is_super req act)
                 || (not is_super && req = act)
            ->
                Some bc

        | Variable ireq, Variable iact
            when is_inferable ireq bc && is_inferable iact bc
            ->
                assert false (* nyi *)

        | Variable i, _ when is_inferable i bc ->
            assert (not (has_value i bc));
            set_inferable i act

        | _, Variable j when is_inferable j bc ->
            assert false (* nyi *)

        | Variable i, Variable j when i = j ->
            Some bc

        | Typed (req, _), Typed (act, _) ->
            uni req is_super act bc

        | Appl _, Appl _ ->
            assert false (* nyi *)

        | Pi _, Pi _ ->
            assert false (* nyi *)

        | Lambda _, Lambda _ ->
            assert false (* nyi *)

        | Value _, _ | _, Value _ ->
            assert false (* Illegal call! [req] and [act] are no types! *)

        | _, _ ->
            None
    in
    uni (expand req bc) is_super (expand act bc) bc





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
        (unify req_typ true act_typ bc)




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





let push_any (uni: int) (bc: t): t =
    let cnt = count bc
    in
    {bc with
        base =
            Gamma.push_local
                (placeholder_name cnt)
                Term.(any_uni uni)
                bc.base;

        locals = Array.push Local.make bc.locals;

        stack = Required_type (Term.Variable 0, cnt + 1) :: bc.stack
    }



let start_function_application: t -> t =
    push_any 1




let rec push_implicits (bc: t): t =
    match bc.stack with
    | Built f_n :: stack ->
        let open Gamma in
        let open Term in
        let f = term_of_term_n f_n bc in
        let tp = type_of_term f bc.base in
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
                            Array.push Local.make bc.locals;
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
        let tp = type_of_term f bc.base in
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
        let f =   term_of_term_n f_n   bc
        and arg = term_of_term_n arg_n bc
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







let pop (bc: t): Term.t * t =
    match bc.stack with
    | Built res_n :: stack ->
        term_of_term_n res_n bc,
        {bc with stack}
    | _ ->
        assert false (* Illegal call! *)






let make (base: Gamma.t): t =
    push_any 2 {base0 = base; base; locals = [||]; stack = []}






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
                        if is_inferable i bc then
                            Typed (
                                term,
                                expand (Gamma.type_of_term term bc.base) bc
                            )
                        else
                            term)
                    typ)
            in
            Printf.printf "final\n%s\n\n" (string_of_term typ bc);
            term, typ, bc.base
        )

    | _ ->
        assert false (* Illegal call! Not in final state. *)
