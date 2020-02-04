open Fmlib
open Common


module Algo = Gamma_algo.Make (Gamma_holes)
module Uni  = Unifier.Make (Gamma_holes)


type entry =
    | Required_type of Term.typ_n
    | Built of Term.t_n



type t = {
    gh: Gamma_holes.t;
    stack: entry list;
    binders: (int * int) list; (* start bound, start level *)
}



let count (bc: t): int =
    Gamma_holes.count bc.gh

let count_base (bc: t): int =
    Gamma_holes.count_base bc.gh

let count_locals (bc: t): int =
    count bc - count_base bc

let count_bounds (bc: t): int =
    Gamma_holes.count_bounds bc.gh

let base (bc: t): Gamma.t =
    Gamma_holes.context bc.gh



let top_of_stack (bc: t): entry =
    match bc.stack with
    | top :: _ ->
        top
    | _ ->
        assert false (* Illegal call! *)



let string_of_term (term: Term.t) (bc: t): string =
    Term_printer.string_of_term
        term
        (Gamma_holes.context bc.gh)

let _ = string_of_term




let term_of_term_n (tn: Term.t_n) (bc: t): Term.t =
    Gamma_holes.term_of_term_n tn bc.gh


let type_of_term (term: Term.t) (bc: t): Term.typ =
    Algo.type_of_term term bc.gh


let key_normal (term: Term.t) (bc: t): Term.t =
    Algo.key_normal term bc.gh


let is_kind (typ: Term.typ) (bc: t): bool =
    Algo.is_kind typ bc.gh



let required_type (bc: t): Term.typ =
    match top_of_stack bc with
    | Required_type (term_n) ->
        term_of_term_n term_n bc
    | _ ->
        assert false (* Illegal call! *)




let built_type (bc: t): Term.typ =
    match top_of_stack bc with
    | Built (term_n) ->
        type_of_term (term_of_term_n term_n bc) bc
    | _ ->
        assert false (* Illegal call! *)









let set_term (value: Term.t) (bc: t): t =
    match bc.stack with
    | Required_type _ :: rest ->
        {bc with stack = Built (value, count bc) :: rest}
    | _ ->
        assert false (* Illegal call! *)


let unify (act: Term.typ) (req: Term.typ) (is_super: bool) (bc: t): t option =
    Option.map
        (fun gh -> {bc with gh})
        (Uni.unify act req is_super bc.gh)




let push_hole (uni: int) (bc: t): t =
    {bc with
        gh =
            Gamma_holes.push_hole Term.(any_uni uni) bc.gh}


let push_hole_for_term (uni: int) (bc: t): t =
    let bc = push_hole uni bc in
    {bc with
        stack =
            Required_type (Term.Variable 0, count bc)
            :: bc.stack
    }



let push_bound (name: string) (typed: bool) (typ: Term.typ) (bc: t): t =
    {bc with
        gh =
            Gamma_holes.push_bound name typed typ bc.gh}




let candidate (term: Term.t) (bc: t): t option =
    let act_typ = type_of_term term bc
    and req_typ = required_type bc
    in
    Option.map
        (fun bc -> set_term term bc)
        (unify act_typ req_typ true bc)




let receive_candidate (term: Term.t) (bc: t): (t, Term.typ * t) result =
    let act_typ = type_of_term term bc
    and req_typ = required_type bc
    in
    match unify act_typ req_typ true bc with
    | None ->
        Error (req_typ, bc)
    | Some bc ->
        Ok (set_term term bc)




let receive_base_candidate (term: Term.t) (bc: t): t option =
    match
        receive_candidate
            (Term.up (count_locals bc) term)
            bc
    with
    | Ok bc ->
        Some bc
    | _ ->
        None





let expect_type (bc: t): t =
    (* Expecting a type as the next expression. *)
    {bc with
        stack = Required_type (Term.any_uni 1,0) :: bc.stack}




let expect_typed (bc: t): t =
    (* Expecting a term whose required type is the last built expression. *)
    {bc with
        stack =
            match bc.stack with
            | Built typ_n :: _ ->
                Required_type typ_n :: bc.stack
            | _ ->
                assert false (* Illegal call! *)
    }


let expect_untyped (bc: t): t =
    push_hole_for_term 1 bc




let make_typed (bc: t): Term.t * t =
    match bc.stack with
    | Built exp_n :: Built typ_n :: stack ->
        Term.Typed (
            term_of_term_n exp_n bc,
            term_of_term_n typ_n bc),
        {bc with stack}
    | _ ->
        assert false (* Illegal call! *)



let expect_function (_: int):  t -> t =
    push_hole_for_term 1




let rec push_implicits (bc: t): t =
    match bc.stack with
    | Built f_n :: stack ->
        let open Term in
        let f = term_of_term_n f_n bc in
        let tp = type_of_term f bc in
        (match key_normal tp bc with
            | Pi (arg_tp, res_tp, _ )
                when is_kind arg_tp bc
                    && has_variable 0 res_tp
                ->
                push_implicits
                    {bc with
                        gh =
                            Gamma_holes.push_hole arg_tp bc.gh;
                        stack =
                            Built
                                (Appl (up1 f,
                                       Variable 0,
                                       Application_info.Implicit),
                                 count bc + 1)
                            :: stack}
            | _ ->
                bc)
    | _ ->
        assert false (* Illegal call! *)




let push_argument (bc: t): t option =
    match bc.stack with
    | Built f_n :: _ ->
        let open Term in
        let f = term_of_term_n f_n bc in
        let tp = type_of_term f bc in
        (match key_normal tp bc with
            | Pi (arg_tp, _, _ ) ->
                Some
                    {bc with
                        stack =
                            Required_type (arg_tp, count bc) :: bc.stack}
            | _ ->
                None)
    | _ ->
        assert false (* Illegal call! *)




let apply_argument (mode: Ast.Expression.argument_type) (bc: t): t =
    match bc.stack with
    | Built arg_n :: Built f_n :: stack ->
        let f =   term_of_term_n f_n bc
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



let start_binder (bc: t): t =
    {bc with
        binders = (count_bounds bc, count bc) :: bc.binders}


let make_bound (level: int) (bc: t): Term.t * t =
    let cnt_base = count_base bc in
    assert (cnt_base <= level);
    assert (level < count bc);
    let ibnd = level - cnt_base in
    Gamma_holes.variable_of_bound ibnd bc.gh,
    bc



let check_bound (i: int) (_: int) (bc: t): (t, unit) result =
    (* Check if the type of the i-th bound variable of the current binder is
    completely inferred.*)
    let module Result = Monad.Result (Unit) in
    let module Monadic = Term.Monadic ( Monad.Result (Unit) )
    in
    match bc.binders with
    | (bnd0, cnt0) :: _ ->
        let typ =
            type_of_term
                (Gamma_holes.variable_of_bound (bnd0 + i) bc.gh)
                bc
        in
        if Gamma_holes.unfilled_holes cnt0 typ bc.gh = [] then
            Ok bc
        else
            Error ()
    | _ ->
        assert false (* Illegal call! *)





let lambda_bound (name: string) (bc: t): t =
    push_hole 1 bc
    |> push_bound name false Term.(Variable 0)


let lambda_bound_typed (_: string) (_: t): (t, Term.typ * t) result =
    assert false


let lambda_inner_typed (bc: t): t =
    match bc.stack with
    | Built exp :: Built typ :: stack ->
        {bc with stack =
            Built
             (Term.Typed (term_of_term_n exp bc, term_of_term_n typ bc),
              count bc)
            :: stack}
    | _ ->
        assert false (* Illegal call! *)


let pi_bound (name: string) (bc: t): t =
    lambda_bound name bc


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
    | Built res_tp_n :: stack,
      (bnd0, cnt0)   :: binders
        ->
        Gamma_holes.pi cnt0 bnd0 (term_of_term_n res_tp_n bc) bc.gh,
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
    push_hole_for_term
        2
        {gh = Gamma_holes.make base;
         stack = [];
         binders = []}






let final (bc: t): Term.t * Term.typ * Gamma.t =
    match bc.stack with
    | [Built term_n] ->
        let term = term_of_term_n term_n bc in
        let typ  = type_of_term term bc in
        let nlocs = count_locals bc
        in
        (match Term.down nlocs term, Term.down nlocs typ with
        | Some term, Some typ ->
            term, typ , Gamma_holes.base_context bc.gh
        | _, _ ->
            term, typ, Gamma_holes.context bc.gh
        )

    | _ ->
        assert false (* Illegal call! Not in final state. *)
