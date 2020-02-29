open Fmlib
open Common

module Algo = Gamma_algo.Make (Gamma_holes)
module Uni  = Unifier.Make (Gamma_holes)


module Stack =
struct
    let split (stack: 'a list): 'a * 'a list =
        match stack with
        | [] ->
            assert false (* Illegal call! *)
        | hd :: tl ->
            hd, tl
end


type entry = {
    cnt0: int;
    bnd0: int;
}

type t = {
    gh: Gamma_holes.t;
    sp: int;
    stack: int list;
    entry: entry;
    entries: entry list;
}


let index_of_level (level: int) (bc: t): int =
    Gamma_holes.index_of_level level bc.gh


let string_of_term (term: Term.t) (bc: t): string =
    Term_printer.string_of_term term (Gamma_holes.context bc.gh)
let _ = string_of_term



let count (bc: t): int =
    Gamma_holes.count bc.gh

let count_base (bc: t): int =
    Gamma_holes.count_base bc.gh


let count_locals (bc: t): int =
    Gamma_holes.count_locals bc.gh


let count_bounds (bc: t): int =
    Gamma_holes.count_bounds bc.gh


let type_at_level (level: int) (bc: t): Term.typ =
    Gamma_holes.type_at_level level bc.gh


let type_of_term (term: Term.t) (bc: t): Term.typ =
    Algo.type_of_term term bc.gh



let required_type (bc: t): Term.typ =
    type_at_level bc.sp bc



let term_at_level (level: int) (bc: t): Term.t =
    Gamma_holes.expand
        (Term.Variable (index_of_level level bc))
        bc.gh

let top_term (bc: t): Term.t =
    term_at_level bc.sp bc




let add_implicits
    (_: Term.t) (_: Term.typ) (_:t)
    : Term.t * Term.typ * t
    =
    assert false




let unify (act: Term.typ) (req: Term.typ) (bc: t): t option =
    Option.map
        (fun gh -> {bc with gh})
        (Uni.unify act req true bc.gh)



let set_term (term: Term.t) (bc: t): t =
    {bc with
        gh =
            Gamma_holes.fill_hole (index_of_level bc.sp bc) term bc.gh}



let make (gamma: Gamma.t): t =
    let cnt0 = Gamma.count gamma in
    {
        gh =
            Gamma_holes.(
                make gamma
                |> push_hole Term.(any_uni 2)
                |> push_hole Term.(Variable 0)
            );

        sp = cnt0 + 1;

        stack = [];

        entry = {
            cnt0;
            bnd0 = 0;
        };

        entries = [];
   }


let final
    (bc: t)
    : (Term.t * Term.typ, Term.t list * Term.t * Term.typ * Gamma.t) result
    =
    let cnt0 = count_base bc
    and nlocs = count_locals bc in
    assert (bc.stack = []);
    assert (bc.entries = []);
    assert (bc.sp = cnt0 + 1);
    let term = top_term bc in
    let typ  = type_of_term term bc in
    match Term.down nlocs term, Term.down nlocs typ with
    | Some term, Some typ ->
        Ok (term, typ)
    | _ ->
        assert false (* nyi: find the unresolved holes. *)




let candidate (term: Term.t) (nargs: int) (bc: t): t option =
    let tp = type_of_term term bc in
    if 0 < nargs then
        let term, tp, bc = add_implicits term tp bc in
        Option.map
            (set_term term)
            (unify tp (required_type bc) bc)
    else
        (* Missing: adding of implicit arguments!!! *)
        Option.map
            (set_term term)
            (unify tp (required_type bc) bc)



let base_candidate
    (term: Term.t)
    (nargs: int)
    (bc: t)
    : t option
    =
    let term = Term.up (count_locals bc) term in
    candidate term nargs bc



let bound (ibound: int) (nargs: int) (bc: t): (t, Term.typ) result =
    match
        candidate (Gamma_holes.variable_of_bound ibound bc.gh) nargs bc
    with
    | None ->
        Error (required_type bc)
    | Some bc ->
        Ok bc



module Product =
(* ... A: Any1, x: A, B: Any1, y: B, ... , RT: Any1 *)
struct
    let start (bc: t): t =
        let cnt0 = count bc
        and bnd0 = count_bounds bc
        in
        {
            gh = Gamma_holes.push_hole Term.(any_uni 1) bc.gh;

            stack = bc.sp :: bc.stack;

            sp = cnt0;

            entries = bc.entry :: bc.entries;

            entry = {cnt0; bnd0}
        }

    let next (name: string) (typed: bool) (bc: t): t =
        let cnt0 = count bc
        and tp = top_term bc
        in
        {bc with
            gh = Gamma_holes.(
                push_bound name typed tp bc.gh
                |> push_hole Term.(any_uni 1)
            );

            stack = bc.sp :: bc.stack;

            sp = cnt0 + 1
        }

    let end_ (nargs: int) (bc: t): (t, int) result =
        let res = top_term bc
        and arg_tps, stack =
            let rec args nargs stack tps =
                if nargs = 0 then
                    tps, stack
                else
                    let sp, stack = Stack.split stack in
                    args (nargs - 1) stack (term_at_level sp bc :: tps)
            in
            args nargs bc.stack []
        in
        let rec find_incomplete i tps =
            if i = nargs then
                None
            else
                let tp, tps = Stack.split tps in
                if Int_set.is_empty
                    (Gamma_holes.unfilled_holes bc.entry.cnt0 tp bc.gh)
                then
                    find_incomplete (i + 1) tps
                else
                    Some i
        in
        match find_incomplete 0 arg_tps with
        | Some i ->
            Error i
        | None ->
            let sp, stack = Stack.split stack in
            let tp = Gamma_holes.pi bc.entry.cnt0 bc.entry.bnd0 res bc.gh in
            let entry, entries = Stack.split bc.entries in
            Ok (set_term tp
                    {   gh = Gamma_holes.remove_bounds nargs bc.gh;
                        sp;
                        stack;
                        entry;
                        entries})
end
