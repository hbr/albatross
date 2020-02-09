open Fmlib
open Common


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





type t = {
    base0: Gamma.t;
    base: Gamma.t;
    locals: Local.t array;
    bounds: (int * bool) array;          (* level of bound, is typed? *)
}



let make (base: Gamma.t): t =
    {base0 = base;
     base;
     locals = [||];
     bounds = [||]}




let count (gh: t): int =
    Gamma.count gh.base


let count_base (gh: t): int =
    Gamma.count gh.base0


let count_bounds (gh: t): int =
    Array.length gh.bounds


let count_locals (gh: t): int =
    Array.length gh.locals


let context (gh: t): Gamma.t =
    gh.base


let base_context (gh: t): Gamma.t =
    gh.base0


let index_of_level (level: int) (gh: t): int =
    Gamma.index_of_level level gh.base


let local_of_index (idx: int) (gh: t): Local.t =
    let nlocs = count_locals gh
    in
    assert (idx < nlocs);
    gh.locals.(Term.bruijn_convert idx nlocs)


let is_hole (idx: int) (gh: t): bool =
    idx < count_locals gh
    && Local.is_hole (local_of_index idx gh)



let is_bound (idx: int) (gh: t): bool =
    idx < count_locals gh
    && Local.is_bound (local_of_index idx gh)




let bound_number (idx: int) (gh: t): int =
    assert (is_bound idx gh);
    Local.bound_number (local_of_index idx gh)



let variable_of_bound (i: int) (gh: t): Term.t =
    assert (i < count_bounds gh);
    Term.Variable
            (index_of_level
                (fst gh.bounds.(i))
                gh)

let value (idx: int) (gh: t): Term.t option =
    let nlocs = count_locals gh
    in
    if nlocs <= idx then
        None
    else
        Option.map
            (fun (term, n) ->
                assert (n <= count gh);
                Term.up (count gh - n) term)
            (Local.value (local_of_index idx gh))



let has_value (idx: int) (gh: t): bool =
    Option.has (value idx gh)



let collect_holes (cnt0: int) (filled: bool) (term: Term.t) (gh: t): Int_set.t =
    let cnt = count gh
    and nlocs = count_locals gh
    in
    assert (cnt0 <= cnt);
    let nmin = min nlocs (cnt - cnt0)
    in
    Term.fold_free
        (fun idx set ->
            if nmin <= idx then
                set
            else
                let loc = local_of_index idx gh in
                if Local.is_hole loc && ((Local.value loc <> None) = filled) then
                    Int_set.add
                        (Gamma.level_of_index idx gh.base)
                        set
                else
                    set)
        term
        Int_set.empty




let unfilled_holes (cnt0: int) (term: Term.t) (gh: t): Int_set.t =
    collect_holes cnt0 false term gh




let expand (term: Term.t) (gh: t): Term.t =
    Term.substitute
        (fun i ->
            match value i gh with
            | None ->
                Variable i
            | Some term ->
                term)
        term


let is_expanded (term: Term.t) (gh: t): bool =
    Int_set.is_empty
        (collect_holes 0 true term gh)



let term_of_term_n ((term,n): Term.t_n) (gh: t): Term.t =
    expand (Term.up (count gh - n) term) gh





let type_at_level (level: int) (gh: t): Term.typ =
    let typ = Gamma.type_at_level level gh.base in
    if count_base gh <= level then
        expand typ gh
    else
        typ


let type_of_variable (idx: int) (gh: t): Term.typ =
    type_at_level (Gamma.level_of_index idx gh.base) gh



let name_at_level (level: int) (gh: t): string =
    Gamma.name_at_level level gh.base



let type_of_literal (value: Term.Value.t) (gh: t): Term.typ =
    Gamma.type_of_literal value gh.base



let definition_term (idx: int) (gh: t): Term.t option =
    Gamma.definition_term idx gh.base



let push_bound (name: string) (typed: bool) (typ: Term.typ) (gh: t): t =
    {gh with
        base = Gamma.push_local name typ gh.base;

        locals =
            Array.push
                (Local.make_bound (Array.length gh.bounds))
                gh.locals;

        bounds = Array.push (count gh, typed) gh.bounds;
    }



let push_local (name: string) (typ: Term.typ) (gh: t): t =
    push_bound name true typ gh



let push_hole (typ: Term.typ) (gh: t): t =
    let name = "<" ^ string_of_int (count_locals gh) ^ ">"
    in
    {gh with
        base   = Gamma.push_local name typ gh.base;
        locals = Array.push Local.hole gh.locals;
    }




let fill_hole (idx: int) (value: Term.t) (gh: t): t =
    let cnt    = count gh
    and nlocs  = count_locals gh
    and locals = Array.copy gh.locals
    in
    let loc_level = Term.bruijn_convert idx nlocs
    in
    locals.(loc_level) <-
        Local.set_value (value, cnt) locals.(loc_level);
    let gh_new = {gh with locals}
    in
    for i = 0 to nlocs - 1 do
        if i <> loc_level then
            match Local.value locals.(i) with
            | None ->
                ()
            | Some term_n ->
                let term =
                    expand (term_of_term_n term_n gh_new) gh_new
                in
                locals.(i) <-
                    Local.set_value (term, cnt) locals.(i)
    done;
    {gh with locals}





let into_binder
    (cnt0: int)
    (bnd0: int)
    (i: int)
    (tp: Term.typ)
    (gh: t)
    : Term.typ
    =
    (* Adapt references to bound variable into a binder. The type [tp] must not
    contain any holes above the level [cnt0], only to bound variables
    [0,1,...,i-1]. *)
    assert (cnt0 <= count gh);
    assert (bnd0 <= count_bounds gh);
    let cnt = count gh
    in
    Term.substitute
        (fun idx ->
            if cnt - cnt0 <= idx then
                Variable (idx + i)
            else (
                let loc = local_of_index idx gh in
                assert (Local.is_bound loc);
                let i_bnd = Local.bound_number loc in
                assert (bnd0 <= i_bnd);
                assert (i_bnd < bnd0 + i);
                Variable (Term.bruijn_convert (i_bnd - bnd0) i)))
        tp



let pi (cnt0: int) (bnd0: int) (res_tp: Term.typ) (gh: t): Term.typ =
    assert (0 <= bnd0);
    assert (bnd0 < count_bounds gh);
    let open Term
    in
    let nbounds = count_bounds gh - bnd0
    and into = into_binder cnt0 bnd0
    in
    let rec make i res_tp =
        if i = 0 then
            res_tp
        else
            let i = i - 1 in
            let name, typed, arg_tp =
                let level, typed = gh.bounds.(bnd0 + i) in
                name_at_level level gh,
                typed,
                into i (type_at_level level gh) gh
            in
            make
                i
                (Pi (
                        arg_tp,
                        res_tp,
                        if name = "_" then
                            Pi_info.arrow
                        else if typed then
                            Pi_info.typed name
                        else
                            Pi_info.untyped name))
    in
    make
        nbounds
        (into nbounds (expand res_tp gh) gh)







let lambda (_: int) (_: int) (_: Term.t) (_: t): Term.t =
    assert false
