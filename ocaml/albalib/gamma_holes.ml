open Fmlib


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


let term_of_term_n ((term,n): term_n) (gh: t): Term.t =
    Term.up (count gh - n) term



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



let level_of_bound (i: int) (gh: t): int =
    assert (i < count_bounds gh);
    fst gh.bounds.(i)



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


let unfilled_holes (_: int) (_: Term.t) (_: t): int list =
    assert false



let expand (term: Term.t) (gh: t): Term.t =
    Term.substitute
        (fun i ->
            match value i gh with
            | None ->
                Variable i
            | Some term ->
                term)
        term


let is_expanded (_: Term.t) (_: t): bool =
    assert false



let type_of_variable (idx: int) (gh: t): Term.typ =
    let typ = Gamma.type_of_variable idx gh.base
    in
    if idx < count_locals gh then
        expand typ gh
    else
        typ



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


let pi (_: int) (_: int) (_: Term.typ) (_: t): Term.typ =
    assert false


let lambda (_: int) (_: int) (_: Term.t) (_: t): Term.t =
    assert false
