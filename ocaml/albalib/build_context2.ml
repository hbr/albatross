
module Algo = Gamma_algo.Make (Gamma_holes)
module Uni  = Unifier.Make (Gamma_holes)



type t = {
    gh: Gamma_holes.t;
    sp: int;
}


let index_of_level (level: int) (bc: t): int =
    Gamma_holes.index_of_level level bc.gh


let count_base (bc: t): int =
    Gamma_holes.count_base bc.gh


let count_locals (bc: t): int =
    Gamma_holes.count_locals bc.gh


let type_at_level (level: int) (bc: t): Term.typ =
    Gamma_holes.type_at_level level bc.gh


let type_of_term (term: Term.t) (bc: t): Term.typ =
    Algo.type_of_term term bc.gh



let required_type (bc: t): Term.typ =
    type_at_level bc.sp bc



let top_term (bc: t): Term.t =
    Gamma_holes.expand (Term.Variable (index_of_level bc.sp bc)) bc.gh




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
   }


let final
    (bc: t)
    : (Term.t * Term.typ, Term.t list * Term.t * Term.typ * Gamma.t) result
    =
    let cnt0 = count_base bc
    and nlocs = count_locals bc in
    assert (bc.sp = cnt0 + 1);
    let term = top_term bc in
    let typ  = type_of_term term bc in
    match Term.down nlocs term, Term.down nlocs typ with
    | Some term, Some typ ->
        Ok (term, typ)
    | _ ->
        assert false (* nyi: find the unresolved holes. *)



let base_candidate
    (term: Term.t)
    (nargs: int)
    (bc: t)
    : t option
    =
    (*
    *)
    let term = Term.up (count_locals bc) term in
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
