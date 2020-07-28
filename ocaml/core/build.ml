(** A core internal module to support term building. Do not use outside of core
    directly. *)


open Fmlib
open Module_types




module Make (Info: ANY) =
struct
    module Term_ts =
    struct
        type t = {
            term: Term.t;
            typ:  Term.t;
            info: Info.t;
            n: int;
        }

        let make term typ info n =
            {term; typ; info; n}

        let get (cnt: int) (term: t): Term.t * Term.typ =
            assert (cnt <= term.n);
            let delta = term.n - cnt
            in
            match Term.down delta term.term, Term.down delta term.typ with
            | Some term, Some typ ->
                term, typ
            | _, _ ->
                assert false (* Term not valid in base context. *)
    end



    type t = {
        name_map: Name_map.t;
        gh: Gamma_holes.t;
        terms: Term_ts.t Sequence.t;
        stack: int list;
    }

    type problem = Info.t * Type_error.t

    type 'a res = ('a, problem) result


    let make (context: Context.t): t =
        let gamma = Context.gamma context
        and name_map = Context.name_map context
        in
        {
            name_map;
            gh = Gamma_holes.make gamma;
            terms = Sequence.empty;
            stack = [];
        }


    let empty: t =
        make Context.empty


    let count (bc: t): int =
        Gamma_holes.count bc.gh

    let count_base (bc: t): int =
        Gamma_holes.count_base bc.gh


    let count_terms (bc: t): int =
        Sequence.length bc.terms


    let get_term (bc: t): Term.t * Term.typ =
        (* Get the term in the original context. *)
        match bc.stack with
        | [i] ->
            Term_ts.get
                (count_base bc)
                (Sequence.elem i bc.terms)
        | _ ->
            assert false (* Illegal. Final term not constructed. *)


    let add_term
            (info: Info.t) (term: Term.t) (typ: Term.typ) (bc: t)
        : t res
        =
        Ok (
            let cnt = count bc in
            { bc with
              terms =
                  Sequence.push
                      (Term_ts.make term typ info cnt)
                      bc.terms;
            }
        )

    let start_term (bc: t): t =
        (* Start a term without any requirements. *)
        {bc with
         stack = count_terms bc :: bc.stack;
        }


    let start_application (_: t): t =
        assert false

    let start_argument (_: t): t =
        assert false

    let end_application (_: Info.t) (_: t): t res =
        assert false



    module Construct =
    struct
        let sort (info: Info.t) (s: Sort.t) (bc: t): t res =
            let add =
                add_term
                    info
                    (Term.Sort s)
                    (Term.Sort (Sort.type_of s))
            in
            match s with
            | Sort.Proposition ->
                add bc
            | Sort.Any i ->
                if i > 0 then
                    Error (info, Type_error.Higher_universe i)
                else
                    add bc

        let identifier
                (info: Info.t) (name: string) (bc: t)
            : t res
            =
            if name = "Proposition" then
                sort info Sort.Proposition bc
            else if name = "Any" then
                sort info (Sort.Any 0) bc
            else
                Error (info, Type_error.Not_yet_implemented "<identifiers>")
    end

end
