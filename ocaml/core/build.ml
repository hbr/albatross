(** A core internal module to support term building. Do not use outside of core
    directly. *)


open Fmlib
open Module_types




module Make (Info: ANY) =
struct
    module Algo = Gamma_algo.Make (Gamma_holes)

    type name =
        Info.t * string


    type requirement =
        | Some_type


    type item = {
        requirement: requirement option;
        nargs: int;
        term: (Info.t * Term.t * Term.typ) option;
    }

    type binder = {
        info: Info.t;
        sort: Sort.t;
        name_map_previous: Name_map.t;
    }


    type t = {
        name_map: Name_map.t;
        gh: Gamma_holes.t;
        stack: item list;           (* terms under construction *)
        binders: binder list;       (* open binders *)
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
            stack = [];
            binders = [];
        }


    let empty: t =
        make Context.empty


    let count (bc: t): int =
        Gamma_holes.count bc.gh

    let count_base (bc: t): int =
        Gamma_holes.count_base bc.gh


    let string_of_term (term: Term.t) (bc: t): string =
        Term_printer.string_of_term
            term
            (Gamma_holes.context bc.gh)


    let push_item
            (requirement: requirement option)
            (nargs: int)
            (bc: t)
        : t
        =
        {bc with
         stack =
             {requirement; nargs; term = None} :: bc.stack}


    let sort_of_term (term: Term.typ): Sort.t =
        match term with
        | Sort sort ->
            sort
        | _ ->
            assert false (* term is not a sort *)

    let split_list (lst: 'a list): 'a * 'a list =
        match lst with
        | [] ->
            assert false (* Illegal call! *)
        | hd :: tl ->
            hd, tl


    let split_stack (bc: t): item * item list =
        split_list bc.stack

    let split_binders (bc: t): binder * binder list =
        split_list bc.binders


    let map_top (f: item -> item res): t -> t res =
        fun bc ->
        let top, stack = split_stack bc in
        Result.map
            (fun item -> {bc with stack = item :: stack})
            (f top)


    let get_top (bc: t): Term.t * Term.typ * item list =
        let item, stack = split_stack bc
        in
        match item.term with
        | None ->
            assert false (* Term construction not yet completed. *)
        | Some (_, term, typ) ->
            term, typ, stack



    let get_final (bc: t): Term.t * Term.typ =
        (* Get the term in the original context. *)
        let term, typ, stack = get_top bc
        in
        assert (stack = []);
        let cnt = count bc
        and cnt0 = count_base bc
        in
        match
            Term.down (cnt - cnt0) term,
            Term.down (cnt - cnt0) typ
        with
        | Some term, Some typ ->
            term, typ
        | _, _ ->
            assert false (* Term or type still contain some holes. *)


    let put_term
            (info: Info.t) (term: Term.t) (typ: Term.typ): t -> t res
        =
        fun bc ->
        map_top
            (fun item ->
                 assert (item.term = None);
                 let put _ =
                     Ok {item with term = Some (info, term, typ)}
                 in
                 match item.requirement with
                 | None ->
                     put ()
                 | Some req ->
                     match req with
                     | Some_type ->
                         (
                             match typ with
                             | Term.Sort _ ->
                                 put ()
                             | _ ->
                                 Error (info, Type_error.Not_a_type)
                         )
            )
            bc


    let make_sort (info: Info.t) (s: Sort.t) (bc: t): t res =
        let add =
            put_term
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


    let make_identifier (info: Info.t) (name: string): t -> t res =
        fun bc ->
        if name = "Proposition" then
            make_sort info Sort.Proposition bc
        else if name = "Any" then
            make_sort info (Sort.Any 0) bc
        else
            match Name_map.find name bc.name_map with
            | [] ->
                Error (info, Type_error.Name_not_found name)
            | [level] ->
                let typ = Gamma_holes.type_at_level level bc.gh
                and idx = Gamma_holes.index_of_level level bc.gh
                in
                put_term info (Term.Variable idx) typ bc
            | _ ->
                Error (info,
                       Type_error.Not_yet_implemented
                           "<name overloading>")


    let start_term: t -> t =
        (* Start a term without any requirements. *)
        push_item None 0


    let start_type: t -> t =
        (* Start the analysis of a type. *)
        push_item (Some Some_type) 0


    let start_application (_: t): t =
        assert false

    let start_argument (_: t): t =
        assert false

    let end_application (_: Info.t) (_: t): t res =
        assert false


    let start_binder ((info, name): name): t -> t =
        fun bc ->
        let item, stack = split_stack bc
        in
        match item.term with
        | None ->
            assert false (* Illegal call, type not yet constructed. *)
        | Some (_, typ, sort) ->
            let sort = sort_of_term sort
            in
            {name_map =
                 Name_map.add_local name bc.name_map;
             stack;
             gh =
                 Gamma_holes.push_bound name true typ bc.gh;
             binders =
                 {info; sort; name_map_previous = bc.name_map}
                 :: bc.binders}


    let end_pi (info: Info.t): t -> t res =
        fun bc ->
        let res_tp, res_sort, stack = get_top bc
        in
        let term = Gamma_holes.pi 1 res_tp bc.gh
        and gh = Gamma_holes.remove_bounds 1 bc.gh
        and res_sort = sort_of_term res_sort
        in
        let binder, binders = split_binders bc in
        let name_map = binder.name_map_previous
        in
        let typ = Term.Sort (Sort.pi_sort binder.sort res_sort)
        in
        let bc = {gh; stack; binders; name_map} in
        put_term info term typ bc
end
