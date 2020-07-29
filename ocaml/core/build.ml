(** A core internal module to support term building. Do not use outside of core
    directly. *)


open Fmlib
open Module_types




module Make (Info: ANY) =
struct

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



    let map_top (f: item -> item res): t -> t res =
        fun bc ->
        match bc.stack with
        | [] ->
            assert false (* Illegal call. *)
        | top :: stack ->
            Result.map
                (fun item -> {bc with stack = item :: stack})
                (f top)


    let get_term (bc: t): Term.t * Term.typ =
        (* Get the term in the original context. *)
        match bc.stack with
        | [item] ->
            (
                match item.term with
                | None ->
                    assert false (* Term construction not yet completed. *)
                | Some (_, term, typ) ->
                    term, typ
            )
        | _ ->
            assert false (* Illegal. Final term not constructed. *)


    let put_term
            (info: Info.t) (term: Term.t) (typ: Term.typ): t -> t res
        =
        fun bc ->
        map_top
            (fun item ->
                 assert (item.term = None);
                 let put _ =
                     Printf.printf "new %s: %s\n"
                         (string_of_term term bc)
                         (string_of_term typ bc);
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
            | [idx] ->
                let typ = Gamma_holes.type_of_variable idx bc.gh
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
        match bc.stack with
        | [] ->
            assert false (* Illegal call! *)
        | item :: stack ->
            match item.term with
            | None ->
                assert false (* Illegal call, type not yet constructed. *)
            | Some (_, typ, _) ->
                {name_map =
                     Name_map.add_local name bc.name_map;
                 stack;
                 gh =
                     Gamma_holes.push_bound name true typ bc.gh;
                 binders =
                     {info} :: bc.binders}


    let end_pi (_: Info.t): t -> t res =
        fun _ -> assert false
end
