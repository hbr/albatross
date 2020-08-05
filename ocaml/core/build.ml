(** A core internal module to support term building. Do not use outside of core
    directly.



    Basic Idea
    ==========


    There is a stack of to be built terms. When the construction of term starts,
    the term can get some type requirement.

    Invariant
    =========

    - Only terms which are welltyped in the context are constructed.

    - All terms on the stack are welltyped and satisfy their requirements or
      have still a chance to satisfy their requirement. The satisfaction of the
      requirements is checked by putting a term to the stack.


    Used Typing Rules
    =================

    Product
    -------

        Gamma  |- A: sA
        Gamma, x:A |- R: sR
        ----------------------------------------
        Gamma |- (all (x: A). R) : pi_sort(sA,sR)


        sA              sR              pi_sort(sA,sR)
        ----------------------------------------------
        *               Proposition     Proposition
        Proposition     Any(i)          Any(i)
        Any(i)          Any(j)          Any(max(i,j))


        A and R must be types. If this is satisfied, the product can be built in
        a typesafe manner.

        Generating the product term, it is checked, if A is a kind and if x
        occurs in R.

        First build A with the requirement of being a type. Then make a new
        binder (x:A). The build R with the requirement of being a type. Finally
        build all (x:A): R.


    Application
    -----------

        Gamma |- f: all (x: A). B
        Gamma |- a: A'
        Gamma |- A' <= A             -- subtype
        ----------------------------------------
        Gamma |- f a: B[x:=a]

        We start to build [f a] with a possible requirement which has to be
        satisfied after being applied to [nargs] arguments.

        [start_application] increments nargs by one. Then it builds [f]. The
        function term can only be built if its type is a product type.

        Then we start a new term with the required type [A] from the type of
        [f].



*)


open Fmlib
open Module_types
open Common


module Signature = Gamma_algo.Signature


module Make (Info: ANY) =
struct
    module Algo = Gamma_algo.Make (Gamma_holes)
    module Uni = Unifier.Make (Gamma_holes)

    type name =
        Info.t * string


    type requirement =
        | No_requirement
        | Some_type
        | Result_type of Term.typ




    type item = {
        requirement: requirement;
        satisfied: bool;
        nargs: int;
        term: (Info.t
               * Term.t
               * Signature.t
               * int  (* size of the context *)
               ) option;
    }

    type binder = {
        info: Info.t;
        sort: Sort.t;
        binder_level: int;
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


    let into_new_binder (idx: int) (term: Term.t): Term.t
        (* Put [term] which is welltyped in the current context into a new
           binder where [idx] is the index of the current binder to which is
           bound.

                gamma ... idx ... |- term
                                  ^
                                  cnt

           [idx] is no longer refereced in the new term. All referenced to [idx]
           are replace by 0 i.e. the new bound variable. All other variables
           have to be increased by one, because they have to escape the new
           binder.
        *)
        =
        Term.map
            (fun i ->
                 if i = idx then
                     0
                 else
                     i + 1)
            term



    let push_item
            (requirement: requirement)
            (nargs: int)
            (bc: t)
        : t
        =
        {bc with
         stack =
             {requirement; nargs; satisfied = false; term = None}
             ::
             bc.stack}


    let sort_of_term (term: Term.typ): Sort.t =
        match term with
        | Sort sort ->
            sort
        | _ ->
            assert false (* term is not a sort *)




    let split_stack (bc: t): item * item list =
        List.split_head_tail bc.stack


    let split_binders (bc: t): binder * binder list =
        List.split_head_tail bc.binders



    let map_top (f: item -> item res): t -> t res =
        fun bc ->
        let top, stack = split_stack bc in
        Result.map
            (fun item -> {bc with stack = item :: stack})
            (f top)




    let map_top0 (f: item -> item): t -> t =
        fun bc ->
        match map_top (fun item -> Ok (f item)) bc with
        | Ok bc ->
            bc
        | Error _ ->
            assert false (* Illegal call. *)



    let get_top (bc: t): Term.t * Term.typ * item list =
        let item, stack = split_stack bc
        in
        match item.term with
        | None ->
            assert false (* Cannot happen. Term construction not yet completed.
                         *)
        | Some (_, term, sign, n) ->
            assert (n <= count bc);
            let delta = count bc - n in
            Term.up delta term,
            Term.up delta (Signature.typ sign),
            stack



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
            (info: Info.t) (term: Term.t) (typ: Term.typ)
            (decr: int) (* decrement nargs *)
        : t -> t res
        =
        (* Check that welltyped [term] of [typ] satisfies the requirements. If
         * yes, put it as the new top term. Otherwise report an error. *)
        assert (decr = 0 || decr = 1);
        fun bc ->
        let sign = Algo.signature typ bc.gh
        and item, stack = split_stack bc
        in
        assert (decr <= item.nargs);
        let nargs_new = item.nargs - decr in
        let put bc =
            Ok {bc with
                stack =
                    {item with
                     nargs = nargs_new;
                     term =
                         Some (info, term, sign, count bc)}
                    ::
                    stack}
        in
        match item.requirement with
        | No_requirement ->
            put bc

        | Some_type ->
            if Signature.is_sort item.nargs sign then
                put bc
            else
                Error (info, Type_error.Not_a_type)

        | Result_type req_typ ->
            if nargs_new = 0 then
                match Uni.unify typ req_typ true bc.gh with
                | None ->
                    Error (
                        info,
                        Type_error.Wrong_type (
                            req_typ,
                            typ,
                            Gamma_holes.context bc.gh
                        ))
                | Some gh ->
                    put {bc with gh}
            else
                assert false (* nyi: multiargument application *)




    let check_naming_convention
            (info: Info.t) (name: string) (typ: Term.typ) (bc: t)
        : t res
        =
        let is_lower, is_upper =
            if String.length name > 0 then
                let c = name.[0] in
                Char.is_lower c, Char.is_upper c
            else
                false, false
        and tv fail =
            if not fail then
                Ok bc
            else
                Error (info, Type_error.Naming_type_variable)
        and no_tv fail =
            if not fail then
                Ok bc
            else
                Error (info, Type_error.Naming_no_type_variable)
        in
        match Algo.sort_of_kind typ bc.gh with
        | None ->
            (* proof or object, must be lower case or operator *)
            no_tv is_upper
        | Some Sort.Proposition ->
            (* must be lower case or operator *)
            no_tv is_upper
        | Some Sort.Any _ ->
            (* mus be upper case or operator *)
            tv is_lower




    let make_sort (info: Info.t) (s: Sort.t) (bc: t): t res =
        let add =
            put_term
                info
                (Term.Sort s)
                (Term.Sort (Sort.type_of s))
                0
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
                let level = Gamma_holes.adapted_level level bc.gh in
                let typ = Gamma_holes.type_at_level level bc.gh
                and idx = Gamma_holes.index_of_level level bc.gh
                in
                put_term info (Term.Variable idx) typ 0 bc
            | _ ->
                Error (info,
                       Type_error.Not_yet_implemented
                           "<name overloading>")




    let start_term: t -> t =
        (* Start a term without any requirements. *)
        push_item No_requirement 0




    let start_type: t -> t =
        (* Start the analysis of a type. *)
        push_item Some_type 0






    let start_application: t -> t =
        (* Start an application [f a]. The top term contains the requirement for
         * [f a]. In order to convert this into a requirement for [f], the
         * number of expected arguments has to be increased by one. *)
        map_top0
            (fun item ->
                 assert (item.term = None);
                 {item with nargs = item.nargs + 1})





    let start_argument (bc: t): t =
        (* The top term is a function term. Extract the argument type as a
         * requirement for the argument to be constructed. *)
        let item, _ = split_stack bc in
        assert (item.term <> None);
        assert (item.nargs > 0);
        let _, _, sign, n = Option.value item.term in
        let req_typ =
            Term.up
                (count bc - n)
                (Signature.argument_type sign)
        in
        push_item
            (Result_type req_typ)
            0
            bc





    let end_application (_: Info.t) (_: t): t res =
        (* The stack looks like
         *
         *      stack = ... f arg
         *
         *  [arg] is a valid argument for [f].
         *
         *
         *  1. Pop [arg]
         *
         *  2. Replace [f] by [f a] and reduce the number of expected arguments
         *     by one.
         *
         *  3. If the requirements for [f] had not yet been satisfied, check the
         *     requirements (if possible) or leave the requirements as not yet
         *     checked.
         *)
        assert false




    let start_binder ((info, name): name): t -> t res =
        fun bc ->
        let open Result in
        let typ, sort, stack = get_top bc in
        let sort = sort_of_term sort in
        check_naming_convention info name typ bc
        >>= fun _ ->
        Ok
            {name_map =
                 Name_map.add_local name bc.name_map;
             stack;
             gh =
                 Gamma_holes.push_bound name true typ bc.gh;
             binders =
                 {info;
                  sort;
                  name_map_previous = bc.name_map;
                  binder_level = count bc
                 }
                 ::
                 bc.binders
            }


    let end_pi (info: Info.t): t -> t res =
        (* Make [all (x:A): R] and put it on top of the stack.

           - [R] is on top of the stack.

           - [(x:A)] is the most recent binder.

           1. Get [x:A]

           2. Pop [R] and lift it into the new binder

           3. Pop the most recent binder

           4. Push [all (x:A): R] onto the stack
        *)
        fun bc ->
        let binder, binders = split_binders bc
        and res_typ, res_sort, stack = get_top bc
        in
        let arg_typ =
            Gamma_holes.type_at_level binder.binder_level bc.gh
        and arg_name =
            Gamma_holes.name_at_level binder.binder_level bc.gh
        and arg_idx =
            Gamma_holes.index_of_level binder.binder_level bc.gh
        in
        let kind = Algo.is_kind arg_typ bc.gh in
        (* MISSING: Check holes in [arg_typ]. As long as binders are fully
         * typed, there are no holes.
         *
         * If bound variable is untyped, check the naming conventions.
         *)
        put_term
            info
            (Term.make_product
                 arg_name
                 true (* is_typed *)
                 kind
                 arg_typ
                 (into_new_binder arg_idx res_typ))
            (Term.Sort
                 (Sort.pi_sort
                      binder.sort
                      (sort_of_term res_sort)))
            0
            {gh = Gamma_holes.pop_bound bc.gh;
             stack;
             binders;
             name_map = binder.name_map_previous}
end
