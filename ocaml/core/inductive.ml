(* A pure representation of inductive types. *)

open Fmlib


type params = (string * Term.typ) array


module Header =
struct
    type t = {
        name: string;
        kind:  Term.typ; (* only indices, valid in a context with parameters *)
        indices: (Term.Pi_info.t * Term.typ) array; (* kind arguments *)
        sort:  Term.Sort.t;
    }
    (* [indices] and [sort] represent the normalized version of [kind]*)


    let make name kind indices sort =
        {name; kind; indices = Array.of_list indices; sort}


    let name header = header.name


    let count_indices (header: t): int =
        Array.length header.indices

    let has_index (header: t): bool =
        0 <> count_indices header


    let kind (params: params) (header: t): Term.typ =
        Array.fold_right
            (fun (name, typ) res ->
                Term.(Pi (typ, res, Pi_info.typed name)))
            params
            header.kind


    let is_well_constructed
        (i: int)
        (params: params)
        (headers: t array)
        (nargs: int)
        (typ: Term.typ)
        : bool
    =
        (* Check that [typ] has the form [I p1 p2 ... i1 i2 ...] where [I]
        corresponds to the [i]th inductive type, [p1 p2 ...] are the parameters
        and [i1 i2 ... ] are the indices. *)
        let open Term in
        let nparams = Array.length params
        and ntypes  = Array.length headers
        and f, params_index = split_application typ in
        let params_index = Array.of_list params_index
        in
        let inductive_variable =
            Variable (bruijn_convert i (ntypes + nparams + nargs))
        and param_variable k =
            Variable (bruijn_convert k (nparams + nargs))
        in
        f = inductive_variable
        &&
        Common.Interval.forall
            (fun k ->
                assert (k < Array.length params_index);
                param_variable k = fst params_index.(k)
            )
            0 nparams
end (* Header *)





module Constructor =
struct
    type t = {
        name: string;
        typ:  Term.typ; (* Valid in context with all types of the family and the
        parameters. *)
    }

    let make name typ =
        {name; typ}
end




module Type =
struct
    type t = {
        nprevious: int; (* number of previous constructors *)
        header: Header.t;
        constructors: Constructor.t array;
    }

    let make nprevious header constructors =
        {nprevious; header; constructors}
end (* Type *)


let default_type
    (i:int) (params: params) (headers: Header.t array)
    : Term.typ
=
    (* Valid in a context with the types and the parameters. *)
    let nparams = Array.length params
    and ntypes  = Array.length headers
    in
    let rec make k typ =
        if k = nparams then
            typ
        else
            make
                (k + 1)
                Term.(
                    application
                        typ
                        (Variable (bruijn_convert k nparams))
                )
    in
    make 0 Term.(Variable (bruijn_convert i ntypes + nparams))


type t = {
    params: params;

    types: Type.t array;
}

let make params types =
    {params; types}
