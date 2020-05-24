(* A pure representation of inductive types. *)


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


    let name header = header.name


    let has_index (header: t): bool =
        0 <> Array.length header.indices


    let kind (params: params) (header: t): Term.typ =
        Array.fold_right
            (fun (name, typ) res ->
                Term.(Pi (typ, res, Pi_info.typed name)))
            params
            header.kind


    let make name kind indices sort =
        {name; kind; indices = Array.of_list indices; sort}
end (* Header *)





module Constructor =
struct
    type t = {
        name: string;
        typ:  Term.typ; (* Valid in context with all types of the family and the
        parameters. *)
    }
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


type t = {
    params: params;

    types: Type.t array;
}

let make params types =
    {params; types}
