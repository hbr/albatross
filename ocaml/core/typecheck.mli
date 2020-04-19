module Problem:
sig
    type t =
    | Out_of_bound of int * Gamma.t
    | Argument_type
    | Typed
    | Lambda
    | No_type
    | Name of string
end

type path = int list



val is_valid_context: Gamma.t -> bool
(**
    [is_valid_context gamma]

    Is the context [gamma] wellformed?
*)



val check: Term.t -> Gamma.t -> (Term.typ, path * Problem.t) result
(**
    [check term gamma]

    Verify if [term] is welltyped in the valid context [gamma]. If yes,
    return its type.

    Precondition:
    {[is_valid_context gamma]}
*)

