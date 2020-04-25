type t = unit (* DUMMY *)


let singleton (_: Term.t) (_: Gamma.t): t =
    ()


let add_unique (_: Term.t) (_: Gamma.t) (table: t): t option =
    Some table
