type t = unit

let count_explicit_args (_: t): int =
  assert false (* nyi *)

let count_first_implicits (_: t): int =
  assert false (* nyi *)

let typ (_: t): Term.typ =
  assert false (* nyi *)
