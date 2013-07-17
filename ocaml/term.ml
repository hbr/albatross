open Type

type term =
    Variable    of int
  | Application of term * term
  | Lambda      of typ * term

