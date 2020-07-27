(** Description of a type error *)


type t =
  | Higher_universe of int
  | Not_yet_implemented of string
