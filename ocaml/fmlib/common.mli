(** Module to represent types which cannot be inhabited. *)
module Void:
sig
  type t
end


(** Module to represent the [unit] type. *)
module Unit:
sig
  type t = unit
end


(** Module to represent the [int] type. *)
module Int:
sig
  type t = int
  val compare: t -> t -> int
end



(** Module to represent the [float] type. *)
module Float:
sig
  type t = float
  val compare: t -> t -> int
end


module Either:
sig
  type ('a,'b) t =
    | Left of 'a
    | Right of 'b
  val left:  'a -> ('a,'b) t
  val right: 'b -> ('a,'b) t
end




module Char:
sig
  type t = char
  val code: t -> int
  val chr:  int -> t
  val compare: t -> t -> int
  val escaped: t -> string
  val is_lower: t -> bool
  val is_upper: t -> bool
  val is_letter: t -> bool
  val is_digit:  t -> bool
end



module String:
sig
  type t = string
  val compare: t -> t -> int
  val one: char -> t
  val find: (char -> bool) -> int -> t -> int
  val list: t -> char list
  val of_list: char list -> t
  val length: t -> int
  val get: t -> int -> char
  val escaped: t -> t
  val sub: t -> int -> int -> t
  val concat: string -> string list -> string
  val make: int -> char -> t
  val init: int -> (int -> char) -> t
end


module String_set: Set.S with type elt = String.t
module String_map: Finite_map.S with type key = String.t



module type SEXP =
  sig
    type t =
      | Atom of string
      | Seq of t array
    val string: t -> string
  end

module Sexp: SEXP


module Scan:
sig
  type ('token,'a) result =
    | More of ('token,'a) t
    | End of 'a
  and ('token,'a) t = 'token option -> ('token,'a) result
end


val identity: 'a -> 'a
