module type ANY =
  sig
    type t
  end



module Either:
sig
  type ('a,'b) t =
    | Left of 'a
    | Right of 'b
  val left:  'a -> ('a,'b) t
  val right: 'b -> ('a,'b) t
end


module Char_:
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



module String_:
sig
  type t = string
  val one: char -> t
  val find: (char -> bool) -> int -> t -> int
  val list: t -> char list
  val of_list: char list -> t
end



module List_:
sig
  type 'a t = 'a list
  val find: ('a -> bool) ->'a t -> 'a option
end



module type SEXP =
  sig
    type t =
      | Atom of string
      | Seq of t array
    val string: t -> string
  end

module Sexp: SEXP
