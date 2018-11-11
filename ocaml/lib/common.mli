module Ocaml_char = Char
module Ocaml_string = String
module Ocaml_list = List



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
  val one: char -> t
  val find: (char -> bool) -> int -> t -> int
  val list: t -> char list
  val of_list: char list -> t
  val length: t -> int
  val get: t -> int -> char
  val escaped: t -> t
  val make: int -> char -> t
end



module List:
sig
  type 'a t = 'a list
  val find: ('a -> bool) ->'a t -> 'a option
  val append: 'a list -> 'a list -> 'a list
  val rev_append: 'a list -> 'a list -> 'a list
  val rev: 'a t -> 'a t
  val length: 'a t -> int
  val fold_left: ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val concat: 'a list list -> 'a list
  val map : ('a -> 'b) -> 'a list -> 'b list
  val mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
  val rev_map : ('a -> 'b) -> 'a list -> 'b list
  val for_all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool

  module Monadic (M:Monad.MONAD):
  sig
    val fold_left:  ('a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
    val foldi_left: (int -> 'a -> 'b -> 'b M.t) -> 'a t -> 'b -> 'b M.t
  end
end



module type SEXP =
  sig
    type t =
      | Atom of string
      | Seq of t array
    val string: t -> string
  end

module Sexp: SEXP
