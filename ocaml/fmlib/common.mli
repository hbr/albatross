(** Identity function *)
val identity: 'a -> 'a

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
  val find_bwd: (char -> bool) -> int -> t -> int
  val list: t -> char list
  val of_list: char list -> t
  val length: t -> int
  val get: t -> int -> char
  val escaped: t -> t
  val sub: t -> int -> int -> t
  val concat: string -> string list -> string
  val split_on_char: char -> string -> string list
  val make: int -> char -> t
  val init: int -> (int -> char) -> t
end


module String_set: Set.S with type elt = String.t
module String_map: Finite_map.S with type key = String.t


module Interval:
sig
  (** [find p start beyond] returns [i] with [start <= i < beyond and p i] or
     [i = beyond] if no index in the interval satisfies the predicate [p]. *)
  val find: (int->bool) -> int -> int -> int


  (** [fold a f start beyond] starts with value [a] and folds the function [f]
     over the interval [start..beyond].

     {[fold a f start beyond =

          f (beyond - 1) (...  (f (start+1) (f start a))) ]} *)
  val fold: 'a -> (int -> 'a -> 'a) -> int -> int -> 'a


  module Monadic:
  functor (M:Common_module_types.MONAD) ->
  sig
    (** Like ordinary [fold], but uses the monad [M] to sequence the
       operations. *)
    val fold: 'a -> (int -> 'a -> 'a M.t) -> int -> int -> 'a M.t
  end
end


module Loop_state:
sig
  type ('a,'b) t =
    | More of 'a
    | Exit of 'b

  val more: 'a -> ('a,'b) t
  val exit: 'b -> ('a,'b) t
  val fold: ('a -> 'c) -> ('b -> 'c) -> ('a,'b) t -> 'c
end


module String_reader:
sig
  include Common_module_types.READABLE

  (** [of_string s] creates a readable structure of the string [s]. *)
  val of_string: string -> t

  (** [of_substring s start len] creates a readable structure of the substring
     of [s] starting at position [start] and having length [len]. *)
  val of_substring: string -> int -> int -> t
end

module Fill_reader:
sig
  include Common_module_types.READABLE

  (** [make n c] makes a character filler with [n] characters [c]. *)
  val make: int -> char -> t
end


module Char_reader:
sig
  include Common_module_types.READABLE

  (** [make c] makes a character reader with the character [c]. *)
  val make: char -> t
end




module type SEXP =
  sig
    type t =
      | Atom of string
      | Seq of t array
    val string: t -> string
  end

module Sexp: SEXP