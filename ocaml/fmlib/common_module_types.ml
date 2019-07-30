module type ANY =
  sig
    type t
  end



module type SORTABLE =
  sig
    include ANY
    val compare: t -> t -> int
  end



module type FUNCTOR =
  sig
    type 'a t
    val return: 'a -> 'a t
    val map:    ('a -> 'b) -> 'a t -> 'b t
  end

module type APPLICATIVE =
  sig
    type 'a t
    val return: 'a -> 'a t
    val map:    ('a -> 'b) -> 'a t -> 'b t
    val (<*>):  ('a -> 'b) t -> 'a t -> 'b t
  end


module type MONAD =
  sig
    type 'a t
    val return: 'a -> 'a t
    val (>>=):  'a t -> ('a -> 'b t) -> 'b t
    val (>=>):  ('a -> 'b t) -> ('b -> 'c t) -> ('a -> 'c t)
    val map:  ('a -> 'b) -> 'a t -> 'b t
    val join: 'a t t -> 'a t
    val (<*>): ('a -> 'b) t -> 'a t -> 'b t
  end


module type READABLE =
  sig
    type t
    val has_more: t -> bool
    val peek: t -> char
    val advance: t -> t
  end




module type WRITABLE =
  sig
    type t
    val needs_more: t -> bool
    val putc: t -> char ->  t
    val putend: t -> t
  end




module type FILTER =
  sig
    module Readable: READABLE
    type t
    val needs_more: t -> bool
    val putc: t -> char -> t * Readable.t
    val put_end: t -> t * Readable.t
  end


module type OUTPUT =
  sig
    type t
    val empty: t
    val (<+>): t -> t -> t
    val char: char -> t
    val string: string -> t
    val line: string -> t
    val newline: t
    val substring: string -> int -> int -> t
    val fill: int -> char -> t
  end
