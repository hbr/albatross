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
