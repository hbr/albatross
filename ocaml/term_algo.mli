open Term

val unify: term -> int -> term -> Term_sub.t

val can_unify: term -> int -> term -> bool

val compare: term -> term -> (term->term->'a)
  -> term * 'a array * term array * term array
