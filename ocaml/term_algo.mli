open Term

val unify_pattern: int -> term -> int -> term -> term array

val unify: term -> int -> term -> term array

val can_unify_pattern: term -> int -> term -> bool

val can_unify: term -> int -> term -> bool

val compare: term -> term -> (term->term->'a)
  -> term * 'a array * term array * term array
