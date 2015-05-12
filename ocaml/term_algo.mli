open Term

(*val unify: term -> term -> int -> Term_sub.t*)

val compare: term -> term -> (term->term->'a)
  -> term * 'a array * term array * term array
