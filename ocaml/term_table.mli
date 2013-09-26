open Term

type 'a t

val empty: 'a t

val count: 'a t -> int

val data:  int -> 'a t -> int * 'a

val term:  int -> 'a t -> term

val unify: term -> int -> 'a t -> (int * int * 'a * substitution) list

val add: term -> int -> 'a -> 'a t -> 'a t
