open Term

type 'a t

val global: 'a t

val local: int -> 'a t -> 'a t

val count: 'a t -> int

val data:  int -> 'a t -> int * 'a

val term:  int -> 'a t -> term

val unify: term -> int -> 'a t -> (int * int * 'a * substitution) list

val add: term -> int -> 'a -> 'a t -> 'a t

val write: 'a t -> unit
