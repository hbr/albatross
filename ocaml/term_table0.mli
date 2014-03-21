open Term

type t

val global: t

val local: int -> t -> t

val count_environment: t -> int

val count: t -> int

val term:  int -> int -> t -> term

val unify: term -> int -> t -> (int * Term_sub.t) list

val unify_with: term -> int -> int -> t -> (int * Term_sub.t) list

val add: term -> int -> t -> t

