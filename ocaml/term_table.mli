open Term

type t

val empty: t

val term:  int -> int -> t -> term

val unify: term -> int -> t -> (int * Term_sub.t) list

val unify_with: term -> int -> int -> t -> (int * Term_sub.t) list

val add: term -> int -> int -> int -> t -> t

val print_tab: int -> t -> unit

