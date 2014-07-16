open Term

type t

val empty: t

val terms: t -> (int*int*int*term) list

val term:  int -> int -> t -> term

val unify: term -> int -> t -> (int * Term_sub.t) list

val unify_with: term -> int -> int -> t -> (int * Term_sub.t) list

val unify_unique: term -> int -> t -> int * Term_sub.t

val unify_unique_with: term -> int -> int -> t -> int * Term_sub.t

val add: term -> int -> int -> int -> t -> t

val print_tab: int -> t -> unit

