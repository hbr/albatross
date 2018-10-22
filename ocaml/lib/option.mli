include Monad.MONAD with type 'a t = 'a option

val has: 'a t -> bool
val value: 'a t -> 'a
val of_bool: bool -> unit t
val iter:  ('a -> unit) -> 'a t -> unit
val interval_fold: ('a->int->'a t) -> 'a t -> int -> int -> 'a t

module Within (M:Monad.MONAD): Monad.MONAD with type 'a t = 'a t M.t
