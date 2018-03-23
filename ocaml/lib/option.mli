include Monad.MONAD with type 'a t = 'a option

val has: 'a t -> bool
val value: 'a t -> 'a
val iter:  ('a -> unit) -> 'a t -> unit

module Within (M:Monad.MONAD): Monad.MONAD with type 'a t = 'a t M.t
