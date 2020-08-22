type _ t

val empty: _ t

val push_front: 'a -> 'a t -> 'a t

val push_rear: 'a -> 'a t -> 'a t

val pop_front: 'a t -> ('a * 'a t) option
