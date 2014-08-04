open Container
open Support

type t
val count:       t -> int
val find:        int -> int list -> t -> int
val has:         int -> int list -> t -> bool
val has_current: t -> bool
val current:     t -> int

val is_public:   t -> bool
val is_private:  t -> bool
val is_interface_use: t -> bool

val name:        int -> t -> string

val make: unit -> t

val used: int -> t -> IntSet.t
val has:  int -> int list -> t -> bool
val add:  int -> int list -> int -> t -> unit
val set_used: IntSet.t -> t -> unit
