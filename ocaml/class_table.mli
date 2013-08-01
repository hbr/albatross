open Support
open Type

type t

val base_table: unit -> t

val put: t -> header_mark withinfo -> int withinfo -> unit

val print: t-> unit 

val type2string: typ -> int -> t -> string
