type t

val substring: string -> int -> int -> t
val string: string -> t
val fill: int -> char -> t
val char: char -> t
val length: t -> int
val peek: t -> char
val advance: t -> t option
