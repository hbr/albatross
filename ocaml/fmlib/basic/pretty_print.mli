type t
val has_more: t -> bool
val peek: t -> char
val advance: t -> t

type doc

val layout: int -> int -> doc -> t

val empty: doc
val string: string -> doc
val substring: string -> int -> int -> doc
val char: char -> doc
val fill: int -> char -> doc
val line: string -> doc
val space: doc
val cut: doc
val nest: int -> doc -> doc
val group: doc -> doc
val (<+>): doc -> doc -> doc
val chain: doc list -> doc
val separated_by: doc -> doc list -> doc
val pack: string -> doc list -> doc
val wrap_words: string -> doc
