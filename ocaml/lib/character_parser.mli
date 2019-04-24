module type POSITION =
  sig
    type t
    val line: t -> int
    val column: t -> int
    val start: t
    val next: char -> t -> t
  end


module Position: POSITION


module type PARSE_POSITION =
  sig
    type t
    val mark: t -> Position.t
    val current: t -> Position.t
    val line: t -> int
    val column: t -> int
    val initial: t
    val mark_current: t -> t
  end


module type LEXER =
  sig
  end


module Make: LEXER



val test: unit -> unit
