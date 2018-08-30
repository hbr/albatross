module type DOCUMENT =
  sig
    type t
    val empty: t
    val (^): t -> t -> t
    val nest: int -> t -> t
    val text: string -> t
    val space: t
    val cut: t
    val optional: string -> t
    val group: t -> t
    val (^+): t -> t -> t
    val (^/): t -> t -> t
    val fold: (t -> t -> t) -> t list -> t
    val spread: t list -> t
    val stack:  t list -> t
    val bracket: string -> t -> string -> t
  end


module Document: DOCUMENT


module type LAYOUT =
  sig
    type t
    val best: int -> Document.t -> t
    val to_string: t -> string
    val pretty: int -> Document.t -> string
  end



module Layout: LAYOUT


val test: unit -> unit
