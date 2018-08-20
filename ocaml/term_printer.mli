open Alba2_common

module Term = Term2



module type CONTEXT =
  sig
    type t
    val empty: t
    val push: Feature_name.t option -> Term.typ -> t -> t
    val name: int -> t -> Feature_name.t option
  end


module type S =
  sig
    type context
    type ppt
    type _ out
    val print: Term.t -> context -> ppt -> ppt out
  end

module Make (C:CONTEXT) (PP:Pretty_printer.PRETTY)
       : S with type 'a out = PP.t PP.out and
                type ppt = PP.t and
                type context = C.t


val string_of_term: Term.t -> string

val test: unit -> unit
