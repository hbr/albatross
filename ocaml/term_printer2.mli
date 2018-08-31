open Alba2_common

module Term = Term2



module type CONTEXT =
  sig
    type t
    val empty: t
    val push: Feature_name.t option -> Term.typ -> t -> t
    val push_arguments: Term.arguments -> t -> t
    val name: int -> t -> Feature_name.t option
  end


module type S =
  sig
    type context
    val print: Term.t -> context -> Pretty_printer2.Document.t
  end

module Make (C:CONTEXT)
       : S with type context = C.t


val test: unit -> unit
