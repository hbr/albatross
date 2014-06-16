module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

module type S =
    sig
      type key
      type t
      val make_empty: unit -> t
      val count:      t -> int
      val find:       key -> t -> int
      val index:      key -> t -> int
      val key:        int -> t -> key
      val iter:       (key -> unit)    -> t -> unit
      val iteri:      (int->key->unit) -> t -> unit
    end


module Make (Ord:OrderedType): S with type key = Ord.t
