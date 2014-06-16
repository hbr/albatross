open Container

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

module Make (Ord:OrderedType) = struct

  type key = Ord.t

  module Map = Map.Make(Ord)

  type t = {seq:         key Seq.t;
            mutable map: int Map.t}

  let make_empty () = {seq = Seq.empty (); map = Map.empty}

  let count (mt: t) = Seq.count mt.seq

  let find (e:key) (mt:t): int = Map.find e mt.map

  let mem (e:key) (mt:t): bool =
    try
      let _ = find e mt in true
    with Not_found ->
      false

  let added (e:key) (mt:t): int =
    assert (not (mem e mt));
    let cnt = Seq.count mt.seq in
    Seq.push e mt.seq;
    mt.map <- Map.add e cnt mt.map;
    cnt

  let index (e:key) (mt:t): int =
    try
      find e mt
    with Not_found ->
      added e mt

  let key (i:int) (mt:t): key =
    assert (i < count mt);
    Seq.elem i mt.seq

  let iter (f:key->unit) (mt:t) =
    Seq.iter f mt.seq

  let iteri (f:int->key->unit) (mt:t) =
    Seq.iteri f mt.seq
end
