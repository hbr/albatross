module type ANY =
  sig
    type t
  end


module type SORTABLE =
  sig
    include ANY
    val compare: t -> t -> int
  end
