open Support

type t

val empty: unit -> t

val put: 
    feature_name withinfo -> entities list withinfo -> return_type 
      -> feature_body option -> t -> unit

