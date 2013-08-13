open Support

type t

val empty: unit -> t

val put: entities list withinfo -> feature_body 
  -> Class_table.t -> Feature_table.t -> t -> unit

val print: Class_table.t -> Feature_table.t -> t -> unit
