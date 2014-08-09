open Container
open Term

type t
val empty: t
val fgconcepts: t -> type_term array
val fgnames:    t -> int array
val has_fg:     int -> t -> bool
val make_fgs:    int array -> type_term array -> t
val count_local:  t -> int
val count_global: t -> int
val count:        t -> int
val count_fgs:    t -> int
val count_all:    t -> int
val concept:      int -> t -> type_term
val concepts:     t -> type_term array
val add_fgs:      t -> t -> t
val remove_fgs:   t -> t -> t
val add_global:   type_term array -> t -> t
val add_local:    int -> t -> t
val remove_local: int -> t -> t
val augment_fgs:  int array -> type_term array -> t -> t
val fgs_to_global: t -> t
val involved_classes: type_term -> t -> IntSet.t -> IntSet.t
