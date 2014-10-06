open Container
open Term

(** An environment for types

    It contains the number of type variables without a concepts, the concepts
    of type variables imported from global features and the names and concepts
    of all formal generices of the local environment

    Note: All concepts are valid in (i.e. relative to) the environment *)

type t
val empty: t
    (** An empty type environment *)

val make_fgs:    int array -> type_term array -> t
    (** [make_fgs names cpts] makes a type enviroment from the formal generics
        with the names [names] and the concepts [cpts].

        Note: The concepts can refer to eachother, therefore all global class
        indices must be shifted up by [Array.length cpts] *)

val fgconcepts: t -> type_term array
val fgnames:    t -> int array
val has_fg:     int -> t -> bool
val count_local:  t -> int
val count_global: t -> int
val count:        t -> int
val count_fgs:    t -> int
val count_all:    t -> int
val concept:      int -> t -> type_term
val concepts:     t -> type_term array

val is_equivalent:  t -> t -> bool

val is_equal:       type_term -> t -> type_term -> t -> bool
    (** [is_equal tp1 tvs1 tp2 tvs2]: Are the types [tp1] from the environment
        [tvs1] and [tp2] from the environment [tvs2] equal? *)


val is_equal_or_fg: type_term -> t -> type_term -> t -> bool
    (** [is_equal tp1 tvs1 tp2 tvs2]: Are the types [tp1] from the environment
        [tvs1] and [tp2] from the environment [tvs2] equal or is [tp1] a
        formal generic and its concept is equal with [tp2]? *)

val principal_class: type_term -> t -> int
    (** [principal_class tp tvs] returns the principal class of the type [tp] *)

val add_fgs:      t -> t -> t
val remove_fgs:   t -> t -> t

val insert_fgs:   t -> int -> t -> t
    (** [insert_fgs tvs1 i tvs2] inserts in [tvs1] at [i] the concepts of the
        formal generics of [tvs2] *)

val update_fg: int -> type_term -> t -> t
    (** [update_fg i tp tvs] updates the concept of the formal generic [i]
        with the type [tp]*)


val add_global:   type_term array -> t -> t
val add_local:    int -> t -> t
val remove_local: int -> t -> t
val augment_fgs:  int array -> type_term array -> t -> t
val fgs_to_global: t -> t
val involved_classes: type_term -> t -> IntSet.t -> IntSet.t
