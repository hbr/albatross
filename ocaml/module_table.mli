open Container
open Support
open Term
open Signature

type t
val count:       t -> int
val find:        int -> int list -> t -> int
val has:         int -> int list -> t -> bool
val has_current: t -> bool
val current:     t -> int

val is_public:   t -> bool
val is_private:  t -> bool
val is_interface_use: t -> bool

val name:        int -> t -> string

val make: unit -> t

val used: int -> t -> IntSet.t
val has:  int -> int list -> t -> bool
val add:  int -> int list -> int -> t -> unit
val set_used: IntSet.t -> t -> unit


val put_formal: int withinfo -> type_term -> t -> unit

val class_formal_generics: formal_generics -> t -> (int*type_term) array

val formal_generics: entities list withinfo -> return_type -> int -> TVars_sub.t -> t
  -> TVars_sub.t
   (** [formal_generics entlst rt ntvs_gap tvs ct] cumulates the formal
       generics encountered in the signature [entlst,rt] to the type context
       [tvs] if not yet in. Between the untyped arguments of the signature
       [entlst,rt] and the free type variables already contained in [tvs] a gap
       of [ntvs_gap] is left. *)
