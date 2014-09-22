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
val is_interface_check: t -> bool

val name:        int -> t -> string

val make: unit -> t

val used: int -> t -> IntSet.t
val has:  int -> int list -> t -> bool

val interface_used: int withinfo list -> t -> IntSet.t
    (** [interface_used use_blk mt] returns the used modules in [use_blk] and all
        indirectly used modules including the current module
     *)

val add_used: int -> int list -> IntSet.t -> t -> unit
    (** [add_used name lib used mt] adds the used module (lib,name) which uses
        the modules [used] to the module table [mt]. It sets the current
        module to [lib,name] and puts it to interface-use mode *)


val add_current: int -> IntSet.t -> t -> unit
    (** [add_current name used mt] adds the module [name] which uses the
        modules [used] as the current module to the module table [mt]. It sets
        the current module to [name] and puts it to private mode. *)

val set_interface_check: IntSet.t -> t -> unit
    (** [set_interface_check used mt] sets the current module (which must be
        in private mode) to interface-check mode and set the publicly used modules
        to [used] in the module table [mt]. *)

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
