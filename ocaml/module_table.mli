open Support

type t
val count:       t -> int
val find:        int -> int list -> t -> int
val has:         int -> int list -> t -> bool
val has_current: t -> bool
val current:     t -> int
val is_toplevel: t -> bool
    (** Is the module table in the normal processing of a module i.e. does it
        have only one module on the stack?  *)

val is_public:   t -> bool
val is_private:  t -> bool
val set_public:  t -> unit

val make: unit -> t

val add_used:    int -> info -> t -> unit
    (** [add_used mdl mt] adds the module [mdl] and all its uses modules as
        used modules to the used modules of the current module of [mt].  *)
    
val push: int -> int list -> t -> unit
    (** [push name lib inf mt] pushes [lib.name] as the current module onto
        the stack of [mt]. *)
    
val pop: t -> unit
    (** [pop mt] pops the current module off the stack (because all used
        modules of it are already analyzed] and adds it and its used modules
        to the new current module unless there is no new current module. *)
