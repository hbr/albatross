module type S =
  sig
    type state
    include Monad.S
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> 'a * state
    val eval: state -> 'a t -> 'a
    val state: state -> 'a t -> state
  end


module Make (S: sig type t end): (S with type state = S.t)
