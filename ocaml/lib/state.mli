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


module Make (State:Common.ANY): (S with type state = State.t)


module Within (M:Monad.S) (State:Common.ANY):
sig
  type state = State.t
  include Monad.S
          with type 'a t = state -> ('a * state) M.t
end
