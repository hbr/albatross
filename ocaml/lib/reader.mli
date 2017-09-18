module type S =
  sig
    type env
    include Monad.S
    val get: env t
    val local: (env -> env) -> 'a t -> 'a t
  end


module Make (ENV: sig type t end): S with type env = ENV.t
