module type S =
  sig
    type error
    include Monad.S
    val raise: error -> 'a t
  end


module Make (E: sig type t end)
       : S with
         type 'a t = ('a,E.t) result
         and type error = E.t
