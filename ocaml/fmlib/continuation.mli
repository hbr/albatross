module type S =
  sig
    type answer
    include Monad.MONAD
    val answer: answer t -> answer
    val run: 'a t -> ('a -> answer) -> answer
    val callcc: (('a -> 'b t) -> 'a t) -> 'a t
  end


module Make (A: sig type t end): S with type answer = A.t
