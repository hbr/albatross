open Common_module_types

module type S =
  sig
    type answer
    include MONAD
    val run: answer t -> answer
    val callcc: (('a -> 'b t) -> 'a t) -> 'a t
  end


module Make (A: ANY): S with type answer = A.t
