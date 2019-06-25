open Common_module_types

module type SIG =
  sig
    type answer
    include MONAD
    val run: answer t -> answer
    val callcc: (('a -> 'b t) -> 'a t) -> 'a t
  end


module Make (A: ANY): SIG with type answer = A.t


module type SIG_EXPERIMENTAL =
  sig
    type answer
    include MONAD
    val run: answer t -> answer
  end

module Make_experimental (A:ANY): SIG_EXPERIMENTAL with type answer = A.t
