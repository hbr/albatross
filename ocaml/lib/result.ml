module type S =
  sig
    type error
    include Monad.S
    val raise: error -> 'a t
  end


module Make (E: sig type t end) =
  struct
    type error = E.t
    include
      Monad.Make(
          struct
            type 'a t = ('a,error) result
            let make (a:'a): 'a t = Ok a
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              match m with
              | Ok a -> f a
              | Error e -> Error e
          end
        )
    let raise (e:error): 'a t = Error e
  end
