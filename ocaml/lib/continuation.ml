module type S =
  sig
    type answer
    include Monad.MONAD
    val answer: answer t -> answer
    val run: 'a t -> ('a -> answer) -> answer
    val callcc: (('a -> 'b t) -> 'a t) -> 'a t
  end


module Make (A: sig type t end) =
  struct
    type answer = A.t (* The final answer *)
    include
      Monad.Make(
          struct
            type 'a t = ('a -> answer) -> answer
            (* The continuation monad of type 'a contains a function which
               maps a function of type 'a->answer to the answer. The function
               contained in the monad is a closure which has access to the
               intermediate value of type 'a. *)
            let make (a: 'a): 'a t =
              fun (k:'a->answer) -> k a
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              fun (k:'b->answer) -> m (fun a -> f a k)
          end
        )
    let run (m:'a t) (f:'a->answer): answer =
      m f
    let answer (m: answer t): answer =
      m (fun x -> x)
    let callcc (f:('a->'b t)->'a t): 'a t =
      fun k -> f (fun x -> fun _ -> k x) k
    (*let callcc (f: ('a->'b t)->'a t): 'a t = (* signature from Haskell *)
      fun g -> f g g *)
    (* leroy: let callcc (f: ('a->answer) -> ('a->answer) -> answer): 'a t =
      fun g -> f g g (* type annotion ok?*)*)
    let throw x y = fun g -> x y
  end
