open Common_module_types
open Common

module type S =
  sig
    type answer
    include MONAD
    val run: answer t  -> answer
    val callcc: (('a -> 'b t) -> 'a t) -> 'a t
  end


module Make (A: ANY) =
  struct
    type answer = A.t (* The final answer *)
    include
      Monad.Of_sig_min(
          struct
            type 'a t = ('a -> answer) -> answer
            (* The continuation monad of type 'a contains a function which
               maps a function of type 'a->answer to the answer. The function
               contained in the monad is a closure which has access to the
               intermediate value of type 'a. *)
            let return (a: 'a) (k:'a -> answer): answer =
              k a
            let (>>=) (m:'a t) (f:'a -> 'b t) (k:'b->answer): answer =
              m (fun a -> f a k)
          end
        )

    let run (m:answer t): answer =
      m identity

    let callcc (f:('a->'b t)->'a t): 'a t =
      fun k -> f (fun x -> fun _ -> k x) k
    (*let callcc (f: ('a->'b t)->'a t): 'a t = (* signature from Haskell *)
      fun g -> f g g *)
    (* leroy: let callcc (f: ('a->answer) -> ('a->answer) -> answer): 'a t =
      fun g -> f g g (* type annotion ok?*)*)
    (*let throw x y = fun g -> x y*)
  end
