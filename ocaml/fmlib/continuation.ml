open Common_module_types
open Common

module type SIG_EXPERIMENTAL =
  sig
    type answer
    include MONAD
    val run: answer t -> answer
  end


module Make_experimental (A: ANY) =
  struct
    type answer = A.t (* The final answer *)

    type state =
      | More of (unit -> state)
      | Done of answer

    module M = struct
      type 'a t = ('a -> state) -> state

      let return (a:'a) (k:'a -> state): state =
        k a

      let (>>=) (m:'a t) (f:'a -> 'b t) (k:'b->state): state =
        m (fun a -> More (fun () -> f a k))
    end

    include Monad.Of_sig_min (M)

    let run (m:answer t): answer =
      let rec iterate = function
        | Done a ->
           a
        | More f ->
           iterate (f ())
      in
      iterate @@ m (fun a -> Done a)

    (*let run_while (m:answer t): answer =
      let st = ref (m (fun a -> Done a))
      and goon = ref true
      in
      while !goon do
        match !st with
        | Done _ ->
           goon := false
        | More f ->
           st := f ()
      done;
      match !st with
      | Done a ->
         a
      | _ ->
         assert false (* cannot happen *)*)
  end



module type SIG =
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
