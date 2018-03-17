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


module Make (St: sig type t end): (S with type state = St.t) =
  struct
    type state = St.t
    include
      Monad.Make(
          struct
            type 'a t = state -> 'a * state
            let make (a:'a): 'a t =
              fun s -> a,s
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              (fun s ->
                let a,s1 = m s in
                f a s1)
          end
        )
    let get: state t =
      (fun s -> s,s)

    let put (s:state): unit t =
      fun _ -> (),s

    let update (f:state->state): unit t =
      fun s -> (), f s

    let run (s:state) (m:'a t): 'a * state =
      m s

    let eval (s:state) (m:'a t): 'a =
      m s |> fst

    let state (s:state) (m:'a t): state =
      m s |> snd
  end
