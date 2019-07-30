open Common_module_types


module type SIG_MIN =
  sig
    type _ t
    val return: 'a -> 'a t
    val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  end

module type SIG_WITH_MAP =
  sig
    include SIG_MIN
    val map: ('a -> 'b) -> 'a t -> 'b t
  end





module type RESULT =
  sig
    include MONAD
    type error
    val throw: error -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
    val continue: 'a t -> ('a -> 'z) -> (error -> 'z) -> 'z
  end




module type RESULT_IN =
  sig
    include MONAD
    module M: MONAD
    type error
    val throw: error -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
    val lift: 'a M.t -> 'a t
  end



module type READER =
  functor (Env:ANY) ->
  sig
    include MONAD
    type env = Env.t
    val ask: env t
    val local: (env->env) -> 'a t -> 'a t
    val run: env -> 'a t -> 'a
  end



module type READER_INTO =
  functor (M:MONAD) (Env:ANY) ->
  sig
    include MONAD

    type env = Env.t

    val run: env -> 'a t -> 'a M.t
    val ask: env t
    val local: (env->env) -> 'a t -> 'a t
    val lift: 'a M.t -> 'a t
  end





module type STATE =
  functor (S:ANY) ->
  sig
    include MONAD
    type state = S.t
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> 'a * state
    val eval: state -> 'a t -> 'a
    val state: state -> 'a t -> state
  end


module type STATE_INTO =
  functor (M:MONAD) (S:ANY) ->
  sig
    include MONAD
    type state = S.t
    val lift: 'a M.t -> 'a t
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> ('a*state) M.t
    val eval: state -> 'a t -> 'a M.t
  end



module type STATE_WITH_RESULT =
  sig
    include MONAD
    type state
    type error
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val throw: error -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
    val continue: state -> 'a t ->
                  (state -> 'a -> 'z) ->
                  (state -> error -> 'z) ->
                  'z
  end





module Of_sig_with_map (M:SIG_WITH_MAP): MONAD with type 'a t = 'a M.t =
  struct
    include M

    let (>=>) f g a =
      f a >>= g

    let (<*>) mf m =
      mf >>= fun f -> map f m

    let join mm =
      mm >>= fun m -> m
  end


module Of_sig_min (M:SIG_MIN): MONAD with type 'a t = 'a M.t =
  struct
    include M

    let (>=>) f g a =
      f a >>= g

    let map (f:'a -> 'b) (m:'a t): 'b t =
      m >>= fun a -> return (f a)

    let (<*>) mf m =
      mf >>= fun f -> map f m

    let join mm =
      mm >>= fun m -> m
  end



module Result (E: ANY) =
  struct
    type error = E.t

    include
      Of_sig_min(
          struct
            type 'a t = ('a,error) result
            let return (a:'a): 'a t = Ok a
            let (>>=) (m:'a t) (f:'a -> 'b t): 'b t =
              match m with
              | Ok a -> f a
              | Error e -> Error e
          end
        )

    let throw (e:error): 'a t =
      Error e

    let catch (m:'a t) (f:error->'a t): 'a t =
      match m with
      | Ok _ -> m
      | Error e -> f e

    let continue (m:'a t) (f1:'a->'r) (f2:error->'r): 'r =
      match m with
      | Ok a ->
         f1 a
      | Error e ->
         f2 e
  end (* Result *)





module Result_in (M:MONAD) (Error:ANY) =
  struct
    module M = M
    type error = Error.t
    include
      Of_sig_min(
          struct
            type 'a t = ('a,error) result M.t
            let return (a:'a): 'a t =
              Ok a |> M.return
            let (>>=) (m:'a t) (f:'a -> 'b t): 'b t =
              M.(m >>= fun res ->
                 match res with
                 | Ok a ->
                    f a
                 | Error e ->
                    Error e |> return
              )
          end)

    let throw (e:error): 'a t =
      Error e |> M.return

    let catch (m:'a t) (f:error -> 'a t): 'a t =
      M.(m >>= fun r ->
         match r with
         | Ok _ ->
            m
         | Error e ->
            f e
        )

    let lift (m:'a M.t): 'a t =
      M.map (fun a -> Ok a) m
  end (* Result_in *)




module Reader (Env:ANY) =
  struct
    type env = Env.t
    include
      Of_sig_min (
          struct
            type 'a t = env -> 'a
            let return (a:'a) (_:env): 'a =
              a
            let (>>=) (m:'a t) (f:'a -> 'b t) (e:env): 'b =
              f (m e) e
          end
        )

    let run (e:env) (m:'a t): 'a =
      m e

    let ask (e:env): env =
      e

    let local (f:env->env) (m:'a t) (e:env): 'a =
      f e |> m
  end




module Reader_into: READER_INTO =
  functor (M:MONAD) (Env:ANY) ->
  struct
    type env = Env.t
    include
      Of_sig_min (
          struct
            type 'a t = env -> 'a M.t
            let return (a:'a) (_:env): 'a M.t =
              M.return a
            let (>>=) (m:'a t) (f:'a -> 'b t) (e:env): 'b M.t =
              M.(m e >>= fun a -> f a e)
          end
        )

    let run (e:env) (m:'a t): 'a M.t =
      m e

    let ask: env t = M.return

    let local (f:env->env) (m:'a t) (e:env): 'a M.t =
      f e |> m

    let lift (m:'a M.t) (_:env): 'a M.t =
      m
  end









module State: STATE =
  functor (St:ANY) ->
  struct
    type state = St.t

    include
      Of_sig_min(
          struct
            type 'a t = state ref -> 'a
            let return (a:'a) (_:state ref): 'a =
              a
            let (>>=) (m:'a t) (f:'a -> 'b t) (sr:state ref) : 'b =
              (f @@ m sr) sr
          end
        )

    let get (sr:state ref): state =
      !sr

    let put (s:state) (sr:state ref): unit =
      sr := s

    let update (f:state->state) (sr:state ref): unit =
      sr := f !sr

    let run (s:state) (m:'a t): 'a * state =
      let sr = ref s in
      m sr, !sr

    let eval (s:state) (m:'a t): 'a =
      let sr = ref s in
      m sr

    let state (s:state) (m:'a t): state =
      let sr = ref s in
      ignore (m sr);
      !sr
  end (* State *)







module State_into: STATE_INTO
  =
  functor (M:MONAD) (St:ANY) ->
  struct
    type state = St.t

    include
      Of_sig_min(
          struct
            type 'a t = state -> ('a * state) M.t
            let return (a:'a): 'a t =
              fun s -> M.return (a,s)
            let (>>=) (m:'a t) (f:'a -> 'b t): 'b t =
              (fun s ->
                M.(m s >>= fun (x,sx) -> f x sx))
          end
        )

    let get: state t =
      fun s -> M.return (s,s)

    let put (s:state): unit t =
      fun _ -> M.return ((),s)

    let update (f:state->state): unit t =
      fun s -> M.return ((),f s)

    let lift (m:'a M.t): 'a t =
      fun s -> M.(m >>= fun x -> return (x,s))

    let run (s:state) (m:'a t): ('a*state) M.t =
      m s

    let eval (s:state) (m: 'a t): 'a M.t =
      M.(m s >>= fun (a,_) -> return a)
  end (* State_into *)



module State_with_result (S:ANY) (Error:ANY) =
  struct
        module ST = State (S)

        module R  = Result_in (ST) (Error)

        include R

        type state = ST.state

        let get: state t = lift ST.get

        let put (s:state): unit t =
          ST.put s |> lift

        let update (f:state->state): unit t =
          ST.update f |> lift

        let continue
              (s:state) (m:'a t)
              (f1:state->'a->'z) (f2:state->error->'z)
            : 'z =
          let r,s = ST.run s m in
          match r with
          | Ok a ->
             f1 s a
          | Error e ->
             f2 s e
  end (* State_with_result *)


module String_buffer =
  struct
    include
      Of_sig_min(
          struct
            type 'a t = Buffer.t -> 'a * Buffer.t
            let return (a:'a): 'a t =
              fun buf -> a,buf
            let (>>=) (m:'a t) (f:'a -> 'b t): 'b t =
              fun buf ->
              let a,buf1 = m buf in
              f a buf1
          end)

    let getc (i:int): char t =
      fun buf ->
      try
        Buffer.nth buf i,buf
      with Invalid_argument _ ->
        assert false

    let length: int t =
      fun buf -> Buffer.length buf,buf

    let putc (c:char): unit t =
      fun buf -> Buffer.add_char buf c; (),buf

    let fill (c:char) (n:int): unit t =
      fun buf ->
      for _ = 0 to n - 1 do
        Buffer.add_char buf c
      done;
      (), buf

    let put_string (s:string): unit t =
      fun buf -> Buffer.add_string buf s; (),buf

    let put_substring (s:string) (start:int) (len:int): unit t =
      fun buf -> Buffer.add_substring buf s start len; (),buf

    let run (n:int) (m:'a t): string =
      assert (0 <= n);
      let _,buf = m (Buffer.create n) in
      Buffer.contents buf
  end
