module type MONAD0 =
  sig
    type _ t
    val make: 'a -> 'a t
    val bind: 'a t -> ('a -> 'b t) -> 'b t
  end



module type MONAD =
  sig
    type _ t
    val make:  'a -> 'a t
    val bind:  'a t -> ('a -> 'b t) -> 'b t
    val apply: ('a->'b) t -> 'a t -> 'b t
    val map:   ('a -> 'b) -> 'a t -> 'b t
    val (>>=): 'a t -> ('a -> 'b t) -> 'b t
    val (>>):  'a t -> 'b t -> 'b t
    val sequence: 'a t list -> 'a list t
    val map_list: 'a list -> ('a -> 'b t) -> 'b list t
    val map_array: 'a array -> ('a -> 'b t) -> 'b array t
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




module type STATE =
  sig
    include MONAD
    type state
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> 'a * state
    val eval: state -> 'a t -> 'a
    val state: state -> 'a t -> state
  end


module type STATE_INTO =
  sig
    include MONAD
    module M: MONAD
    type state
    val lift: 'a M.t -> 'a t
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
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





module Make (M:MONAD0): MONAD with type 'a t = 'a M.t =
  struct
    include M
    let (>>=) = bind
    let map (f:'a -> 'b) (m:'a t): 'b t =
      m >>= fun a -> make (f a)
    let apply (f: ('a -> 'b) t) (m:'a t): 'b t =
      f >>= fun f -> map f m
    let sequence (lst:'a t list): 'a list t =
      List.fold_right
        (fun m mlst ->
          mlst >>= fun lst ->
          m >>= fun a ->
          make (a :: lst)
        )
        lst
        (make [])
    let (>>) (m1:'a t) (m2:'b t): 'b t =
      m1 >>= fun _ -> m2
    let map_list (lst:'a list) (f:'a -> 'b t): 'b list t =
      let rec mplst (lst:'a list) (res:'b list): 'b list t =
        match lst with
        | [] ->
           make res
        | hd :: tl ->
           f hd >>= fun b ->
           mplst tl (b :: res)
      in
      map List.rev (mplst lst [])
    let map_array (arr:'a array) (f:'a -> 'b t): 'b array t =
      let len = Array.length arr in
      let rec mp (i:int) (res:'b array): 'b array t =
        if i = len then
          make res
        else
          f arr.(i) >>= fun b ->
          let res =
            if Array.length res = len then
              (res.(i) <- b; res)
            else
              (Array.make len b)
          in
          mp (i+1) res
      in
      mp 0 [||]
  end



module Result (E: Common.ANY) =
  struct
    type error = E.t

    include
      Make(
          struct
            type 'a t = ('a,error) result
            let make (a:'a): 'a t = Ok a
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              match m with
              | Ok a -> f a
              | Error e -> Error e
          end
        )

    let throw (e:error): 'a t =
      Error e

    let catch (m:'a t) (f:error->'a t): 'a t =
      match m with
      | Ok a -> m
      | Error e -> f e

    let continue (m:'a t) (f1:'a->'r) (f2:error->'r): 'r =
      match m with
      | Ok a ->
         f1 a
      | Error e ->
         f2 e
  end (* Result *)





module Result_in (M:MONAD) (Error:Common.ANY) =
  struct
    module M = M
    type error = Error.t
    include
      Make(
          struct
            type 'a t = ('a,error) result M.t
            let make (a:'a): 'a t =
              Ok a |> M.make
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              M.(m >>= fun res ->
                 match res with
                 | Ok a ->
                    f a
                 | Error e ->
                    Error e |> make
              )
          end)

    let throw (e:error): 'a t =
      Error e |> M.make

    let catch (m:'a t) (f:error -> 'a t): 'a t =
      M.bind m
        (fun r ->
          match r with
          | Ok a ->
             m
          | Error e ->
             f e
        )

    let lift (m:'a M.t): 'a t =
      M.map (fun a -> Ok a) m
  end (* Result_in *)







module State (St: Common.ANY): STATE with type state = St.t =
  struct
    type state = St.t

    include
      Make(
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
  end (* State *)







module State_into (M:MONAD) (St:Common.ANY)
       : STATE_INTO with type state = St.t
  =
  struct
    module M = M
    type state = St.t

    include
      Make(
          struct
            type 'a t = state -> ('a * state) M.t
            let make (a:'a): 'a t =
              fun s -> M.make (a,s)
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              (fun s ->
                M.(m s >>= fun (x,sx) -> f x sx))
          end
        )

    let get: state t =
      fun s -> M.make (s,s)

    let put (s:state): unit t =
      fun _ -> M.make ((),s)

    let update (f:state->state): unit t =
      fun s -> M.make ((),f s)

    let lift (m:'a M.t): 'a t =
      fun s -> M.(m >>= fun x -> make (x,s))
  end (* State_into *)



module State_with_result (S:Common.ANY) (Error:Common.ANY) =
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
      Make(
          struct
            type 'a t = Buffer.t -> 'a * Buffer.t
            let make (a:'a): 'a t =
              fun buf -> a,buf
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
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

    let put_string (s:string): unit t =
      fun buf -> Buffer.add_string buf s; (),buf

    let put_substring (start:int) (len:int) (s:string): unit t =
      fun buf -> Buffer.add_substring buf s start len; (),buf

    let run (n:int) (m:'a t): string =
      assert (0 <= n);
      let _,buf = m (Buffer.create n) in
      Buffer.contents buf
  end
