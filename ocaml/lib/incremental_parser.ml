module type ANY = Common.ANY



module type PARSER =
  sig
    type token
    type error
    type state
    type 'a t =
      | Accept of state * 'a * token list
      | More of state * (state -> token -> 'a t)
      | Reject of state * error * int * token list

    val next:    'a t -> token -> 'a t
    val consume: 'a t -> token list -> 'a t

    type ('a,'z) context =
      {state:state;
       success: state -> 'a -> token list -> 'z t;
       failure: state -> error -> int -> token list -> 'z t}

    type ('a,'z) partial = ('a,'z) context -> 'z t

    val make: ('a,'a) partial -> state -> 'a t
    val consume: 'a t -> token list -> 'a t
    val next:    'a t -> token -> 'a t

    val backtrack: ('a,'a) partial -> ('a,'z) context -> 'z t

    val token: (state -> token -> state * ('a,error) result) ->
               ('a,'z) partial

    val join: ('a -> 'b -> state -> state * 'c) ->
              ('a,'z) partial ->
              ('b,'z) partial ->
              ('c,'z) partial

    val choose: ('a,'z) partial -> ('a,'z) partial -> ('a,'z) partial
    val choose_l: ('a,'z) partial list -> ('a,'z) partial
  end



module Make (Token:ANY) (Error:ANY) (State:ANY)
       : (PARSER with type token = Token.t
                  and type error = Error.t
                  and type state = State.t)
  =
  struct
    type token = Token.t
    type error = Error.t
    type state = State.t
    type 'a t =
      | Accept of state * 'a * token list
      | More of state * (state -> token -> 'a t)
      | Reject of state * error * int * token list

    type tlist = token list

    type ('a,'z) context =
      {state:state;
       success: state -> 'a -> tlist -> 'z t;
       failure: state -> error -> int -> tlist -> 'z t}

    type ('a,'z) partial =
      ('a,'z) context ->
      'z t

    let make (pp:('a,'a) partial) (state:state): 'a t =
      pp {state;
          success = (fun s a la -> Accept (s,a,la));
          failure = (fun s e n la -> Reject (s,e,n,la))}

    let rec consume (p:'a t) (ts:tlist): 'a t =
      match p with
      | Accept (s, a, la) ->
         Accept (s, a, List.rev_append ts la)
      | More (s, f) ->
         begin
           match ts with
           | [] -> p
           | t :: tl ->
              consume (f s t) tl
         end
      | Reject (s, e, n, la) ->
         Reject (s, e, n, List.rev_append ts la)

    let next (p: 'a t) (t:token): 'a t =
      consume p [t]


    module ST = State_transformer.Make (State)
    module M =
      struct
        type 'a pt = 'a t
        include Result.Within
                  (ST)
                  (Error)
        let run (s:state) (m:'a t) (f1:state->'a->'b) (f2:state->'e->'b): 'b =
          let r,s = ST.run s m in
          match r with
          | Ok a ->
             f1 s a
          | Error e ->
             f2 s e
      end


    let one (f:token -> 'a M.t) (c:('a,'z) context): 'z t =
      More (c.state,
            M.(fun s t ->
              run
                s (f t)
                (fun s a -> c.success s a [])
                (fun s e -> c.failure s e 0 [t])
            ))

    let join_new
          (f: ('a*'b) -> 'r M.t)
          (pp: ('a,'z) partial)
          (qq: ('b,'z) partial)
          (c: ('r,'z) context)
        : 'z t =
      let cq s a =
        {state = s;
         success =
           (fun s b la ->
             M.(run
                  s (f (a,b))
                  (fun s r -> c.success s r la)
                  (fun s e -> c.failure s e 0 la)));
         failure = c.failure}
      in
      let cp =
        {state = c.state;
         success =
           (fun s a la -> List.fold_left next (cq s a |> qq) (List.rev la));
         failure = c.failure}
      in
      pp cp

    let backtrack
          (pp: ('a,'a) partial)
          (c:  ('a,'z) context)
        : 'z t =
      let rec f (p:'a t) (used:tlist): 'z t =
        match p with
        | Accept (s,a,la) ->
           c.success s a la
        | More (s,fp) ->
           More (s, fun s t -> f (fp s t) (t::used))
        | Reject (s,e,n,la) ->
           c.failure s e 0 used
      in
      f (make pp c.state) []


    let token
          (f:state -> token -> state * ('a,error) result)
          (k:('a,'z) context)
        : 'z t =
      More (k.state,
            (fun s t ->
              let s,r = f s t in
              match r with
              | Ok a ->
                 k.success s a []
              | Error e ->
                 k.failure s e 0 [t])
        )

    let join
          (f: 'a -> 'b -> state -> state * 'r)
          (pp: ('a,'z) partial)
          (qq: ('b,'z) partial)
          (c: ('r,'z) context)
        : 'z t =
      let cq s a =
        {state = s;
         success =
           (fun s b la ->
             let s,r = f a b s in
             c.success s r la);
         failure = c.failure}
      in
      let cp =
        {state = c.state;
         success =
           (fun s a la -> List.fold_left next (cq s a |> qq) (List.rev la));
         failure = c.failure}
      in
      pp cp

    let choose_l (l: ('a,'z) partial list) (c: ('a,'z) context): 'z t =
      match l with
      | [] ->
         assert false (* illegal call without alternatives *)
      | pp :: rest ->
         let rec choose l s e la =
           match l with
           | [] ->
              c.failure s e 0 la
           | pp :: rest ->
              pp (context s rest)
         and context s l =
           {state = s;
            success = c.success;
            failure =
              (fun s e n la ->
                if n = 0 then
                  choose l s e la
                else
                  c.failure s e n la)}
         in
         pp (context c.state rest)


    let choose
          (pp: ('a,'z) partial)
          (qq: ('a,'z) partial)
          (c: ('a,'z) context)
        : 'z t =
      pp {state = c.state;
          success = c.success;
          failure =
            (fun s e n la ->
              if n = 0 then
                qq {state = s;
                    success = c.success;
                    failure = c.failure}
              else
                c.failure s e n la)}
  end
