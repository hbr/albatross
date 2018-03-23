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

    module M: Monad.STATE_WITH_RESULT with type state = state and
                                           type error = error

    type ('a,'z) context =
      {state:state;
       success: state -> 'a -> token list -> 'z t;
       failure: state -> error -> int -> token list -> 'z t}

    type ('a,'z) partial = ('a,'z) context -> 'z t

    val make: ('a,'a) partial -> state -> 'a t
    val consume: 'a t -> token list -> 'a t
    val next:    'a t -> token -> 'a t

    val backtrack: ('a,'a) partial -> ('a,'z) partial

    val token: (token -> 'a M.t) -> ('a,'z) partial

    val join: (('a*'b) -> 'c M.t) ->
              ('a,'z) partial ->
              ('b,'z) partial ->
              ('c,'z) partial

    val choose: (('a,'z) partial list) -> ('a,'z) partial

    val choose2: ('a,'z) partial -> ('a,'z) partial -> ('a,'z) partial

    val many_base: ('a,'z) partial ->
                   (int -> bool) ->
                   (int -> bool) ->
                   'b ->
                   ('b -> 'a -> 'b M.t) ->
                   ('b -> 'c M.t) ->
                   ('c,'z) partial

    val many0: ('a,'z) partial -> ('a list -> 'c M.t) -> ('c,'z) partial

    val many1: ('a,'z) partial -> ('a list -> 'c M.t) -> ('c,'z) partial

    val between: ('a -> 'b -> 'c -> 'r M.t) ->
                 ('a,'z) partial ->
                 ('b,'z) partial ->
                 ('c,'z) partial ->
                 ('r,'z) partial

    val count: int -> int ->
               ('a,'z) partial ->
               ('a list -> 'b M.t) ->
               ('b,'z) partial

    val optional: ('a,'z) partial -> ('a option,'z) partial
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


    module M = Monad.State_with_result (State) (Error)


    let token (f:token -> 'a M.t) (c:('a,'z) context): 'z t =
      More (c.state,
            M.(fun s t ->
              continue
                s (f t)
                (fun s a -> c.success s a [])
                (fun s e -> c.failure s e 0 [t])
            ))

    let join
          (f: ('a*'b) -> 'r M.t)
          (pp: ('a,'z) partial)
          (qq: ('b,'z) partial)
          (c: ('r,'z) context)
        : 'z t =
      let cq s a =
        {state = s;
         success =
           (fun s b la ->
             M.(continue
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


    let choose (l: ('a,'z) partial list) (c: ('a,'z) context): 'z t =
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


    let choose2 (pp: ('a,'z) partial) (qq: ('a,'z) partial): ('a,'z) partial =
      choose [pp;qq]


    let many_base
          (pp: ('a,'z) partial)
          (sufficient: int -> bool)
          (flush: int -> bool)
          (b0:'b)
          (f1: 'b -> 'a -> 'b M.t)
          (f2: 'b -> 'c M.t)
          (c:('c,'z) context)
        : 'z t =
      let rec many (i:int) (b:'b) (s:state): 'z t =
        let continue s b i la =
          M.(continue
               s (f2 b)
               (fun s r -> c.success s r la)
               (fun s e -> c.failure s e 0 la))
        in
        if sufficient i && flush i then
          continue s b i []
        else
          pp {state = s;
              success =
                (fun s a la ->
                  M.continue
                    s (f1 b a)
                    (fun s b -> List.fold_left next (many (i+1) b s) (List.rev la))
                    (fun s e -> c.failure s e 0 la));
              failure =
                (fun s e n la ->
                  if n = 0 && sufficient i then
                    continue s b i la
                  else
                    c.failure s e n la)}
      in
      many 0 b0 c.state


    let many0
          (pp: ('a,'z) partial)
          (f:'a list -> 'c M.t)
        : ('c,'z) partial =
      many_base
        pp (fun _ -> true) (fun _ -> false)
        [] (fun l a -> a :: l |> M.make) f

    let many1
          (pp: ('a,'z) partial)
          (f:'a list -> 'c M.t)
        : ('c,'z) partial =
      many_base
        pp
        (fun i -> i <> 0)
        (fun _ -> false)
        [] (fun l a -> a :: l |> M.make) f


    let count
          (i0:int) (i1:int)
          (pp: ('a,'z) partial)
          (f:'a list -> 'c M.t)
        : ('c,'z) partial =
      assert (0 <= i0);
      assert (i0 <= i1);
      many_base
        pp (fun i -> i0 <= i) (fun i -> i = i1)
        [] (fun l a -> a :: l |> M.make) f



    let optional (pp:('a,'z) partial): ('a option,'z) partial =
      count 0 1 pp
        (fun l ->
          match l with
          | [] ->
             None |> M.make
          | [x] ->
             Some x |> M.make
          | _ ->
             assert false)



    let between
          (f: 'a -> 'b -> 'c -> 'r M.t)
          (pp1: ('a,'z) partial)
          (pp2: ('b,'z) partial)
          (pp3: ('c,'z) partial)
        : ('r,'z) partial =
      join
        (fun ((a,b),c) -> f a b c)
        (join M.make pp1 pp2)
        pp3
  end
