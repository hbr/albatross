open Common_module_types
open Common


module type BASIC =
  sig
    type n_consumed = int
    type token
    type error
    type state
    type 'a parser

    val put_token:'a parser -> token -> 'a parser
    val put_end:  'a parser -> 'a parser
    val consume:  'a parser -> token list -> 'a parser

    val continue: 'a parser ->
                  (state -> 'a -> n_consumed -> token list -> 'z) ->
                  (state -> 'z) ->
                  (state -> error -> n_consumed -> token list -> 'z) ->
                  'z

    module M: Monad.STATE_WITH_RESULT with type state = state and
                                           type error = error

    type ('a,'z) context

    type ('a,'z) t = ('a,'z) context -> 'z parser

    val parser: ('a,'a) t -> state -> 'a parser

    val backtrack: ('a,'a) t -> ('a,'z) t

    val token: (token -> 'a M.t) -> error -> ('a,'z) t

    val succeed: 'a -> ('a,'z) t
    val fail:    error -> ('a,'z) t

    val (>>=): ('a,'z) t -> ('a -> ('b,'z) t) -> ('b,'z) t
    val catch: ('a,'z) t -> (error -> ('a,'z) t) -> ('a,'z) t
    val map: ('a -> 'b) -> ('a,'z) t -> ('b,'z) t
    val map_error: (error -> error) -> ('a,'z) t -> ('a,'z) t
  end


module type COMBINATOR =
  sig
    include BASIC

    val (>>): ('a,'z) t -> ('b,'z) t -> (('a*'b),'z) t

    val (<|>): ('a,'z) t -> ('a,'z) t -> ('a,'z) t

    val many0: ('a,'z) t -> ('a list,'z) t

    val many1: ('a,'z) t -> ('a list,'z) t

    val many0_separated: ('a,'z) t -> ('b,'z) t -> ('a list,'z) t
    val many1_separated: ('a,'z) t -> ('b,'z) t -> ('a list,'z) t

    val between: ('a,'z) t ->
                 ('b,'z) t ->
                 ('c,'z) t ->
                 ('b,'z) t

    val with_prefix: ('a,'z) t ->
                     ('b,'z) t ->
                     ('b,'z) t

    val with_suffix: ('a,'z) t ->
                     ('b,'z) t ->
                     ('a,'z) t

    val count: int -> int ->
               (int -> error) ->
               ('a,'z) t ->
               ('a list,'z) t

    val optional: ('a,'z) t -> ('a option,'z) t
  end (* COMBINATOR *)






(* The generic reactive parser *)
module Basic (Token:ANY) (Error:ANY) (State:ANY)
       : (BASIC with type token = Token.t
                 and type error = Error.t
                 and type state = State.t)
  =
  struct
    type n_consumed = int
    type token = Token.t
    type error = Error.t
    type state = State.t
    type tok = One of token | End
    type 'a parser =
      | Accept of state * 'a * n_consumed * tok list
      | More of state * (state -> tok -> 'a parser)
      | Reject of state * error * int * tok list

    type tlist = tok list

    type ('a,'z) context =
      {state:state;
       success: state -> 'a -> int -> tlist -> 'z parser;
       failure: state -> error -> int -> tlist -> 'z parser}

    type ('a,'z) t = ('a,'z) context -> 'z parser

    let parser (pp:('a,'a) t) (state:state): 'a parser =
      pp {state;
          success = (fun s a n la -> Accept (s,a,n,la));
          failure = (fun s e n la -> Reject (s,e,n,la))}


    let next0 (p:'a parser) (t:tok): 'a parser =
      match p with
      | Accept (_,_,_,End::_) | Reject (_,_,_,End::_)->
         assert false (* cannot accept token beyond end marker *)
      | Accept (s,a,n,la) ->
         Accept (s,a,n, t :: la)
      | More (s,f) ->
         f s t
      | Reject (s,e,n,la) ->
         Reject (s,e,n, t :: la)


    let put_token (p:'a parser) (t:token): 'a parser =
      next0 p (One t)


    let put_end (p:'a parser): 'a parser =
      match p with
      | Accept (_,_,_,End::_) | Reject (_,_,_,End::_)->
         assert false (* cannot accept token beyond end marker *)
      | Accept (s,a,n,la) ->
         Accept (s,a,n, End :: la)
      | More (s,f) ->
         f s End
      | Reject (s,e,n,la) ->
         Reject (s,e,n, End :: la)


    let consume (p:'a parser) (ts:token list): 'a parser =
      List.fold_left put_token p ts

    let revert_la (l:tlist): token list =
      let rec revert l1 l2 =
        match l1 with
        | [] -> List.rev l2
        | End :: tl ->
           revert tl l2
        | One t :: tl ->
           revert tl (t::l2)
      in
      revert l []

    let continue
          (p:'a parser)
          (f1:state -> 'a -> n_consumed -> token list -> 'z)
          (f2:state -> 'z)
          (f3:state -> error -> n_consumed -> token list -> 'z)
        : 'z =
      match p with
      | Accept (s,a,n,la) ->
         f1 s a n (revert_la la)
      | More (s,_) ->
         f2 s
      | Reject (s,e,n,la) ->
         f3 s e n (revert_la la)

    let consume_look_ahead (p:'a parser) (la:tlist): 'a parser =
      List.fold_left next0 p (List.rev la)


    module M = Monad.State_with_result (State) (Error)


    let succeed (a:'a) (c:('a,'z) context): 'z parser =
      c.success c.state a 0 []


    let fail (e:error) (c:('a,'z) context): 'z parser =
      c.failure c.state e 0 []


    let (>>=)
          (p:('a,'z) t)
          (f: 'a -> ('b,'z) t)
          (c: ('b,'z) context)
        : 'z parser =
      p {state = c.state;
         success =
           (fun s a n la ->
             consume_look_ahead
               ((f a)
                  {state = s;
                   success =
                     (fun s b n1 la ->
                       c.success s b (n+n1) la);
                   failure =
                     (fun s e n1 la ->
                       c.failure s e (n+n1) la)})
               la);
         failure = c.failure}


    let catch
          (p:('a,'z) t)
          (f:error -> ('a,'z) t)
          (c:('a,'z) context)
        : 'z parser =
      p {state = c.state;
         success = c.success;
         failure =
           (fun s e n la ->
             if n = 0 then
               consume_look_ahead (f e c) la
              else
                c.failure s e n la)
        }


    let backtrack
          (pp: ('a,'a) t)
          (c:  ('a,'z) context)
        : 'z parser =
      let s0 = c.state in
      let rec f (p:'a parser) (used:tlist): 'z parser =
        match p with
        | Accept (s,a,n,la) ->
           c.success s a n la
        | More (s,fp) ->
           More (s, fun s t -> f (fp s t) (t::used))
        | Reject (_,e,_,_) ->
           c.failure s0 e 0 used
      in
      f (parser pp c.state) []


    let token (f:token -> 'a M.t) (e:error) (c:('a,'z) context): 'z parser =
      More (c.state,
            M.(fun s t ->
              match t with
              | One t0 ->
                 continue
                   s (f t0)
                   (fun s a -> c.success s a 1 [])
                   (fun s e -> c.failure s e 0 [t])
              | End ->
                 c.failure s e 0 [t]
            ))

    let map
          (f:'a -> 'b)
          (p:('a,'z) t)
          (c:('b,'z) context)
        : 'z parser =
      p {state = c.state;
         success =
           (fun s a n la ->
             c.success s (f a) n la);
         failure = c.failure}

    let map_error
          (f:error -> error)
          (p: ('a,'z) t)
          (c: ('a,'z) context)
        : 'z parser =
      p {state = c.state;
         success = c.success;
         failure =
           (fun s e n la ->
             c.failure s (f e) n la)}
  end (* Basic *)










module Combinator (P:BASIC) =
  struct
    include P

    let (>>)
          (p: ('a,'z) t)
          (q: ('b,'z) t)
          : (('a*'b),'z) t =
      p >>= fun a -> q |> map (fun b -> a,b)


    let between
          (pp1: ('a,'z) t)
          (pp2: ('b,'z) t)
          (pp3: ('c,'z) t)
        : ('b,'z) t =
      pp1 >> pp2 >> pp3 |> map (fun ((_,b),_) -> b)


    let with_prefix (p:('a,'z) t) (q:('b,'z) t): ('b,'z) t =
      p >> q |> map snd


    let with_suffix (p:('a,'z) t) (q:('b,'z) t): ('a,'z) t =
      p >> q |> map fst


    let (<|>) (p: ('a,'z) t) (q: ('a,'z) t): ('a,'z) t =
      catch p (fun _ -> q)

    let count
          (i0:int) (i1:int) (e: int -> error)
          (p: ('a,'z) t)
        : ('c,'z) t =
      assert (0 <= i0);
      assert (i0 <= i1);
      let rec cnt i l c =
        (if i = i1 then
           succeed l
         else
           (p >>= fun a -> cnt (i+1) (a::l))
           <|> if i < i0 then
                 fail (e i)
               else
                 succeed l) c
      in
      cnt 0 [] |> map List.rev


    let optional (p:('a,'z) t): ('a option,'z) t =
      (p |> map (fun a -> Some a))
      <|> (succeed None)


    let many0 (p: ('a,'z) t): ('a list,'z) t =
      let rec many l c: 'z parser =
        ((p >>= fun a -> many (a::l)) <|> succeed l)
          c
      in
      many [] |> map List.rev


    let many1
          (pp: ('a,'z) t)
        : ('a list,'z) t =
      pp >> (many0 pp) |> map (fun (a,l) -> a :: l)


    let many1_separated
          (pp:('a,'z) t)
          (sep: ('b,'z) t)
        : ('a list,'z) t =
      pp >> (with_prefix sep pp |> many0) |> map (fun (a,l) -> a :: l)


    let many0_separated
          (pp:('a,'z) t)
          (sep: ('b,'z) t)
        : ('a list,'z) t =
        many1_separated pp sep <|> succeed []
  end


module Make (Token:ANY) (Error:ANY) (State:ANY) =
  Combinator (Basic (Token) (Error) (State))
