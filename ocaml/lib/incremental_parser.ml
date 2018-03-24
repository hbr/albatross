open Common


module type PARSER =
  sig
    type token
    type error
    type state
    type 'a t =
      | Accept of state * 'a * int * token list
      | More of state * (state -> token -> 'a t)
      | Reject of state * error * int * token list

    val next:    'a t -> token -> 'a t
    val consume: 'a t -> token list -> 'a t

    module M: Monad.STATE_WITH_RESULT with type state = state and
                                           type error = error

    type ('a,'z) context =
      {state:state;
       success: state -> 'a -> int -> token list -> 'z t;
       failure: state -> error -> int -> token list -> 'z t}

    type ('a,'z) partial = ('a,'z) context -> 'z t

    val make: ('a,'a) partial -> state -> 'a t
    val consume: 'a t -> token list -> 'a t
    val next:    'a t -> token -> 'a t

    val backtrack: ('a,'a) partial -> ('a,'z) partial

    val token: (token -> 'a M.t) -> ('a,'z) partial

    val join: ('a,'z) partial -> ('b,'z) partial -> (('a*'b),'z) partial

    val join_base: ('a,'z) partial ->
                   ('b,'z) partial ->
                   (('a*'b) -> 'c M.t) ->
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

    val many0: ('a,'z) partial -> ('a list,'z) partial

    val many1: ('a,'z) partial -> ('a list,'z) partial

    val many0_separated: ('a,'z) partial -> ('b,'z) partial -> ('a list,'z) partial
    val many1_separated: ('a,'z) partial -> ('b,'z) partial -> ('a list,'z) partial

    val between: ('a,'z) partial ->
                 ('b,'z) partial ->
                 ('c,'z) partial ->
                 ('b,'z) partial

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
      | Accept of state * 'a * int * token list
      | More of state * (state -> token -> 'a t)
      | Reject of state * error * int * token list

    type tlist = token list

    type ('a,'z) context =
      {state:state;
       success: state -> 'a -> int -> tlist -> 'z t;
       failure: state -> error -> int -> tlist -> 'z t}

    type ('a,'z) partial =
      ('a,'z) context ->
      'z t

    let make (pp:('a,'a) partial) (state:state): 'a t =
      pp {state;
          success = (fun s a n la -> Accept (s,a,n,la));
          failure = (fun s e n la -> Reject (s,e,n,la))}

    let rec consume (p:'a t) (ts:tlist): 'a t =
      match p with
      | Accept (s, a, n, la) ->
         Accept (s, a, n, List.rev_append ts la)
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


    let succeed (a:'a) (c:('a,'z) context): 'z t =
      c.success c.state a 0 []

    let token (f:token -> 'a M.t) (c:('a,'z) context): 'z t =
      More (c.state,
            M.(fun s t ->
              continue
                s (f t)
                (fun s a -> c.success s a 1 [])
                (fun s e -> c.failure s e 0 [t])
            ))

    let join_base
          (pp: ('a,'z) partial)
          (qq: ('b,'z) partial)
          (f: ('a*'b) -> 'r M.t)
          (c: ('r,'z) context)
        : 'z t =
      let cq s a n0 =
        {state = s;
         success =
           (fun s b n la ->
             M.(continue
                  s (f (a,b))
                  (fun s r -> c.success s r (n+n0) la)
                  (fun s e -> c.failure s e (n+n0) la)));
         failure =
           (fun s e n la -> c.failure s e (n+n0) la)}
      in
      let cp =
        {state = c.state;
         success =
           (fun s a n la -> List.fold_left next (cq s a n |> qq) (List.rev la));
         failure = c.failure}
      in
      pp cp


    let join
          (pp: ('a,'z) partial)
          (qq: ('b,'z) partial)
        : (('a*'b),'z) partial =
      join_base pp qq M.make


    let backtrack
          (pp: ('a,'a) partial)
          (c:  ('a,'z) context)
        : 'z t =
      let s0 = c.state in
      let rec f (p:'a t) (used:tlist): 'z t =
        match p with
        | Accept (s,a,n,la) ->
           c.success s a n la
        | More (s,fp) ->
           More (s, fun s t -> f (fp s t) (t::used))
        | Reject (s,e,n,la) ->
           c.failure s0 e 0 used
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
              consume (pp (context s rest)) (List.rev la)
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
      let rec many (i:int) (ntoks:int) (b:'b) (s:state): 'z t =
        let continue s b ntoks (la:tlist) =
          M.(continue
               s (f2 b)
               (fun s r -> c.success s r ntoks la)
               (fun s e -> c.failure s e ntoks la))
        in
        if sufficient i && flush i then
          continue s b ntoks []
        else
          pp {state = s;
              success =
                (fun s a n la ->
                  M.continue
                    s (f1 b a)
                    (fun s b ->
                      List.fold_left next (many (i+1) (ntoks+n) b s) (List.rev la))
                    (fun s e -> c.failure s e n la));
              failure =
                (fun s e n la ->
                  if n = 0 && sufficient i then
                    continue s b ntoks la
                  else
                    c.failure s e (ntoks+n) la)}
      in
      many 0 0 b0 c.state


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
             assert false (* not more than one element is in the list*)
        )


    let many0
          (pp: ('a,'z) partial)
        : ('a list,'z) partial =
      many_base
        pp (fun _ -> true) (fun _ -> false)
        [] (fun l a -> a :: l |> M.make) (fun l -> List.rev l |> M.make)

    let many1
          (pp: ('a,'z) partial)
        : ('a list,'z) partial =
      many_base
        pp
        (fun i -> i <> 0)
        (fun _ -> false)
        [] (fun l a -> a :: l |> M.make) (fun l -> List.rev l |> M.make)

    let many1_separated
          (pp:('a,'z) partial)
          (sep: ('b,'z) partial)
        : ('a list,'z) partial =
      join_base
        pp
        (many0 (join_base sep pp (fun (_,a) -> M.make a)))
        (fun (a,l) -> a :: l |> M.make)

    let many0_separated
          (pp:('a,'z) partial)
          (sep: ('b,'z) partial)
        : ('a list,'z) partial =
      choose2
        (many1_separated pp sep)
        (succeed [])

    let between
          (pp1: ('a,'z) partial)
          (pp2: ('b,'z) partial)
          (pp3: ('c,'z) partial)
        : ('b,'z) partial =
      join_base
        (join pp1 pp2)
        pp3
        (fun ((a,b),c) -> M.make b)
  end







module Character_parser =
  struct
    module Token =
      struct
        type t = One of char | End
      end

    module State =
      struct
        type t = {line:int; column:int}
        let start: t = {line = 0; column = 0}
      end

    include Make (Token) (String) (State)

    let make (pp:('a,'z) partial): 'a t =
      make pp State.start

    let run_string (s:string) (p:'a t): 'a t =
      let len = String.length s in
      let rec run i p: 'a t =
        if i = len then
          p
        else
          run (i+1) (next p (Token.One s.[i]))
      in
      next (run 0 p) Token.End

    let expect_base (f:char->bool) (e:char->error): (char,'z) partial =
      token
        (fun t ->
          match t with
          | Token.One c when  f c ->
             M.(update
                  (fun s ->
                    State.(if c = '\n' then
                             {line = s.line + 1; column = 0}
                           else
                             {s with column = s.column + 1}))
                >>= fun _ -> M.make c)
          | Token.One c ->
             M.throw (e c)
          | Token.End ->
             M.throw ("Unexpected end of stream")
        )

    let expect (c:char): (char,'z) partial =
      expect_base
        (fun c1 -> c1 = c)
        (fun c1 -> "Expected '" ^ String_.one c ^
                     "', found '" ^ String_.one c1 ^ "'")

    let letter (c: (char,'z) context) : 'z t =
      expect_base
        Char_.is_letter
        (fun c -> "Expected letter, found '"  ^ String_.one c ^ "'")
        c

    let digit (c: (char,'z) context) : 'z t =
      expect_base
        Char_.is_digit
        (fun c -> "Expected digit, found '"  ^ String_.one c ^ "'")
        c
  end





let test (): unit =
  let open Printf in
  let open Character_parser in
  let print_result (str:string) (p:'a t) (f:'a -> string): unit =
    let rest la =
      let rec rest0 l la =
        match la with
        | [] ->
           l
        | Token.One c :: tl ->
           rest0 (c::l) tl
        | Token.End :: tl ->
           rest0 l tl
      in
      String_.of_list (rest0 [] la)
    in
    printf "input '%s' " str;
    match p with
    | Accept (s,a,n,la) ->
       printf "(%d,%d) found '%s', consumed %d, rest '%s'\n"
         s.State.line s.State.column
         (f a)
         n (rest la)
    | More (s,g) ->
       printf "(%d,%d) not yet complete\n" s.State.line s.State.column
    | Reject (s,e,n,la) ->
       printf "(%d,%d) error %s, consumed %d, rest '%s'\n"
         s.State.line s.State.column
         e n (rest la)
  in
  let run (p:'a t) (str:string) (f:'a -> string): unit =
    print_result str (run_string str p) f
  in
  printf "Test character parser\n";
  (*run
    (choose2 (many1 letter M.make) (many1 digit M.make) |> make)
    "1234"
    (fun l -> List.rev l |> String_.of_list);*)
  run
    (many1_separated (choose2 (many1 letter) (many1 digit)) (expect ' ') |> make)
    "hello 1 2 3 4 r:"
    (fun l ->
      String.concat " " (List.map String_.of_list l))
  (*run
    ((join letter letter) |> make)
    "h.ello."
    (fun (a,b) -> String_.one a ^ String_.one b)*)
