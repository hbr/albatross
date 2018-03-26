open Common

module type CHARACTER_TOKEN =
  sig
    type t = Char of char | End
  end



module type POSITION =
  sig
    type t
    val line: t -> int
    val column: t -> int
    val start: t
    val next: char -> t -> t
  end


module Position: POSITION =
  struct
    type t = {line:int; column:int}
    let line (p:t): int = p.line
    let column (p:t): int = p.column
    let start: t = {line = 0; column = 0}
    let next_column (p:t): t = {p with column = p.column + 1}
    let next_line   (p:t): t = {line = p.line +1; column = 0}
    let next (c:char) (p:t): t =
      if c = '\n' then
        next_line p
      else
        next_column p
  end


module type PARSE_POSITION =
  sig
    type t
    val start: t -> Position.t
    val current: t -> Position.t
    val line: t -> int
    val column: t -> int
    val initial: t
    val next: char -> t -> t
    val start_of_current: t -> t
  end


module Sexp =
  struct
    type t =
      | Atom of string
      | Seq of t array
    let string(s:t): string =
      let rec string0 i s =
        match s with
        | Atom str ->
           str
        | Seq arr ->
           let s0 =
             String.concat
               ""
               (List.map (string0 (i+1)) (Array.to_list arr))
           in
           if i = 0 then
             s0
           else
             "(" ^ s0 ^ ")"
      in
      string0 0 s
  end



module Character_token: CHARACTER_TOKEN =
  struct
    type t = Char of char | End
  end


module Parse_position =
  struct
    type t = {start: Position.t; current: Position.t}
    let start   (p:t): Position.t = p.start
    let current (p:t): Position.t = p.current
    let line (p:t): int = Position.line p.current
    let column (p:t): int = Position.column p.current
    let initial: t = {start = Position.start; current = Position.start}
    let next (c:char) (p:t): t =
      {p with current = Position.next c p.current}
    let start_of_current (p:t): t =
      {p with start = p.current}
  end





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

    val parser: ('a,'a) partial -> state -> 'a t
    val consume: 'a t -> token list -> 'a t
    val next:    'a t -> token -> 'a t

    val backtrack: ('a,'a) partial -> ('a,'z) partial

    val token: (token -> 'a M.t) -> ('a,'z) partial

    val succeed: 'a -> ('a,'z) partial
    val fail:    error -> ('a,'z) partial

    val map:  ('a -> 'b) -> ('a,'z) partial ->('b,'z) partial
    val (>>=): ('a,'z) partial -> ('a -> ('b,'z) partial) -> ('b,'z) partial
    val catch: ('a,'z) partial -> (error -> 'a M.t) -> ('a,'z) partial


    val join: ('a,'z) partial -> ('b,'z) partial -> (('a*'b),'z) partial
    val (>>): ('a,'z) partial -> ('b,'z) partial -> (('a*'b),'z) partial

    val choose: (('a,'z) partial list) -> ('a,'z) partial

    val choose2: ('a,'z) partial -> ('a,'z) partial -> ('a,'z) partial

    val many0: ('a,'z) partial -> ('a list,'z) partial

    val many1: ('a,'z) partial -> ('a list,'z) partial

    val many0_separated: ('a,'z) partial -> ('b,'z) partial -> ('a list,'z) partial
    val many1_separated: ('a,'z) partial -> ('b,'z) partial -> ('a list,'z) partial

    val between: ('a,'z) partial ->
                 ('b,'z) partial ->
                 ('c,'z) partial ->
                 ('b,'z) partial

    val with_prefix: ('a,'z) partial ->
                     ('b,'z) partial ->
                     ('b,'z) partial

    val with_suffix: ('a,'z) partial ->
                     ('b,'z) partial ->
                     ('a,'z) partial

    val count: int -> int ->
               (int -> error) ->
               ('a,'z) partial ->
               ('a list,'z) partial

    val optional: ('a,'z) partial -> ('a option,'z) partial

    val matching: ('a,'z) partial -> ('a,'z) partial -> (Sexp.t,'z) partial
  end





(* The generic reactive parser *)
module Generic (Token:ANY) (Error:ANY) (State:ANY)
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

    let parser (pp:('a,'a) partial) (state:state): 'a t =
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

    let consume_look_ahead (p:'a t) (la:tlist): 'a t =
      consume p (List.rev la)


    module M = Monad.State_with_result (State) (Error)


    let succeed (a:'a) (c:('a,'z) context): 'z t =
      c.success c.state a 0 []


    let fail (e:error) (c:('a,'z) context): 'z t =
      c.failure c.state e 0 []


    let (>>=)
          (p:('a,'z) partial)
          (f: 'a -> ('b,'z) partial)
          (c: ('b,'z) context)
        : 'z t =
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


    let map
          (f:'a -> 'b)
          (p:('a,'z) partial)
          (c:('b,'z) context)
        : 'z t =
      p {state = c.state;
         success =
           (fun s a n la ->
             c.success s (f a) n la);
         failure = c.failure}

    let catch (pp:('a,'z) partial) (f:error -> 'a M.t) (c:('a,'z) context): 'z t =
      pp {state = c.state;
          success = c.success;
          failure =
            (fun s e n la ->
              if n = 0 then
                M.continue
                  s (f e)
                  (fun s a -> consume_look_ahead (c.success s a 0 []) la)
                  (fun s e -> c.failure s e n la)
              else
                c.failure s e n la)
        }


    let token (f:token -> 'a M.t) (c:('a,'z) context): 'z t =
      More (c.state,
            M.(fun s t ->
              continue
                s (f t)
                (fun s a -> c.success s a 1 [])
                (fun s e -> c.failure s e 0 [t])
            ))


    let (>>)
          (p: ('a,'z) partial)
          (q: ('b,'z) partial)
          (c: (('a*'b),'z) context)
        : 'z t =
      p {state = c.state;
          success =
            (fun s a n la ->
              consume_look_ahead
                (q {state = s;
                     success =
                       (fun s b np la ->
                         c.success s (a,b) (n+np) la);
                     failure =
                       (fun s e np la -> c.failure s e (n+np) la)})
                la);
          failure = c.failure}

    let join
          (p: ('a,'z) partial)
          (q: ('b,'z) partial)
        : (('a*'b),'z) partial =
      p >> q


    let between
          (pp1: ('a,'z) partial)
          (pp2: ('b,'z) partial)
          (pp3: ('c,'z) partial)
        : ('b,'z) partial =
      pp1 >> pp2 >> pp3 |> map (fun ((a,b),c) -> b)


    let with_prefix (p:('a,'z) partial) (q:('b,'z) partial): ('b,'z) partial =
      p >> q |> map snd


    let with_suffix (p:('a,'z) partial) (q:('b,'z) partial): ('a,'z) partial =
      p >> q |> map fst


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
      f (parser pp c.state) []


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
              consume_look_ahead (pp (context s rest)) la
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


    let count
          (i0:int) (i1:int) (e: int -> error)
          (p: ('a,'z) partial)
        : ('c,'z) partial =
      assert (0 <= i0);
      assert (i0 <= i1);
      let rec cnt i l c =
        (if i = i1 then
           succeed l
         else
           choose2
             (p >>= fun a -> cnt (i+1) (a::l))
             (if i < i0 then
                fail (e i)
              else
                succeed l)) c
      in
      cnt 0 [] |> map List.rev


    let optional (p:('a,'z) partial): ('a option,'z) partial =
      choose2
        (p |> map (fun a -> Some a))
        (succeed None)


    let many0
          (p: ('a,'z) partial)
          (c:('a list,'z) context)
        : 'z t =
      let rec many l c: 'z t =
        (choose2
           (p >>= fun a -> many (a::l))
           (succeed l))
          c
      in
      (many [] |> map List.rev) c

    let many1
          (pp: ('a,'z) partial)
        : ('a list,'z) partial =
      pp >> (many0 pp) |> map (fun (a,l) -> a :: l)

    let many1_separated
          (pp:('a,'z) partial)
          (sep: ('b,'z) partial)
        : ('a list,'z) partial =
      pp >> (with_prefix sep pp |> many0) |> map (fun (a,l) -> a :: l)

    let many0_separated
          (pp:('a,'z) partial)
          (sep: ('b,'z) partial)
        : ('a list,'z) partial =
      choose2
        (many1_separated pp sep)
        (succeed [])




    (* Example: Matching Parentheses:

       parens:  empty
             |  ( parens ) parens

     *)
    let matching
          (pp1: ('a,'z) partial)
          (pp2: ('b,'z) partial)
          (c: (Sexp.t,'z) context)
        : 'z t =
      let rec f (c:(Sexp.t,'z) context): 'z t =
        (choose2
           (pp1 >> f >> pp2 >> f |>
              map
                (fun (((_,s1),_),s2) ->
                  match s2 with
                  | Sexp.Atom _ ->
                     assert false
                  | Sexp.Seq arr ->
                     Sexp.Seq (Array.append [|s1|] arr))
           )
           (succeed (Sexp.Seq [||]))
        ) c
      in
      f c
  end




module Character_parser =
  struct
    module Token =
      struct
        type t = One of char | End
      end

    include Generic (Character_token) (String) (Parse_position)

    let parser (pp:('a,'z) partial): 'a t =
      parser pp Parse_position.initial

    let run_string (pp:('a,'a) partial) (s:string): 'a t =
      let len = String.length s in
      let rec run i p: 'a t =
        if i = len then
          p
        else
          run (i+1) (next p (Character_token.Char s.[i]))
      in
      next (run 0 (parser pp)) Character_token.End

    let expect_base (f:char->bool) (e:char->error): (char,'z) partial =
      token
        (fun t ->
          match t with
          | Character_token.Char c when  f c ->
             M.(update
                  (Parse_position.next c)
                >>= fun _ -> M.make c)
          | Character_token.Char c ->
             M.throw (e c)
          | Character_token.End ->
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
        | Character_token.Char c :: tl ->
           rest0 (c::l) tl
        | Character_token.End :: tl ->
           rest0 l tl
      in
      String_.of_list (rest0 [] la)
    in
    printf "input '%s' " (String.escaped str);
    match p with
    | Accept (s,a,n,la) ->
       printf "(%d,%d) found '%s', consumed %d, rest '%s'\n"
         (Parse_position.line s)
         (Parse_position.column s)
         (f a)
         n (rest la)
    | More (s,g) ->
       printf "(%d,%d) not yet complete\n"
         (Parse_position.line s)
         (Parse_position.column s)
    | Reject (s,e,n,la) ->
       printf "(%d,%d) error %s, consumed %d, rest '%s'\n"
         (Parse_position.line s)
         (Parse_position.column s)
         e n (rest la)
  in
  let run (pp:('a,'a) partial) (str:string) (f:'a -> string): unit =
    print_result str (run_string pp str) f
  in
  printf "Test character parser\n";
  (*run
    (many1_separated (choose2 (many1 letter) (many1 digit)) (expect '\n'))
    "hello\n1\n2\n3 4 r:"
    (fun l ->
      String.concat " " (List.map String_.of_list l))*)
  run
    (count 2 3 (fun i -> "not enough") letter)
    "abcd."
    String_.of_list
  (*run
    (matching (expect '(') (expect ')'))
    "()((()))."
    Sexp.string*)
