open Common

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
    val mark: t -> Position.t
    val current: t -> Position.t
    val line: t -> int
    val column: t -> int
    val initial: t
    val mark_current: t -> t
  end



module Parse_position =
  struct
    type t = {start: Position.t; current: Position.t}
    (*unused: let start   (p:t): Position.t = p.start
    let current (p:t): Position.t = p.current*)
    let line (p:t): int = Position.line p.current
    let column (p:t): int = Position.column p.current
    let initial: t = {start = Position.start; current = Position.start}
    let next (c:char) (p:t): t =
      {p with current = Position.next c p.current}
    (* unused: let start_of_current (p:t): t =
      {p with start = p.current}*)
  end




module type LEXER =
  sig
  end

module Make =
  struct

    include Generic_parser.Make (Char) (String) (Parse_position)

    let parser (pp:('a,'z) t): 'a parser =
      parser pp Parse_position.initial

    let run_string (pp:('a,'a) t) (s:string): 'a parser =
      let len = String.length s in
      let rec run i p: 'a parser =
        if i = len then
          p
        else
          run (i+1) (put_token p s.[i])
      in
      put_end (run 0 (parser pp))

    let expect_base (f:char->bool) (e:char->error): (char,'z) t =
      token
        (fun c ->
          if f c then
            M.(update (Parse_position.next c) >>= fun _ -> M.make c)
          else
            M.throw (e c))
        "Unexpected end of stream"

    let expect (c:char): (char,'z) t =
      expect_base
        (fun c1 -> c1 = c)
        (fun c1 -> "Expected '" ^ String.one c ^
                     "', found '" ^ String.one c1 ^ "'")
(* unused:
    let letter (c: (char,'z) context) : 'z parser =
      expect_base
        Char.is_letter
        (fun c -> "Expected letter, found '"  ^ String.one c ^ "'")
        c*)

(* unused:
    let digit (c: (char,'z) context) : 'z parser =
      expect_base
        Char.is_digit
        (fun c -> "Expected digit, found '"  ^ String.one c ^ "'")
        c*)

    (* Example: Matching Parentheses:

       parens:  empty
             |  ( parens ) parens

     *)
    let matching
          (pp1: ('a,'z) t)
          (pp2: ('b,'z) t)
          (c: (Sexp.t,'z) context)
        : 'z parser =
      let rec f (c:(Sexp.t,'z) context): 'z parser =
        ((pp1 >> f >> pp2 >> f |>
              map
                (fun (((_,s1),_),s2) ->
                  match s2 with
                  | Sexp.Atom _ ->
                     assert false
                  | Sexp.Seq arr ->
                     Sexp.Seq (Array.append [|s1|] arr))
         ) <|> succeed (Sexp.Seq [||])
        ) c
      in
      f c
  end





let test (): unit =
  let open Printf in
  let open Make in
  let print_result (str:string) (p:'a parser) (f:'a -> string): unit =
    printf "input '%s' " (String.escaped str);
    continue
      p
      (fun s a n la ->
        printf "(%d,%d) found '%s', consumed %d, rest '%s'\n"
          (Parse_position.line s)
          (Parse_position.column s)
          (f a)
          n (String.of_list (List.rev la)))
      (fun s ->
        printf "(%d,%d) not yet complete\n"
          (Parse_position.line s)
          (Parse_position.column s))
      (fun s e n la ->
        printf "(%d,%d) error %s, consumed %d, rest '%s'\n"
          (Parse_position.line s)
          (Parse_position.column s)
          e n (String.of_list (List.rev la)))
  in
  let run (pp:('a,'a) t) (str:string) (f:'a -> string): unit =
    print_result str (run_string pp str) f
  in
  printf "Test character parser\n";
  (*run
    (many1_separated (many1 letter <|> many1 digit) (expect '\n'))
    "hello\n1\n2\n3 4 r:"
    (fun l ->
      String.concat " " (List.map String.of_list l))*)
  (*run
    (count 2 3 (fun i -> "not enough") letter)
    "abcd."
    String.of_list*)
  run
    (matching (expect '(') (expect ')'))
    "()((())).,-"
    Sexp.string
