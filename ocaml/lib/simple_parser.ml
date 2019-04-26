open Common
open Common_module_types
open Parse_combinators



module Position:
sig
  type t
  val line: t -> int
  val column: t -> int
  val start: t
  val next: char -> t -> t
end =
  struct
    type t = {line:int; column:int}
    let line (p:t): int = p.line
    let column (p:t): int = p.column
    let start: t = {line = 0; column = 0}
    let next_column (p:t): t = {p with column = p.column + 1}
    let next_line   (p:t): t = {line = p.line + 1; column = 0}
    let next (c:char) (p:t): t =
      if c = '\n' then
        next_line p
      else
        next_column p
  end





module Simple_parser (F:ANY) =
  struct
    module Token =
      struct
        type t = char option
      end

    module Error =
      struct
        type t = string
      end

    module P = Basic_parser.Make (Token) (Position) (Error) (F)
    include  P

    module C = Combinators (P)
    include C

    let position =
      state

    let line (p:parser): int =
      Position.line (position p)

    let column (p:parser): int =
      Position.column (position p)

    let expect (f:char -> ('a,error) result) (e:error): 'a t =
      token
        (fun pos t ->
          match t with
          | None ->
             Error e
          | Some c ->
             match f c with
             | Ok a ->
                Ok (a, Position.next c pos)
             | Error e ->
                Error e)

    let expect_end (a:final): final t =
      token
        (fun pos t ->
          match t with
          | None ->
             Ok (a, pos)
          | Some _ ->
             Error "end")

    let (<?>) (p:'a t) (s:string): 'a t =
      let es =
        if String.length s = 0 then
          []
        else
          [s] in
      p <?> es

    let char (c:char): unit t =
      let estr = "'" ^ String.one c ^ "'"
      in
      expect
        (fun d ->
          if c = d then
            Ok ()
          else
            Error estr)
        estr

    let one_of_chars (str:string): unit t =
      let errstr = "one of \"" ^ str ^ "\"" in
      expect
        (fun c ->
          let idx = String.find (fun d -> c = d) 0 str
          and len = String.length str in
          if idx < len then
            Ok ()
          else
            Error errstr)
        errstr


    let space: unit t =
      char ' '

    let string (str:string): unit t =
      let len = String.length str in
      let rec parse i =
        if i = len then
          succeed ()
        else
          char str.[i] >>= fun _ -> parse (i+1)
      in
      parse 0

    let letter: char t =
      expect
        (fun c ->
          if Char.is_letter c then
            Ok c
          else
            Error "letter")
        "letter"

    let run (p:final t) (s:string): parser =
      let p = ref (make_parser Position.start p) in
      let i = ref 0
      and len = String.length s in
      while !i <> len && needs_more !p do
        assert (needs_more !p);
        p := put_token !p (Some s.[!i]);
        i := !i + 1
      done;
      if needs_more !p then
        p := put_token !p None;
      !p

    let lookahead_string (p:parser): string =
      assert (has_ended p);
      "["
      ^ String.concat
          "; "
          (List.map
             (fun o ->
               match o with
               | None ->
                  "None"
               | Some c ->
                  "Some " ^ "'" ^ String.one c ^ "'")
             (lookahead p))
      ^
        "]"

    let result_string (p:parser) (f:final -> string): string =
      assert (has_ended p);
      match result p with
      | Ok a ->
         "Ok " ^ f a
      | Error es ->
         "Error ["
         ^ String.concat "; " es
         ^ "]"
  end






(* ********** *)
(* Unit Tests *)
(* ********** *)


module CP = Simple_parser (Char)
module UP = Simple_parser (Unit)
module IP = Simple_parser (Int)



let%test _ =
  let open CP in
  let p = run letter "a" in
  has_ended p
  && result p = Ok 'a'
  && column p = 1
  && lookahead p = []


let%test _ =
  let open CP in
  let p = run (letter >>= expect_end) "a" in
  has_ended p
  && result p = Ok 'a'
  && column p = 1
  && lookahead p = []



let%test _ =
  let open CP in
  let p = run letter "1" in
  has_ended p
  && result p = Error ["letter"]
  && column p = 0
  && lookahead p = [Some '1']

let%test _ =
  let open UP in
  let p = run (char 'a') "z" in
  has_ended p
  && result p = Error ["'a'"]
  && column p = 0
  && lookahead p = [Some 'z']

let%test _ =
  let open UP in
  let p = run (char 'a' >>= expect_end) "ab" in
  has_ended p
  && result p = Error ["end"]
  && column p = 1
  && lookahead p = [Some 'b']

let%test _ =
  let open UP in
  let p = run (char 'a') "a" in
  has_ended p
  && result p = Ok ()
  && column p = 1
  && lookahead p = []

let%test _ =
  let open UP in
  let p = run (char 'a'
               >>= fun _ -> char 'b'
               >>= expect_end)
            "ab"
  in
  has_ended p
  && result p = Ok ()
  && column p = 2
  && lookahead p = []

let%test _ =
  let open UP in
  let p = run (char 'a'
               >>= fun _ -> char 'b')
            "a"
  in
  has_ended p
  && result p = Error ["'b'"]
  && column p = 1
  && lookahead p = [None]




(* Test the [>>-] combinator *)
(* ************************* *)
let%test _ =
  let open UP in
  let p = run (char 'a' >>= fun _ -> char 'b') "ab" in
  has_ended p
  && result p = Ok ()
  && column p = 2
  && lookahead p = []



(* Test the [>>-] combinator *)
(* ************************* *)

let%test _ =
  let open UP in
  let p =
    run (char 'a' >>- fun _ -> char 'b') "ab"
  in
  has_ended p
  && result p = Ok ()
  && column p = 2
  && lookahead p = []


let%test _ =
  let open UP in
  let p =
    run (char 'a' >>- fun _ -> char 'b') "ac"
  in
  has_ended p
  && column p = 0
  && lookahead p = [Some 'a'; Some 'c']



(* Test [optional] *)
(* *************** *)
let%test _ =
  let open UP in
  let p =
    run (map (fun _ -> ()) (char 'a' |> optional)) "a"
  in
  has_ended p
  && column p = 1
  && lookahead p = []


let%test _ =
  let open UP in
  let p =
    run (map (fun _ -> ()) (char 'a' |> optional)) "b"
  in
  has_ended p
  && column p = 0
  && lookahead p = [Some 'b']






(* Test nested parenthesis *)
(* *********************** *)

let parens: unit UP.t =
  let open UP in
  let rec pars (): unit t =
    (consumer (char '(') >>= pars
     >>= fun _ ->
     char ')' >>= pars)
    <|> succeed ()
  in
  pars ()

let nesting: int IP.t =
  let open IP in
  let rec pars (): int t =
    (consumer (char '(')
     >>= pars
     >>= fun n ->
     char ')'
     >>= pars
     >>= fun m -> succeed (max (n+1) m))
    <|> succeed 0
  in
  pars ()

let%test _ =
  let open UP in
  let p = run parens "(())()"
  in
  has_ended p
  && column p = 6
  && lookahead p = [None]

let%test _ =
  let open UP in
  let p = run parens "(())("
  in
  has_ended p
  && column p = 5
  && result p = Error ["'('"; "')'"]
  && lookahead p = [None]

let%test _ =
  let open UP in
  let p = run parens ")"
  in
  has_ended p
  && column p = 0
  && result p = Ok ()
  && lookahead p = [Some ')']


let%test _ =
  let open IP in
  let p = run nesting "(())()"
  in
  has_ended p
  && result p = Ok 2
  && lookahead p = [None]


let%test _ =
  let open IP in
  let p = run nesting "(()(()))"
  in
  has_ended p
  && result p = Ok 3
  && lookahead p = [None]


(* String parser *)
(* ************* *)

let%test _ =
  let open UP in
  let p = run (string "abcd") "abcd"
  in
  has_ended p
  && column p = 4
  && result p = Ok ()
  && lookahead p = []

let%test _ =
  let open UP in
  let p = run (string "(a)" <|> string "(b)") "(b)"
  in
  has_ended p
  && column p = 1
  && result p = Error ["'a'"]
  && lookahead p = [Some 'b']




(* Backtrackable *)
(* ************* *)

let%test _ =
  let open UP in
  let p =
    run
      (backtrackable (string "(a)"))
      "(a"
  in
  has_ended p
  && column p = 0
  && result p = Error ["')'"]
  && lookahead p = [Some '('; Some 'a'; None]


let%test _ =
  let open UP in
  let p =
    run
      (backtrackable (string "(a)")
       <|> string "(b)")
      "(b)"
  in
  has_ended p
  && column p = 3
  && result p = Ok ()
  && lookahead p = []


let%test _ =
  let open UP in
  let p =
    run
      ((backtrackable (string "(a)")
        <|> string "(b)")
       >>= expect_end)
      "(b)"
  in
  has_ended p
  && column p = 3
  && result p = Ok ()
  && lookahead p = []





(* Sentences and Error Messages *)
(* **************************** *)
module String_list =
  struct
    type t = string list
  end

module SLP = Simple_parser (String_list)

let word: string SLP.t =
  let open SLP in
  one_or_more letter >>= fun l -> succeed (String.of_list l)

let separator: int SLP.t =
  let open SLP in
  skip_one_or_more (space <|> char ',')

let sentence: string list SLP.t =
  let open SLP in
  one_or_more_separated word separator >>= fun lst ->
  one_of_chars ".?!" >>= fun _ ->
  succeed lst


let%test _ =
  let open SLP in
  let p = run sentence "hi,di,hi." in
  result p = Ok ["hi"; "di"; "hi"]

let%test _ =
  let open SLP in
  let p = run sentence "hi,,di hi!" in
  result p = Ok ["hi"; "di"; "hi"]

let%test _ =
  let open SLP in
  let p = run sentence "hi       di        hi?" in
  result p = Ok ["hi"; "di"; "hi"]


let%test _ =
  let open SLP in
  let p = run sentence "hi,123" in
  has_ended p
  && result p = Error ["' '" ; "','" ; "letter"]
  && column p = 3
  && lookahead p = [Some '1']



let word: string SLP.t =
  let open SLP in
  one_or_more letter <?> "word" >>= fun l -> succeed (String.of_list l)

let separator: int SLP.t =
  let open SLP in
  skip_one_or_more (space <|> char ',')

let sentence: string list SLP.t =
  let open SLP in
  one_or_more_separated word separator >>= fun lst ->
  one_of_chars ".?!" >>= fun _ ->
  succeed lst

let%test _ =
  let open SLP in
  let p = run sentence "hi,123" in
  has_ended p
  && result p = Error ["' '" ; "','" ; "word"]
  && column p = 3
  && lookahead p = [Some '1']


let word: string SLP.t =
  let open SLP in
  one_or_more letter <?> "word" >>= fun l -> succeed (String.of_list l)

let separator: int SLP.t =
  let open SLP in
  skip_one_or_more (space <|> char ',' <?> "")

let sentence: string list SLP.t =
  let open SLP in
  one_or_more_separated word separator >>= fun lst ->
  one_of_chars ".?!" >>= fun _ ->
  succeed lst

let%test _ =
  let open SLP in
  let p = run sentence "hi,123" in
  has_ended p
  && result p = Error ["word"]
  && column p = 3
  && lookahead p = [Some '1']
