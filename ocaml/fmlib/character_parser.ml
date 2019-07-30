open Common
open Common_module_types
open Parse_combinators

module type CONTEXT =
  sig
    type t
    type msg
    val message: t -> msg
    val line: t -> int
    val column: t -> int
  end

module type DEAD_END =
  sig
    type t
    type msg
    type context
    val message: t -> msg
    val line: t -> int
    val column: t -> int
    val offside: t -> (int * int option) option
    val contexts: t -> context list
  end

module Position:
sig
  type t
  val line: t -> int
  val column: t -> int
  val start: t
  val make: int -> int -> t
  val next: char -> t -> t
end =
  struct
    type t = {line:int; column:int}

    let line (p:t): int = p.line

    let column (p:t): int = p.column

    let start: t =
      {line = 0; column = 0}

    let make line column = {line;column}

    let next_column (p:t): t =
      {p with column = p.column + 1}

    let next_line (p:t): t =
      {line = p.line + 1; column = 0;}

    let next (c:char) (p:t): t =
      if c = '\n' then
        next_line p
      else
        next_column p
  end


module Located =
  struct
    type 'a t =
      {start:Position.t; value:'a; end_:Position.t}

    let make start value end_ =
      {start;value;end_}

    let map (f:'a -> 'b) (l:'a t): 'b t =
      {l with value = f l.value}

    let use (l:'a t) (f: Position.t -> 'a -> Position.t -> 'b): 'b =
      f l.start l.value l.end_

    let value (l:'a t): 'a =
      l.value

    let start (l:'a t): Position.t = l.start

    let end_ (l:'a t) = l.end_
  end


module Indent =
  struct
    type t = {
        lb: int;
        ub: int option;
        abs: bool
      }
    let initial: t = {lb = 0;
                      ub = None;
                      abs = false}


    let bounds (ind:t): int * int option =
      ind.lb, ind.ub

    let is_offside (col:int) (ind:t): bool =
      col < ind.lb

    let token (pos:int) (ind:t): t =
      if ind.abs then
        {lb = pos; ub = Some pos; abs = false}
      else
        match ind.ub with
        | Some ub when ub <= pos ->
           ind
        | _ ->
           {ind with ub = Some pos}

    let absolute (ind:t): t =
      {ind with abs = true}

    let start_indented (strict:bool) (ind:t): t =
      if ind.abs then
        ind
      else
        let incr = if strict then 1 else 0
        in
        {ind with lb = ind.lb + incr; ub = None}

    let end_indented (strict:bool) (ind0:t) (ind:t): t =
      if ind0.abs then
        ind
      else
        let lb =
          if strict then
            ind.lb - 1
          else
            ind.lb
        in
        (assert (ind0.lb <= lb); (* Lower bound cannot decrease. *)
         {ind0 with
           ub =
             Some (
                 match ind0.ub with
                 | None -> lb
                 | Some ub0 -> min ub0 lb)}
        )
  end




module Context (Msg:ANY) =
  struct
    type msg = Msg.t
    type t = {
        pos: Position.t;
        msg: Msg.t;
      }

    let make pos msg: t = {pos; msg}

    let message (c:t) = c.msg

    let line (c:t) = Position.line c.pos

    let column (c:t) = Position.column c.pos

  end



module Error (Msg:ANY) (Ctx:CONTEXT) =
  struct
    type msg = Msg.t
    type context = Ctx.t
    type t = {
        pos: Position.t;
        offside: (int * int option) option;
        msg: Msg.t;
        contexts: context list
      }

    let make pos contexts msg = {pos; msg; contexts; offside = None}

    let add_offside pos e = {e with offside = Some pos}

    let message (e:t) = e.msg

    let line (e:t) = Position.line e.pos

    let column (e:t) = Position.column e.pos

    let offside (e:t) = e.offside

    let contexts (e:t): Ctx.t list =  e.contexts
  end


module State (User:ANY) (Context_msg:ANY) =
  struct
    module Context = Context (Context_msg)

    type context = Context.t

    type t = {
        pos: Position.t;
        indent: Indent.t;
        user: User.t;
        contexts: context list
      }

    let make pos user = {pos;user; indent = Indent.initial; contexts = []}

    let position (s:t): Position.t = s.pos
    let line (s:t): int = Position.line s.pos
    let column (s:t): int = Position.column s.pos

    let next (c:char) (s:t): t =
      {s with
        pos = Position.next c s.pos;
        indent = Indent.token (Position.column s.pos) s.indent}

    let bounds (s:t): int * int option =
      Indent.bounds s.indent

    let is_offside (s:t): bool =
      Indent.is_offside (Position.column s.pos) s.indent


    let absolute (s:t): t =
      {s with indent = Indent.absolute s.indent}

    let start_detached (s:t): t =
      {s with indent = Indent.initial}

    let end_detached (s0:t) (s:t): t =
      {s with indent = s0.indent}

    let start_indented (strict:bool) (s:t): t =
      {s with indent = Indent.start_indented strict s.indent}

    let end_indented (strict:bool) (s0:t) (s:t): t =
      {s with indent = Indent.end_indented strict s0.indent s.indent}

    let user (s:t): User.t = s.user
    let update (f:User.t->User.t) (s:t) =
      {s with user = f s.user}

    let contexts (s:t): context list = s.contexts

    let push_context (msg:Context_msg.t) (s:t): t =
      {s with contexts = Context.make s.pos msg :: s.contexts}

    let pop_context (s:t): t =
      match s.contexts with
      | [] ->
         assert false (* Illegal call *)
      | _ :: contexts ->
         {s with contexts}
  end






module type PARSER =
  sig
    type parser
    val needs_more: parser -> bool
    val has_ended:  parser -> bool
    val position:   parser -> Position.t
    val line:   parser -> int
    val column: parser -> int
    val put_char: parser -> char -> parser
    val put_end: parser -> parser
  end







module Advanced (User:ANY) (Final:ANY) (Problem:ANY) (Context_msg:ANY) =
  struct
    module Token =
      struct
        type t = char option
      end

    module Context = Context (Context_msg)

    module Dead_end = Error (Problem) (Context)

    module State = State (User) (Context_msg)

    module Basic = Generic_parser.Make (Token) (State) (Dead_end) (Final)
    include  Basic

    module Combi = Add_combinators (Basic)
    include Combi

    let state (p:parser): User.t =
      State.user (Basic.state p)

    let position (p:parser): Position.t =
      State.position (Basic.state p)

    let line (p:parser): int =
      State.line (Basic.state p)

    let column (p:parser): int =
      State.column (Basic.state p)

    let error (msg:Problem.t) (st:state): Dead_end.t =
      Dead_end.make (State.position st) (State.contexts st) msg

    let get_state: User.t t =
      Basic.get >>= fun st ->
      return (State.user st)

    let update (f:User.t -> User.t): unit t =
      Basic.update (State.update f)

    let get_position: (Position.t) t =
      Basic.get >>= fun st ->
      return (State.position st)

    let fail (msg:Problem.t): 'a t =
      Basic.get >>= fun st ->
      Basic.fail @@ error msg st

    let token
          (f:state->char->('a,error) result)
          (e:state->error) (* generate error in case there in no character or
                              offside *)
        : 'a t =
      Basic.token
        (fun st t ->
          match t with
          | None ->
             Error (e st)
          | Some c ->
             if State.is_offside st then
               Error (Dead_end.add_offside (State.bounds st) (e st))
             else
               match f st c with
               | Ok a ->
                  Ok (a, State.next c st)
               | Error e ->
                  Error e)


    (* Character Combinators *)

    let expect (p:char -> bool) (msg:Problem.t): char t =
      token
        (fun st c ->
          if p c then
            Ok c
          else
            Error (error msg st))
        (error msg)


    let expect_end (msg:Problem.t): unit t =
      Basic.token
        (fun st t ->
          match t with
          | None ->
             Ok ((), st)
          | Some _ ->
             Error (error msg st))


    let char (c:char) (msg:Problem.t): unit t =
      let e = error msg in
      token
        (fun st d ->
          if c = d then
            Ok ()
          else
            Error (e st))
        e

    let one_of_chars (str:string) (msg:Problem.t): unit t =
      let e = error msg in
      token
        (fun st c ->
          if String.find (fun d -> c = d) 0 str = String.length str then
            Error (e st)
          else
            Ok ())
        e


    let space (msg:Problem.t): unit t =
      char ' ' msg

    let string (str:string) (msg:int -> Problem.t): unit t =
      let len = String.length str in
      let rec parse i =
        if i = len then
          return ()
        else
          char str.[i] (msg i) >>= fun _ -> parse (i+1)
      in
      parse 0


    let word
          (start:char -> bool) (inner:char -> bool) (msg:Problem.t): string t
      =
      let module Arr = Segmented_array in
      expect start msg >>= fun c ->
      loop
        (Arr.singleton c)
        (fun arr ->
          (expect inner msg >>= fun c ->
           return @@ Loop_state.more (Arr.push c arr))
          <|> succeed (Loop_state.exit @@ Arr.to_string arr))


    let whitespace_char (msg:Problem.t): char t =
      expect (fun c -> c = ' ' || c = '\n' || c = '\t') msg

    let whitespace (msg:Problem.t): int t =
      skip_zero_or_more (map (fun _ -> () ) (whitespace_char msg))

    let variable
          (start:char -> bool)
          (inner:char -> bool)
          (reserved: String_set.t)
          (msg:Problem.t)
        : string t =
      Basic.get >>= fun st ->
      word start inner msg >>= fun str ->
      if String_set.mem str reserved then
        Basic.fail (error msg st)
      else
        return str

    let letter (msg:Problem.t): char t =
      expect Char.is_letter msg

    let digit (msg:Problem.t): char t =
      expect Char.is_digit msg


    (* Context *)

    let in_context (msg:Context_msg.t) (p:'a t): 'a t =
      Basic.update (State.push_context msg) >>= fun _ ->
      p >>= fun a ->
      Basic.update State.pop_context >>= fun _ ->
      return a

    (* Located *)
    let located (p:'a t): 'a Located.t t =
      Basic.get >>= fun st1 ->
      p >>= fun a ->
      Basic.get >>= fun st2 ->
      return @@ Located.make (State.position st1) a (State.position st2)


    (* Indentation combinators *)


    let absolute (p:'a t): 'a t =
      Basic.update State.absolute >>= fun _ ->
      p

    let indented (strict:bool) (p:'a t): 'a t =
      Basic.get_and_update (State.start_indented strict) >>= fun st ->
      p >>= fun a ->
      Basic.update (State.end_indented strict st) >>= fun _ ->
      return a

    let detached (p:'a t): 'a t =
      Basic.get_and_update State.start_detached >>= fun st ->
      p >>= fun a ->
      Basic.update (State.end_detached st) >>= fun _ ->
      return a

    let get_bounds: (int * int option) t =
      map State.bounds Basic.get

    let put_char (p:parser) (c:char): parser =
      assert (needs_more p);
      Basic.put_token p (Some c)

    let put_end (p:parser): parser =
      assert (needs_more p);
      Basic.put_token p None

    let make (p:final t) (user:User.t): parser =
      Basic.make_parser (State.make Position.start user) p

    let run (pc:final t) (user:User.t) (s:string): parser =
      let p = ref (make pc user) in
      let i = ref 0
      and len = String.length s in
      while !i <> len && needs_more !p do
        p := put_char !p s.[!i];
        i := !i + 1
      done;
      if needs_more !p then
        p := put_end !p;
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

    let result_string
          (p:parser) (f:final -> string) (g:Problem.t->string): string =
      assert (has_ended p);
      match result p with
      | Ok a ->
         "Ok " ^ f a
      | Error es ->
         "Error ["
         ^ String.concat
             ", "
             (List.map
                (fun e ->
                  let string_of_pair i j =
                    "(" ^ string_of_int i ^ "," ^ string_of_int j ^ ")"
                  in
                  string_of_pair (Dead_end.line e) (Dead_end.column e)
                  ^ (match Dead_end.offside e with
                     | None -> ""
                     | Some (lb, None) -> " offside(" ^ string_of_int lb ^ ")"
                     | Some (lb, Some ub) ->
                        " offside" ^ string_of_pair lb ub)
                  ^ " " ^ g @@ Dead_end.message e)
                es)
         ^ "]"
  end


module Simple (Final:ANY) =
  struct
    module Advanced = Advanced (Unit) (Final) (String) (String)
    include Advanced

    let expect_end: unit t =
      Advanced.expect_end "end"

    let char (c:char): unit t =
      Advanced.char c @@ "'" ^ String.one c ^ "'"

    let one_of_chars (str:string) (msg:string) : unit t =
      Advanced.one_of_chars str msg

    let space: unit t =
      Advanced.space "space"

    let string (str:string): unit t =
      Advanced.string str (fun i -> "'" ^ String.one str.[i] ^ "'")

    let whitespace_char: char t =
      Advanced.whitespace_char "whitespace"

    let whitespace: int t =
      Advanced.whitespace "whitespace"

    let letter: char t =
      Advanced.letter "letter"

    let digit: char t =
      Advanced.digit "digit"

    let make (p:final t): parser =
      Advanced.make p ()

    let run (pc:final t) (s:string): parser =
      Advanced.run pc () s

    let result_string (p:parser) (f:final->string): string =
      Advanced.result_string p f identity
  end



(* ********** *)
(* Unit Tests *)
(* ********** *)

module Simple_test (F:ANY) =
  struct
    include Simple (F)
    let one_error line col msg =
      [Dead_end.make (Position.make line col) [] msg]
    let errors line col msgs =
      List.map (Dead_end.make (Position.make line col) []) msgs
  end
module CP = Simple_test (Char)
module UP = Simple_test (Unit)
module IP = Simple_test (Int)
module SP = Simple_test (String)

let%test _ =
  let open CP in
  let p = run letter "a" in
  has_ended p
  && result p = Ok 'a'
  && column p = 1
  && lookahead p = []


let%test _ =
  let open CP in
  let p = run (return identity
               |= letter
               |. expect_end)
            "a"
  in
  has_ended p
  && result p = Ok 'a'
  && column p = 1
  && lookahead p = []

module Ctx = Context (String)
module Dead_end = Error (String) (Ctx)


let%test _ =
  let open CP in
  let p = run letter "1" in
  has_ended p
  && result p = Error (one_error 0 0 "letter")
  && column p = 0
  && lookahead p = [Some '1']

let%test _ =
  let open UP in
  let p = run (char 'a') "z" in
  has_ended p
  && result p = Error (one_error 0 0 "'a'")
  && column p = 0
  && lookahead p = [Some 'z']

let%test _ =
  let open UP in
  let p = run (char 'a' |. expect_end) "ab"
  in
  has_ended p
  && result p = Error (one_error 0 1 "end")
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
  let p = run (char 'a' |. char 'b' |. expect_end) "ab"
  in
  has_ended p
  && result p = Ok ()
  && column p = 2
  && lookahead p = []

let%test _ =
  let open UP in
  let p = run (char 'a' |. char 'b')
            "a"
  in
  has_ended p
  && result p = Error (one_error 0 1 "'b'")
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
    <|> return ()
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
     >>= fun m -> return (max (n+1) m))
    <|> return 0
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
  && result p = Error (errors 0 5 ["'('"; "')'"])
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
  && result p = Error (one_error 0 1 "'a'")
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
  && result p = Error (one_error 0 2 "')'")
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
       |. expect_end)
      "(b)"
  in
  has_ended p
  && column p = 3
  && result p = Ok ()
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






(* Parser Pipelines *)
let%test _ =
  let module SP = Simple (String) in
  let open SP in
  let p =
    run
      (return (fun c1 c2 c3 -> String.one c1 ^ String.one c2 ^ String.one c3)
       |= letter
       |. letter
       |= digit
       |= letter
       |. digit)
      "ab1d0"
  in
  has_ended p
  && result p = Ok "a1d"
  && column p = 5
  && lookahead p = []


(* Variable *)
module Var =
  struct
    include SP
    let var set =
      variable
        Char.is_letter
        (fun c -> Char.is_letter c || Char.is_digit c)
        set
        "variable"
  end

let%test _ =
  let open Var in
  let p =
    run
      (var String_set.empty)
      "a1b"
  in
  has_ended p
  && result p = Ok "a1b"
  && column p = 3
  && lookahead p = [None]

let%test _ =
  let open Var in
  let p =
    run
      (var String_set.empty)
      "."
  in
  has_ended p
  && result p = Error (one_error 0 0 "variable")
  && column p = 0
  && lookahead p = [Some '.']

let%test _ =
  let open Var in
  let p =
    run
      (var @@ String_set.singleton "class")
      "class"
  in
  has_ended p
  && result p = Error (one_error 0 0 "variable")
  && column p = 5
  && lookahead p = [None]
