open Common



module Readable =
  struct
    type e =
      | String of string * int * int (* start, beyond *)
      | Char of char
      | Fill of int * char

    type t =
      | More of e * (t Lazy.t)
      | Done

    let has_more (r:t): bool =
      r <> Done

    let peek (r:t): char =
      match r with
      | Done ->
         assert false (* Illegal call! *)
      | More (e,_) ->
         match e with
         | String (s,pos,beyond) ->
            assert (pos < beyond);
            s.[pos]
         | Char c ->
            c
         | Fill (n,c) ->
            assert (0 < n);
            c

    let advance (r:t): t =
      match r with
      | Done ->
         assert false (* Illegal call! *)
      | More (e,f) ->
         match e with
         | String (s,pos,beyond) ->
            assert (pos < beyond);
            if pos + 1 = beyond then
              Lazy.force f
            else
              More (String (s,pos+1,beyond),f)
         | Char _ ->
            Lazy.force f
         | Fill (n,c) ->
            assert (0 < n);
            if n = 1 then
              Lazy.force f
            else
              More (Fill (n-1, c), f)


    let make_substring (s:string) (start:int) (len:int) (f:unit -> t): t =
      assert (0 <= start);
      assert (0 <= len);
      assert (start + len <= String.length s);
      if len = 0 then
        f ()
      else
        More (String (s,start,start+len), Lazy.from_fun f)

    let make_char (c:char) (f:unit -> t): t =
      More (Char c, Lazy.from_fun f)

    let make_fill (n:int) (c:char) (f:unit -> t): t =
      if n = 0 then
        f ()
      else
        More (Fill(n,c), Lazy.from_fun f)

    let make_empty: t =
      Done
  end






module Document =
  struct
    type t =
      | Nil
      | Concat of t * t
      | Nest of int * t
      | Text of string * int * int (* start, length *)
      | Line of string (* Alternative text *)
      | Group of t

    let empty = Nil

    let (^) (a:t) (b:t): t = Concat(a,b)

    let nest (i:int) (a:t): t = Nest(i,a)

    let text (s:string): t = Text (s,0,String.length s)

    let text_sub (s:string) (start:int) (len:int): t = Text(s,start,len)

    let space: t = Line " "

    let cut: t   = Line ""

    let line (s:string): t = Line s

    let group (d:t): t = Group d

    let bracket (indent:int) (l:string) (d:t) (r:string): t =
        group (text l ^ (nest indent (cut ^ d)) ^ cut ^ text r)

    let group_nested_space (indent:int) (d:t): t =
      group (nest indent (space ^ d))
            (*nest ind (space ^ group d)*)
  end





module Text =
  struct
    type t =
      | String of string * int * int
      | Fill of int * char
      | Char of char
    let string s i l =
      assert (0 <= i);
      assert (0 <= l);
      assert (i + l <= String.length s);
      String (s,i,l)
    let char c = Char c
    let fill n c = Fill (n,c)
    let length = function
      | String (_,_,l) -> l
      | Fill (n,_) -> n
      | Char _ -> 1
    let apply
          (f1:string -> int -> int -> 'a)
          (f2:int -> char -> 'a)
          (f3:char -> 'a)
        : t -> 'a =
      function
      | String (s,i,l) -> f1 s i l
      | Fill (n,c) -> f2 n c
      | Char c -> f3 c
  end




module Line =
  struct
    type t = {s:string; i:int}
    let make s i = {s;i}
    let text (l:t): string = l.s
    let length l = String.length l.s
    let indent l = l.i
  end






(* Gammar

   d ::= t* g* c*                   -- document

   g ::= [| g* c* |]                -- group, at least one LB, either direct or
                                    -- indirect

   c ::= l t* g*                    -- chunk
*)



type chunk = {clen: int; (* Really needed ?*)
              line: Line.t;
              texts:  Text.t list;
              cgroups: group list}

and group = {len:int;
             groups: group list;
             chunks: chunk list}

module Chunk =
  struct
    let line (c:chunk): Line.t = c.line
    let groups (c:chunk): group list = c.cgroups
    let texts (c:chunk): Text.t list = c.texts
    let make (line:Line.t): chunk =
      {clen = Line.length line; line; texts = []; cgroups = []}
    let add_text (t:Text.t) (c:chunk): chunk =
      assert (c.cgroups = []);
      {c with clen = c.clen + Text.length t; texts = t :: c.texts}
    let add_group (g:group) (c:chunk): chunk =
      {c with clen = g.len + c.clen; cgroups = g :: c.cgroups}
  end





module Group =
  struct
    let length (g:group): int =  g.len
    let empty = {len = 0; groups = []; chunks = []}
    let groups (g:group): group list = g.groups
    let chunks (g:group): chunk list = g.chunks
    let add_text (t:Text.t) (g:group): group =
      match g.chunks with
      | [] ->
         assert false (* Illegal call *)
      | c :: tl ->
         {g with len = g.len + Text.length t; chunks = Chunk.add_text t c :: tl}
    let add_line (l:Line.t) (g:group): group =
      {g with
        len = g.len + Line.length l;
        chunks = Chunk.make l :: g.chunks}
    let add_group (gi:group) (go:group): group =
      let len = go.len + gi.len
      in
      match go.chunks with
      | [] ->
         {go with len; groups = gi :: go.groups}
      | c :: cs ->
         {go with len; chunks = Chunk.add_group gi c :: cs}
  end




module Buffer =
  struct
    type t = {gs: group list;
              l:  int;  (* length *)
              o:  int   (* open groups*) }

    let is_empty (b:t): bool = (b.o = 0)
    let length (b:t): int = b.l
    let count (b:t): int = b.o
    let groups (b:t): group list = b.gs
    let empty: t =
      {gs = []; l = 0; o = 0;}
    let push (g:group) (b:t): t =
      {gs = g :: b.gs; l = Group.length g + b.l; o = b.o + 1}
    let add_text (t:Text.t) (b:t): t =
      let open Text in
      match b.gs with
      | [] ->
         assert false (* Illegal call *)
      | g :: tl ->
         {b with
           gs = Group.add_text t g :: tl;
           l  = b.l + length t}
    let add_line (l:Line.t) (b:t): t =
      match b.gs with
      | [] ->
         assert false (* Illegal call *)
      | g :: tl ->
         {b with
           gs = Group.add_line l g :: tl;
           l  = b.l + Line.length l}
    let open_groups (n:int) (b:t): t =
      assert (0 <= n);
      let rec ogs n gs =
        if n = 0 then
          gs
        else
          Group.empty :: ogs (n-1) gs
      in
      {b with o = b.o + n; gs = ogs n b.gs}
    let close_groups (n:int) (b:t): t =
      assert (0 <= n);
      assert (n < b.o);
      let rec close n gs =
        if n = 0 then
          gs
        else
          match gs with
          | gi :: go :: tl ->
             close
               (n-1)
               (Group.add_group gi go :: tl)
          | _ ->
             assert false (* Illegal call: cannot close group unless there is
                             one group to which it can be added. *)
      in
      {b with o = b.o - n; gs = close n b.gs}
  end






module R = Readable

type state = {
    width: int;                (* desired maximal line width *)
    ribbon: int;               (* desired maximal ribbon width *)
    mutable line_indent: int;
    mutable current_indent: int;
    mutable p: int;            (* position on current line at start of buffer
                                  *)
    mutable oe:  int;          (* open effective groups*)
    mutable oa:  int;          (* open active groups *)
    mutable o_r: int;          (* oprn groups to the right of the last open
                                  group in buffer *)
    mutable b: Buffer.t
  }


let init (i:int) (width:int) (ribbon:int): state =
  {line_indent = i; current_indent = i;
   width; ribbon;
   p = i;
   oe = 0; oa = 0; o_r = 0;
   b = Buffer.empty}

let normal (st:state): bool =
  Buffer.is_empty st.b

let buffering (st:state): bool =
  not (Buffer.is_empty st.b)

let relative_position(st:state): int =
  st.p - st.current_indent

let fits_pos (p:int) (st:state): bool =
  p <= st.width
  && p - st.line_indent <= st.ribbon

let fits (len:int) (st:state): bool =
  fits_pos (st.p + (Buffer.length st.b) + len) st

let buffer_fits (st:state): bool =
  fits 0 st

let active_to_effective (st:state): unit =
  (* Make all active groups effective *)
  assert (normal st);
  st.oe <- st.oe + st.oa;
  st.oa <- 0

module M =
  struct
    type 'a t = state -> ('a -> R.t) -> R.t

    let return (a:'a) (_:state) (k:'a -> R.t): R.t =
      k a

    let (>>=) (m:'a t) (f:'a -> 'b t) (st:state) (k:'b -> R.t): R.t =
      m st (fun a -> f a st k)
  end

include Monad.Of_sig_min (M)

let (>>) (m1:'a t) (m2:'b t): 'b t =
  m1 >>= fun _ -> m2


let state: state t =
  fun st k -> k st

let relative_position:  int t =
  state >>= fun st -> return @@ relative_position st

let update (f:state->unit): unit t =
  state >>= fun st -> return @@ f st

let out_string
      (s:string) (start:int) (len:int)
      (st:state) (k:unit -> R.t)
    : R.t =
  st.p <- st.p + len;
  R.make_substring s start len k

let out_fill (n:int) (c:char) (st:state) (k:unit -> R.t): R.t =
  st.p <- st.p + n;
  R.make_fill n c k

let out_char (c:char) (st:state) (k:unit -> R.t): R.t =
  st.p <- st.p + 1;
  R.make_char c k

let out_text (t:Text.t): unit t =
  Text.apply out_string out_fill out_char t

let out_line (indent:int) (st:state) (k:unit -> R.t): R.t =
  st.p <- indent;
  st.line_indent <- indent;
  R.make_char
    '\n'
    (fun () -> R.make_fill indent ' ' k)

let print_list (l:'a list) (f:'a -> unit t): unit t =
  List.fold_right
    (fun a pr -> pr >>= fun _ -> f a)
    l (return ())

let out_texts (l:Text.t list): unit t =
  print_list
    l
    out_text

let out_alternative_text (l:Line.t): unit t =
  let s = Line.text l in
  out_string s 0 (String.length s)


let line_normal (s:string): unit t =
  state >>= fun st ->
  assert (normal st);
  assert (Buffer.is_empty st.b);
  if 0 < st.oa && fits (String.length s) st then
    (* Start buffering *)
    (st.b <-
       Buffer.open_groups st.oa st.b
       |>  Buffer.add_line (Line.make s st.current_indent);
     st.o_r <- 0;
     return ())
  else
    (active_to_effective st;
     out_line st.current_indent)



let rec flush_flatten_group (g:group): unit t =
  let open Group in
  flush_flatten_groups (groups g) >>= fun _ ->
  flush_flatten_chunks (chunks g)

and flush_flatten_groups (gs:group list): unit t =
  List.fold_right
    (fun g pr -> pr >>= fun _ -> flush_flatten_group g)
    gs
    (return ())

and flush_flatten_chunks (cs:chunk list): unit t =
  print_list cs flush_flatten_chunk

and flush_flatten_chunk (c:chunk): unit t =
  out_alternative_text (Chunk.line c) >>= fun _ ->
  out_texts (Chunk.texts c) >>= fun _ ->
  flush_flatten_groups (Chunk.groups c)


let flush_flatten: unit t =
  state >>= fun st ->
  print_list (Buffer.groups st.b) flush_flatten_group >>= fun _ ->
  st.b <- Buffer.empty;
  return ()


let rec flush_group (g:group): unit t =
  (* complete group *)
  state >>= fun st ->
  if fits (Group.length g) st then
    flush_flatten_group g
  else
    flush_groups g.groups >>= fun _ ->
    flush_chunks g.chunks
and flush_chunk (c:chunk): unit t =
  out_line (Line.indent (Chunk.line c)) >>= fun _ ->
  out_texts c.texts >>= fun _ ->
  flush_groups c.cgroups
and flush_groups (gs:group list): unit t =
  print_list gs flush_group
and flush_chunks (cs:chunk list): unit t =
  print_list cs flush_chunk



let flush_effective: unit t =
  (* Flush open groups until buffer fits or is empty. *)
  state >>= fun st ->
  let flush_incomplete o g =
    if 0 < st.oa then
      (st.oa <- st.oa - 1;
       st.oe <- st.oe + 1)
    else if o = 0 then
      (* The last incomplete group in the buffer is flushed as well, all
             open groups to the left of the last group become new active
             groups. *)
      (st.oa <- st.o_r;
       st.o_r <- 0);
    flush_groups g.groups >>= fun _ ->
    flush_chunks g.chunks
  in
  let rec flush l o gs =
    match gs with
    | [] ->
       assert false (* Illegal call *)
    | [g] ->
       assert (not (fits (Group.length g + l) st));
       (* If the first group fitted, then there would be no need to flush
              the group as effective. *)
       flush_incomplete o g
    | g :: gs ->
       let len =  Group.length g + l in
       flush len (o+1) gs >>= fun _ ->
       if fits len st then
         (st.b <- Buffer.push g st.b;
          return ())
       else
         (assert (Buffer.is_empty st.b);
          flush_incomplete o g)
  in
  let gs = Buffer.groups st.b in
  st.b <- Buffer.empty;
  flush 0 0 gs


let text (t:Text.t): unit t =
  state >>= fun st ->
  if normal st then
    out_text t
  else
    (st.b <- Buffer.add_text t st.b;
     if buffer_fits st then
       return ()
     else
       flush_effective)

let substring (s:string) (start:int) (len:int): unit t =
  assert (0 <= start);
  assert (start+len <= String.length s);
  text (Text.string s start len)


let string (s:string): unit t =
  substring s 0 (String.length s)

let char (c:char): unit t =
  text (Text.char c)

let fill (n:int) (c:char): unit t =
  assert (0 < n);
  text (Text.fill n c)


let rec line (s:string): unit t =
  state >>= fun st ->
  if normal st then
    line_normal s
  else if 0 < st.oa then
    (* Still inside the active group. *)
    (let o = Buffer.count st.b in
     if st.oa <= o then
       st.b <- Buffer.close_groups (o - st.oa) st.b;
     st.b <-
       (let n = if o < st.oa then st.oa - o else st.o_r in
        Buffer.open_groups n st.b
        |> Buffer.add_line (Line.make s st.current_indent));
     st.oa  <- st.oa + st.o_r;
     st.o_r <- 0;
     if buffer_fits st then
       return ()
     else
       flush_effective
    )
  else
    (* Outside the active group. *)
    (assert (buffer_fits st);
     st.oa <- st.o_r;
     st.o_r <- 0;
     flush_flatten >>= fun _ -> line s)


let cut: unit t =
  line ""

let space: unit t =
  line " "

let nest (i:int) (m:'a t): unit t =
  let start st k =
    st.current_indent <- st.current_indent + i;
    k ()
  and close st k =
    assert (i <= st.current_indent);
    st.current_indent <- st.current_indent - i;
    k ()
  in
  start >>= fun _ -> m >>= fun _ -> close

let nest_relative (i:int) (m:'a t): unit t =
  relative_position >>= fun p ->
  nest (i+p) m

let group (m:'a t): unit t =
  let start st =
    if st.oa < Buffer.count st.b then
      st.o_r <- st.o_r + 1
    else
      st.oa <- st.oa + 1
  and close st =
    if 0 < st.o_r then
      (assert (st.oa < Buffer.count st.b);
       st.o_r <- st.o_r - 1)
    else if 0 < st.oa then
      st.oa <- st.oa - 1
    else
      (assert (0 < st.oe);
       st.oe <- st.oe - 1)
  in
  update start >>= fun _ ->
  m >>= fun _ ->
  update close


let rec chain (l: unit t list): unit t =
  match l with
  | [] ->
     return ()
  | hd :: tl ->
     hd >>= fun _ -> chain tl


let fill_paragraph (s:string): unit t =
  let is_blank c = c = ' '
  and is_not_blank c = c <> ' '
  in
  let word_start i = String.find is_not_blank i s
  and word_end   i = String.find is_blank i s
  and len = String.length s
  in
  let rec fill p =
    let i = word_start p in
    (if p < i then
       group space
     else
       return ())
    >>= fun _ ->
    if i < len then
      let j = word_end i in
      substring s i (j-i) >>= fun _ ->
      fill j
    else
      return ()
  in
  fill 0


let rec of_document (d:Document.t): unit t =
  match d with
  | Document.Nil ->
     return ()
  | Document.Text (s,i,len) ->
     substring s i len
  | Document.Line s ->
     line s
  | Document.Concat (a,b) ->
     of_document a >>= fun _ ->
     of_document b
  | Document.Nest (i,d) ->
     nest i (of_document d)
  | Document.Group d ->
     group (of_document d)

let run (indent:int) (width:int) (ribbon:int) (m:unit t): R.t =
  let st = init indent width ribbon
  in
  m st
    (fun () ->
      if buffering st then
        flush_flatten st (fun _ -> R.make_empty)
      else
        R.make_empty
    )



(*
  ------------
  Module Tests
  ------------
 *)

let compare (r:Readable.t) (s:string): bool =
  let len = String.length s in
  let rec comp r i =
    if i = len then
      true
    else
      let more = R.has_more r in
      if not more then
        false
      else
        s.[i] = R.peek r
        && comp (R.advance r) (i+1)
  in
  comp r 0

let print_readable (r:Readable.t): unit =
  let open Printf in
  let rec print r =
    if R.has_more r then
      (printf "%c" (R.peek r);
       print (R.advance r))
    else
      ()
  in
  print r


let test (w:int) (pflag:bool) (pp:unit t) (expected:string): bool =
  let res = compare (run 0 w w pp) expected in
  if pflag then
    print_readable (run 0 w w pp);
  res


let%test _ =
  let str = "01234 6789 0 2 4 6 8 01 34 6789 0"
  and res = "01234 6789\n\
             0 2 4 6 8\n\
             01 34 6789\n\
             0"
  in
  test 10 false (fill_paragraph str) res


let%test _ =
  test
    10 false
    (nest 4 (chain [string "0123"; cut; string "456"]) >>= fun _ ->
     chain [cut; string "0123"])
    "0123\
     \n    456\n\
     0123"


let%test _ =
  compare
    (run 0 20 20
       (group
          (chain [
               (group (chain
                         [string "class";
                          nest 4 (chain [space; string "Natural"]);
                          space; string "create"]));
               nest 4
                 (chain
                    [space;
                     (group
                        (chain
                           [string "0"; line "; "; string "succ(Natural)"]))
                    ]
                 );
               chain [space; string "end"]
             ]
       )))
       "class Natural create\n\
        \    0; succ(Natural)\n\
        end"



let maybe =
  Document.(
    group (group (text "class"
                  ^ nest 4 (space ^ text "Maybe(A)")
                  ^ space
                  ^  text "create")
           ^ nest 4 (space
                     ^ group (text "nothing" ^ line "; " ^ text "just(A)"))
           ^ space
           ^ text "end")
  )
  |> of_document

let%test _ =
  compare
    (run 0 70 70 maybe)
    "class Maybe(A) create nothing; just(A) end"

let%test _ =
  compare
    (run 0 20 20 maybe)
    "class\
     \n    Maybe(A)\n\
     create\
     \n    nothing; just(A)\n\
     end"

let%test _ =
  compare
    (run 0 15 15 maybe)
    "class\
     \n    Maybe(A)\n\
     create\
     \n    nothing\
     \n    just(A)\n\
     end"


let plus =
  let open Document in
  let gns = group_nested_space 2
  in
  let insp =
    group (text "inspect"
           ^ nest
               2
               (space
                ^ group (
                      text "a" ^ line "; "
                      ^ text "(_:Natural) := Natural"))
           ^ space ^ text "case"
      )
  and cases =
    group (
        text "0 :="
        ^ gns (text "b")
        ^ line "; "
        ^ text "n.successor :="
        ^ gns (text "n + b.successor")
      )
  in
  text "(+)(a:Natural,b:Natural): Natural :="
  ^ gns (
        group (
            insp
            ^ nest
                2
                (space ^ cases)
            ^ space ^ text "end")
      )
  |> of_document



let%test _ =
  compare
    (run 0 40 40 plus)
    "(+)(a:Natural,b:Natural): Natural :=\
     \n  inspect a; (_:Natural) := Natural case\
     \n    0 := b\n    n.successor := n + b.successor\
     \n  end"



let%test _ =
  compare
    (run 0 39 39 plus)
    "(+)(a:Natural,b:Natural): Natural :=\
     \n  inspect\
     \n    a; (_:Natural) := Natural\
     \n  case\
     \n    0 := b\
     \n    n.successor := n + b.successor\
     \n  end"


let%test _ =
  compare
    (run 0 33 33 plus)
    "(+)(a:Natural,b:Natural): Natural :=\
     \n  inspect\n    a; (_:Natural) := Natural\
     \n  case\
     \n    0 := b\
     \n    n.successor :=\
     \n      n + b.successor\
     \n  end"
