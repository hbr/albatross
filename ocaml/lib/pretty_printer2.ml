open Common
open Printf

module type PRINTER =
  sig
    include Monad.MONAD
    val putc: char -> unit t
    val put_string: string -> unit t
    val put_substring: string -> int -> int -> unit t
    val fill: char -> int -> unit t
  end


type alternative_text = string
type start = int
type length = int
type indent = int
type width  = int
type ribbon = int
type position = int
type open_groups = int



module Document =
  struct
    type t =
      | Nil
      | Concat of t * t
      | Nest of int * t
      | Text of string * start * length
      | Line of alternative_text
      | Group of t

    let empty = Nil

    let (^) (a:t) (b:t): t = Concat(a,b)

    let nest (i:int) (a:t): t = Nest(i,a)

    let text (s:string): t = Text (s,0,String.length s)

    let text_sub (s:string) (i:start) (len:length): t = Text(s,i,len)

    let space: t = Line " "

    let cut: t   = Line ""

    let line (s:string): t = Line s

    let group (d:t): t = Group d

    let bracket (ind:indent) (l:string) (d:t) (r:string): t =
        group (text l ^ (nest ind (cut ^ d)) ^ cut ^ text r)

    let group_nested (ind:indent) (d:t): t =
      group (nest ind d)

    let group_nested_space (ind:indent) (d:t): t =
      group (nest ind (space ^ d))
            (*nest ind (space ^ group d)*)
  end





module Text =
  struct
    type t = {s:string; i0:start; l:length}
    let make s i0 l = {s;i0;l}
    let string t = t.s
    let start t = t.i0
    let length t = t.l
  end




module Line =
  struct
    type t = {s:alternative_text; i:indent}
    let make s i = {s;i}
    let text (l:t): alternative_text = l.s
    let length l = String.length l.s
    let indent l = l.i
  end






(* Gammar

   d ::= t* g* c*                   -- document

   g ::= [| g* c* |]                -- group, at least one LB, either direct or
                                    -- indirect

   c ::= l t* g*                    -- chunk
*)



type chunk = {clen: length;
              line: Line.t;
              texts:  Text.t list;
              cgroups: group list}

and group = {len:length;
             groups: group list;
             chunks: chunk list}

module Chunk =
  struct
    let length (c:chunk): length = c.clen
    let alternative_text (c:chunk): alternative_text = Line.text c.line
    let groups (c:chunk): group list = c.cgroups
    let texts (c:chunk): Text.t list = c.texts
    let make (line:Line.t): chunk =
      {clen = Line.length line; line; texts = []; cgroups = []}
    let add_text (t:Text.t) (c:chunk): chunk =
      assert (c.cgroups = []);
      {c with clen = c.clen + t.Text.l; texts = t :: c.texts}
    let add_group (g:group) (c:chunk): chunk =
      {c with clen = g.len + c.clen; cgroups = g :: c.cgroups}
  end





module Group =
  struct
    let length (g:group): length =  g.len
    let empty = {len = 0; groups = []; chunks = []}
    let groups (g:group): group list = g.groups
    let chunks (g:group): chunk list = g.chunks
    let of_line (l:Line.t): group =
      let c = Chunk.make l in
      {len = Chunk.length c; groups = []; chunks = [c]}
    let add_text (t:Text.t) (g:group): group =
      match g.chunks with
      | [] ->
         assert false (* Illegal call *)
      | c :: tl ->
         {g with len = g.len + t.Text.l; chunks = Chunk.add_text t c :: tl}
    let add_line (l:Line.t) (g:group): group =
      {g with
        len = g.len + String.length l.Line.s;
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
              l:  length;
              o:  open_groups}

    let is_empty (b:t): bool = (b.o = 0)
    let length (b:t): length = b.l
    let count (b:t): open_groups = b.o
    let groups (b:t): group list = b.gs
    let empty: t =
      {gs = []; l = 0; o = 0;}
    let push (g:group) (b:t): t =
      {gs = g :: b.gs; l = Group.length g + b.l; o = b.o + 1}
    let one (g:group): t =
      push g empty
    let add_text (t:Text.t) (b:t): t =
      let open Text in
      match b.gs with
      | [] ->
         assert false (* Illegal call *)
      | g :: tl ->
         {b with
           gs = Group.add_text t g :: tl;
           l  = b.l + t.Text.l}
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






module type PRETTY =
  sig
    include Monad.MONAD

    val text_sub: string -> start -> length -> unit t
    val text: string -> unit t
    val line: alternative_text -> unit t
    val cut: unit t
    val space: unit t
    val nest: indent -> 'a t -> unit t
    val group: 'a t -> unit t
    val fill_of_string: string -> unit t
    val fill_of_strings: string list -> unit t
    val chain: unit t list -> unit t
    val of_document: Document.t -> unit t
  end






module Make:
  functor (P:PRINTER) ->
  sig
    include PRETTY
    val run: indent -> width -> ribbon -> 'a t -> unit P.t
  end
  =
  functor (P:PRINTER) ->
  struct
    type state = {
        width: int;                (* desired maximal line width *)
        ribbon: int;               (* desired maximal ribbon width *)
        mutable line_indent: indent;
        mutable current_indent: indent;
        mutable p: position;       (* on current line at start of buffer *)
        mutable oe:  open_groups;  (* effective *)
        mutable oa:  open_groups;  (* active *)
        mutable o_r: open_groups;  (* to the right of the last open group in
                                      buffer *)
        mutable b: Buffer.t
      }


    let init (i:indent) (width:int) (ribbon:int): state =
      {line_indent = i; current_indent = i;
       width; ribbon;
       p = i;
       oe = 0; oa = 0; o_r = 0;
       b = Buffer.empty}

    let normal (st:state): bool =
      Buffer.is_empty st.b

    let buffering (st:state): bool =
      not (Buffer.is_empty st.b)

    let fits_pos (p:position) (st:state): bool =
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

    include
      Monad.Make(
          struct
            type 'a t = state -> 'a P.t
            let make (a:'a): 'a t =
              fun st -> P.make a
            let bind (m:'a t) (f:'a -> 'b t) (st:state): 'b P.t =
              P.(m st >>= fun a -> f a st)
          end
        )

    let state (st:state): state P.t =
      P.make st

    let print_nothing: unit P.t =
      P.make ()

    let print_list (l:'a list) (f:'a -> unit t): unit t =
      List.fold_right
        (fun a pr -> pr >>= fun _ -> f a)
        l (make ())

    let out_text (s:string) (start:start) (len:length) (st:state): unit P.t =
      st.p <- st.p + len;
      P.put_substring s start len

    let rec out_texts (l:Text.t list): unit t =
      print_list
        l
        (fun t ->
          let open Text in
          out_text t.s t.i0 t.l)

    let out_alternative_text (l:Line.t): unit t =
      let s = Line.text l in
      out_text s 0 (String.length s)

    let out_line (i:indent) (st:state): unit P.t =
      st.p <- i;
      st.line_indent <- i;
      P.(putc '\n' >>= fun _ -> fill ' ' i)


    let line_normal (s:alternative_text) (st:state): unit P.t =
      assert (normal st);
      assert (Buffer.is_empty st.b);
      if 0 < st.oa && fits (String.length s) st then
        (* Start buffering *)
        (st.b <-
           Buffer.open_groups st.oa st.b
           |>  Buffer.add_line (Line.make s st.current_indent);
         st.o_r <- 0;
         print_nothing)
      else
        (active_to_effective st;
         out_line st.current_indent st)


    let rec flush_flatten_group (g:group): unit t =
      flush_flatten_groups g.groups >>= fun _ ->
      flush_flatten_chunks g.chunks

    and flush_flatten_groups (gs:group list): unit t =
      List.fold_right
        (fun g pr -> pr >>= fun _ -> flush_flatten_group g)
        gs
        (make ())

    and flush_flatten_chunks (cs:chunk list): unit t =
      print_list cs flush_flatten_chunk

    and flush_flatten_chunk (c:chunk): unit t =
      out_alternative_text c.line >>= fun _ ->
      out_texts c.texts >>= fun _ ->
      flush_flatten_groups c.cgroups

    let flush_flatten: unit t =
      state >>= fun st ->
      print_list (Buffer.groups st.b) flush_flatten_group >>= fun _ ->
      st.b <- Buffer.empty;
      make ()


    let rec flush_group (g:group) (st:state): unit P.t =
      (* complete group *)
      if fits (Group.length g) st then
        flush_flatten_group g st
      else
        st
        |> (flush_groups g.groups >>= fun _ ->
            flush_chunks g.chunks)
    and flush_chunk (c:chunk): unit t =
      out_line (Line.indent c.line) >>= fun _ ->
      out_texts c.texts >>= fun _ ->
      flush_groups c.cgroups
    and flush_groups (gs:group list): unit t =
      print_list gs flush_group
    and flush_chunks (cs:chunk list): unit t =
      print_list cs flush_chunk


    let flush_effective (st:state): unit P.t =
      (* Flush open groups until buffer fits or is empty. *)
      let flush_incomplete o g st =
        if 0 < st.oa then
          (st.oa <- st.oa - 1;
           st.oe <- st.oe + 1)
        else if o = 0 then
          (* The last incomplete group in the buffer is flushed as well, all
             open groups to the left of the last group become new active
             groups. *)
          (st.oa <- st.o_r;
           st.o_r <- 0);
        (flush_groups g.groups >>= fun _ ->
         flush_chunks g.chunks) st
      in
      let rec flush l o gs st =
        match gs with
        | [] ->
           assert false (* Illegal call *)
        | [g] ->
           assert (not (fits (Group.length g + l) st));
           (* If the first group fitted, then there would be no need to flush
              the group as effective. *)
           flush_incomplete o g st
        | g :: gs ->
           let len =  Group.length g + l in
           P.(flush len (o+1) gs st >>= fun _ ->
              if fits len st then
                (st.b <- Buffer.push g st.b;
                 print_nothing)
              else
                (assert (Buffer.is_empty st.b);
                 flush_incomplete o g st))
      in
      let gs = Buffer.groups st.b in
      st.b <- Buffer.empty;
      flush 0 0 gs st


    let text_sub (s:string) (start:int) (len:int) (st:state): unit P.t =
      assert (0 <= start);
      assert (start+len <= String.length s);
      if normal st then
        out_text s start len st
      else
        (st.b <- Buffer.add_text (Text.make s start len) st.b;
         if buffer_fits st then
           print_nothing
         else
           flush_effective st)


    let text (s:string): unit t =
      text_sub s 0 (String.length s)


    let rec line (s:alternative_text) (st:state): unit P.t =
      if normal st then
        line_normal s st
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
           print_nothing
         else
           flush_effective st
        )
      else
        (* Outside the active group. *)
        (assert (buffer_fits st);
         st.oa <- st.o_r;
         st.o_r <- 0;
         st |> (flush_flatten >>= fun _ -> line s))




    let cut: unit t =
      line ""

    let space: unit t =
      line " "

    let nest (i:int) (m:'a t): unit t =
      let start st =
        st.current_indent <- st.current_indent + i;
        print_nothing
      and close st =
        assert (i <= st.current_indent);
        st.current_indent <- st.current_indent - i;
        print_nothing
      in
      start >>= fun _ -> m >>= fun _ -> close


    let group (m:'a t): unit t =
      let start st =
        if st.oa < Buffer.count st.b then
          st.o_r <- st.o_r + 1
        else
          st.oa <- st.oa + 1;
        print_nothing
      and close st =
        if 0 < st.o_r then
          (assert (st.oa < Buffer.count st.b);
           st.o_r <- st.o_r - 1)
        else if 0 < st.oa then
           st.oa <- st.oa - 1
        else
          (assert (0 < st.oe);
           st.oe <- st.oe - 1);
        print_nothing
      in
      start >>= fun _ ->
      m >>= fun _ ->
      close


    let rec chain (l: unit t list) (st:state): unit P.t =
      match l with
      | [] ->
         print_nothing
      | hd :: tl ->
         P.(hd st >>= fun _ -> chain tl st)


    let fill_of_string (s:string) (st:state): unit P.t =
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
           make ())
        >>= fun _ ->
        if i < len then
          let j = word_end i in
          text_sub s i (j-i) >>= fun _ ->
          fill j
        else
          make ()
      in
      fill 0 st


    let fill_of_strings (l:string list) (st:state): unit P.t =
      let rec fill l first =
        match l with
        | [] ->
           make ()
        | s :: tl ->
           let body = fill_of_string s >>= fun _ -> fill tl false in
           if first then
             body
           else
             group space >>= fun _ -> body
      in
      fill l true st


    let rec of_document (d:Document.t): unit t =
      match d with
      | Document.Nil ->
         make ()
      | Document.Text (s,i,len) ->
         text_sub s i len
      | Document.Line s ->
         line s
      | Document.Concat (a,b) ->
         of_document a >>= fun _ ->
         of_document b
      | Document.Nest (i,d) ->
         nest i (of_document d)
      | Document.Group d ->
         group (of_document d)

    let run (indent:int) (width:int) (ribbon:int) (m:'a t): unit P.t =
      let st = init indent width ribbon in
      P.(m st >>= fun _ ->
         if buffering st then
           flush_flatten st
         else
           print_nothing)
  end (* Make *)


module Printer:
sig
  include PRINTER
  val run: out_channel -> 'a t -> 'a
end =
  struct
    include
      Monad.Make (
          struct
            type 'a t = out_channel -> 'a
            let make (a:'a) (oc:out_channel): 'a = a
            let bind (m:'a t) (f:'a -> 'b t) (oc:out_channel): 'b =
              f (m oc) oc
          end
        )
    let putc (c:char) (oc:out_channel): unit =
      output_char oc c
    let fill (c:char) (n:int) (oc:out_channel): unit =
      for i = 0 to n - 1 do
        output_char oc c
      done
    let put_substring (s:string) (i0:start) (l:length) (oc:out_channel): unit =
      for i = i0 to i0 + l - 1 do
        output_char oc s.[i]
      done
    let put_string (s:string) (oc:out_channel): unit =
      put_substring s 0 (String.length s) oc
    let run (oc:out_channel) (m:'a t): 'a =
      m oc
  end



module Pretty_string =
  struct
    include Make (Monad.String_buffer)
    let string_of (pp:'a t) (size:int) (ind:indent) (w:width) (r:ribbon): string =
      Monad.String_buffer.run
        size
        (run ind w r pp)
  end


let test () =
  let open Printf in
  printf "test pretty printer 2\n";
  let module PP = Make (Monad.String_buffer) in
  let open PP
  in
  let formatw p_flag w pp =
    let s = Pretty_string.string_of pp 200 0 w w in
    if p_flag then
      printf "%s\n" s;
    s
  in
  begin
    let str = "01234 6789 0 2 4 6 8 01 34 6789 0"
    and strlst = ["01234"; "6789 0 2"; "4 6 8 01 34"; "6789 0"]
    and res = "01234 6789\n0 2 4 6 8\n01 34 6789\n0"
    in
    assert (formatw false 10 (fill_of_string str) = res);
    assert (formatw false 10 (fill_of_strings strlst) = res);
  end;

  assert
    begin
      formatw
        false 10
        (nest 4 (chain [text "0123"; cut; text "456"]) >>= fun _ ->
        chain [cut; text "0123"])
      = "0123\n    456\n0123"
    end;

  assert
    begin
      formatw
        false 20
        (group
           (chain [
                (group (chain
                          [text "class";
                           nest 4 (chain [space; text "Natural"]);
                           space; text "create"]));
                nest 4
                  (chain
                     [space;
                      (group
                         (chain
                            [text "0"; line "; "; text "succ(Natural)"]))
                     ]
                  );
                chain [space; text "end"]
              ]
        ))
      = "class Natural create\n    0; succ(Natural)\nend"
    end;

  begin
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
    in
    let maybe = of_document maybe
    in
    assert(
        formatw false 70 maybe
        = "class Maybe(A) create nothing; just(A) end"
      );
    assert(
        formatw false 20 maybe
        = "class\n    Maybe(A)\ncreate\n    nothing; just(A)\nend"
      );
    assert(
        formatw false 15 maybe
        = "class\n    Maybe(A)\ncreate\n    nothing\n    just(A)\nend"
      )
  end;

  begin
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
    in
    let plus = of_document plus in
    assert(
        formatw false 40 plus
        = "(+)(a:Natural,b:Natural): Natural :=\n  "
          ^ "inspect a; (_:Natural) := Natural case\n    "
          ^ "0 := b\n    n.successor := n + b.successor\n  end"
      );
    assert(
        formatw false 39 plus
        = "(+)(a:Natural,b:Natural): Natural :=\n  "
          ^ "inspect\n    a; (_:Natural) := Natural\n  case\n    "
          ^ "0 := b\n    n.successor := n + b.successor\n  end"
      );
    assert(
        formatw false 33 plus
        = "(+)(a:Natural,b:Natural): Natural :=\n  "
          ^ "inspect\n    a; (_:Natural) := Natural\n  case\n    "
          ^ "0 := b\n    n.successor :=\n      n + b.successor\n  end"
      )
  end
