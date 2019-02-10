open Common
open Printf

module type PRINTER =
  sig
    include Monad.MONAD
    val putc: char -> unit t
    val put_string: string -> unit t
    val put_substring: int -> int -> string -> unit t
    val fill: char -> int -> unit t
  end





type command =
  | Text of int * int * string
  | Line of string
  | Open_group
  | Close_group
  | Start_indent of int
  | End_indent of int


module Counter:
sig
  type t
  val position: t -> int
  val open_active: t -> int
  val make: int -> t
  val copy: t -> t
  val advance: int -> t -> unit
  val line: int -> t -> unit
  val open_group: t -> unit
  val close_group: t -> unit
  val active_to_non_flatten: t -> unit
end =
  struct
    type t = {
        mutable pos: int;
        mutable o_n: int;
        mutable o_a: int
      }
    let make (pos:int): t =
      {pos; o_n = 0; o_a = 0}

    let copy (c:t): t =
      {pos = c.pos; o_n = c.o_n; o_a = c.o_a}

    let open_active (c:t): int =
      c.o_a

    let position (c:t): int =
      c.pos

    let advance (len:int) (c:t): unit =
      c.pos <- c.pos + len

    let line (ind:int) (c:t): unit =
      c.pos <- ind

    let open_group (c:t): unit =
      c.o_a <- c.o_a + 1

    let close_group (c:t): unit =
      if c.o_a > 0 then
        c.o_a <- c.o_a - 1
      else
        begin
          assert (c.o_n > 0);
          c.o_n <- c.o_n - 1
        end

    let active_to_non_flatten (c:t): unit =
      c.o_n <- c.o_n + c.o_a;
      c.o_a <- 0
  end



module State:
sig
  type t
  val start: int -> int -> int -> t
  val indentation: t -> int
  val open_active: t -> int
  val position: t -> int
  val buffering: t -> bool
  val is_pending_inner_group: t -> bool
  val has_active: t -> bool
  val not_buffering: t -> bool
  val open_group: t -> unit
  val close_group: t -> unit
  val start_indent: int -> t -> unit
  val end_indent: int -> t -> unit
  val fits: int -> t -> bool
  val advance: int -> t -> unit
  val line: t -> unit
  val start_buffering: string -> t -> unit
  val buffer_text: int -> int -> string -> t -> unit
  val buffer_line: string -> t -> unit
  val pop_buffer: bool -> t -> command list
end =
  struct

    type t = {width: int;          (* desired maximal line width *)
              ribbon: int;         (* desired maximal ribbon width *)
              mutable lindent: int;(* indentation of the current line *)
              mutable indent: int; (* current indentation *)
              mutable counter: Counter.t;
              mutable buf: (command list * Counter.t) option
             }

    (* invariant:

       buffering: buffer starts with line break within the active group (the
       pending line break) and all commands in the buffer would fit flattened
       on the current line.

     *)

    let start (indent:int) (width:int) (ribbon:int): t =
      assert (0 <= indent);
      assert (0 <= width);
      assert (0 <= ribbon);
      {indent;
       lindent = indent;
       width;
       ribbon;
       counter = Counter.make indent;
       buf = None}

    let indentation (st:t): int =
      st.indent

    let buffering (st:t): bool =
      match st.buf with
      | None ->
         false
      | _ ->
         true

    let not_buffering (st:t): bool =
      not (buffering st)

    let is_pending_inner_group (st:t): bool =
      (* Is the pending line break within an inner group of the current active
         group?  *)
      match st.buf with
      | None ->
         assert false (* Illegal call *)
      | Some (buf,counter) ->
         Counter.(
          0 < open_active st.counter
          && open_active st.counter < open_active counter)

    let open_active (st:t): int =
      Counter.open_active st.counter

    let has_active (st:t): bool =
      0 < open_active st

    let position (st:t): int =
      (* The position on the current line. *)
      Counter.position st.counter

    let fits (len:int) (st:t): bool =
      (* Do [len] additional characters still fit on the current line? *)
      let p = position st + len in
      p <= st.width && p <= st.lindent + st.ribbon


    let open_group (st:t): unit =
      match st.buf with
      | None ->
         Counter.open_group st.counter
      | Some (buf,counter) ->
         if has_active st then
           Counter.open_group st.counter;
         st.buf <- Some (Open_group :: buf, counter)

    let close_group (st:t): unit =
      match st.buf with
      | None ->
         Counter.close_group st.counter
      | Some (buf,counter) ->
         if has_active st then
           Counter.close_group st.counter;
         st.buf <- Some (Close_group :: buf, counter)

    let start_indent (i:int) (st:t): unit =
      assert (0 <= i);
      match st.buf with
      | None ->
         st.indent <- st.indent + i
      | Some (buf,counter) ->
         st.buf <- Some (Start_indent i :: buf, counter)

    let end_indent (i:int) (st:t): unit =
      assert (0 <= i);
      assert (i <= indentation st);
      match st.buf with
      | None ->
         st.indent <- st.indent - i
      | Some (buf,counter) ->
         st.buf <- Some (End_indent i :: buf, counter)

    let advance (len:int) (st:t): unit =
      Counter.advance len st.counter

    let line (st:t): unit =
      assert (not_buffering st);
      st.lindent <- st.indent;
      match st.buf with
      | None ->
         Counter.line st.indent st.counter
      | _ ->
         assert false (* Illegal call *)


    let start_buffering (s:string) (st:t): unit =
      assert (not_buffering st);
      assert (0 < open_active st);
      let len = String.length s
      in
      assert (fits len st);
      let counter = Counter.copy st.counter in
      advance len st;
      st.buf <- Some ([Line s], counter)


    let buffer_text (start:int) (len:int) (s:string) (st:t): unit =
      assert (buffering st);
      assert (fits len st);
      match st.buf with
      | None ->
         assert false (* Illegal call *)
      | Some (buf,counter) ->
         advance len st;
         st.buf <- Some (Text (start,len,s) :: buf, counter)


    let buffer_line (s:string) (st:t): unit =
      assert (buffering st);
      assert (not (is_pending_inner_group st));
      let len = String.length s in
      assert (fits len st);
      match st.buf with
      | None ->
         assert false (* Illegal call *)
      | Some (buf,counter) ->
         advance len st;
         st.buf <- Some (Line s :: buf, counter)


    let pop_buffer (flatten:bool) (st:t): command list =
      assert (buffering st);
      match st.buf with
      | None ->
         assert false (* Illegal call *)
      | Some (buf,counter) ->
         if not flatten then
           Counter.active_to_non_flatten counter;
         st.buf <- None;
         st.counter <- counter;
         List.rev buf
  end





module Make  (P:PRINTER):
sig
  include Monad.MONAD

  val text_sub: int -> int -> string -> unit t
  val text: string -> unit t
  val line: string -> unit t
  val cut: unit t
  val space: unit t
  val nest: int -> 'a t -> unit t
  val group: 'a t -> unit t
  val fill_words: string -> unit t
  val fill_paragraph: string list -> unit t
  val chain: unit t list -> unit t
  val run: int -> int -> int -> 'a t -> unit P.t
end
  =
  struct
    let print_nothing: unit P.t =
      P.make ()

    type state = State.t

    type 'a tp = 'a P.t * state

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

    let out_text (start:int) (len:int) (s:string) (st:state): unit P.t =
      assert (State.not_buffering st);
      State.advance len st;
      P.put_substring start len s

    let out_line (st:state): unit P.t =
      assert (State.not_buffering st);
      State.line st;
      P.(putc '\n' >>= fun _ -> State.indentation st |> fill ' ')

    let out_cmd (c:command) (flatten:bool) (st:state): unit P.t =
      assert (State.not_buffering st);
      match c with
      | Text (start,len,s) ->
         out_text start len s st

      | Line s when flatten ->
         out_text 0 (String.length s) s st

      | Line s ->
         out_line st

      | Open_group ->
         State.open_group st;
         print_nothing

      | Close_group ->
         State.close_group st;
         print_nothing

      | Start_indent i ->
         State.start_indent i st;
         print_nothing

      | End_indent i ->
         State.end_indent i st;
         print_nothing

    let flush (flatten:bool) (st:state): unit P.t =
      (* write the commands in the buffer either in flattening or in non
         flattening mode.

         flattening mode: The next command is a line break outside the active
         group or inside the active group but outside the group of the pending
         line break and still fitting.

         non flattening mode: The next command would make the buffer to big to
         fit on the current line.
       *)
      assert (State.buffering st);
      let buf = State.pop_buffer flatten st in
      let rec write buf =
        match buf with
        | [] ->
           assert false (* Illegal call: The buffer must at least contain the
                           pending line break! *)
        | [c] ->
           out_cmd c flatten
        | c :: tl ->
           out_cmd c flatten >>= fun _ -> write tl
      in
      write buf st


    let text_sub (start:int) (len:int) (s:string) (st:state): unit P.t =
      assert (0 <= start);
      assert (start+len <= String.length s);
      if State.buffering st then
        if State.fits len st then
          (State.buffer_text start len s st;
           print_nothing)
        else
          (flush false >>= fun _ -> out_text start len s) st
      else
        out_text start len s st

    let text (s:string): unit t =
      text_sub 0 (String.length s) s



    let line (s:string) (st:state): unit P.t =
      let len = String.length s
      in
      let start_buffering_or_out st =
        if State.has_active st && State.fits len st then
          (State.start_buffering s st;
           print_nothing)
        else
          out_line st
      in
      if State.buffering st then
        if State.has_active st && State.fits len st then
          if State.is_pending_inner_group st then
            (* new pending line break *)
            P.(flush true st >>= fun _ ->
               State.start_buffering s st;
               print_nothing)
          else
            (State.buffer_line s st;
             print_nothing)
        else (* not active or not fits*)
          (flush true >>= fun _ -> start_buffering_or_out) st
      else
        start_buffering_or_out st


    let cut: unit t =
      line ""

    let space: unit t =
      line " "

    let nest (i:int) (m:'a t): unit t =
      let start st =
        State.start_indent i st;
        print_nothing
      and close st =
        State.end_indent i st;
        print_nothing
      in
      start >>= fun _ -> m >>= fun _ -> close


    let group (m:'a t): unit t =
      let start st =
        State.open_group st;
        print_nothing
      and close st =
        State.close_group st;
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

    let fill_words (s:string) (st:state): unit P.t =
      let word_start i = String.find (fun c -> c <> ' ') i s
      and word_end   i = String.find (fun c -> c =  ' ') i s
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
          text_sub i (j-i) s >>= fun _ ->
          fill j
        else
          make ()
      in
      fill 0 st


    let fill_paragraph (l:string list) (st:state): unit P.t =
      let rec fill l first =
        match l with
        | [] ->
           make ()
        | s :: tl ->
           let body = fill_words s >>= fun _ -> fill tl false in
           if first then
             body
           else
             group space >>= fun _ -> body
      in
      fill l true st


    let run (indent:int) (width: int) (ribbon:int) (m:'a t): unit P.t =
      let st = State.start indent width ribbon in
      P.(m st >>= fun _ ->
         if State.buffering st then
           flush true st
         else
           print_nothing)
  end



let test () =
  let open Printf in
  printf "test pretty printer 2\n";
  let module PP = Make (Monad.String_buffer) in
  let open PP
  in
  let buf = Monad.String_buffer.run 200 in
  let formatw p_flag w pp =
    let s = run 0 w w pp |> buf in
    if p_flag then
      printf "%s\n" s;
    s
  in
  assert
    begin
      formatw
         false 10
         (fill_words
            "01234 6789 0 2 4 6 8 01 34 6789 0")
      = "01234 6789\n0 2 4 6 8\n01 34 6789\n0";
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
  let maybe =
    group
      (chain [
           (group (chain
                     [text "class";
                      nest 4 (chain [space; text "Maybe(A)"]);
                      space; text "create"]));
           nest 4
             (chain
                [space;
                 (group
                    (chain
                       [text "nothing"; line "; "; text "just(A)"]))
                ]
             );
           chain [space; text "end"]
         ]
      )
  in
  begin
    assert(
        formatw false 20 maybe
        = "class\n    Maybe(A)\ncreate\n    nothing; just(A)\nend"
      );
    assert(
        formatw false 15 maybe
        = "class\n    Maybe(A)\ncreate\n    nothing\n    just(A)\nend"
      )
  end
