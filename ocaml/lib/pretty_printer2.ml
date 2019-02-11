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


type alternative_text = string
type start = int
type length = int
type indent = int

type command =
  | Text of start * length * string
  | Line of alternative_text * indent



module State =
  struct
    type open_groups = int
    type opened_active = int
    type closed_pending_flag = bool
    type position = int

    type t = {width: int;          (* desired maximal line width *)
              ribbon: int;         (* desired maximal ribbon width *)
              mutable line_indent: indent;
              mutable current_indent: indent;
              mutable p: position;
              mutable pn: position;
              mutable oe: open_groups;  (* effective *)
              mutable op: open_groups;  (* enclosing or before pending line
                                           break *)
              mutable op0: open_groups; (* op at pending line break *)
              mutable opr: open_groups; (* to the right of the group of the
                                           pending line break *)
              (* op + opr is the sum of all open groups in the active region *)
              mutable oar: open_groups; (* to the right of all active groups *)
              mutable buf: command list
             }

    module Group =
      struct
        let count (st:t): int =
          st.oe + st.op + st.opr + st.oar

        let open_normal (st:t): unit =
          assert (st.opr = 0);
          assert (st.oar = 0);
          st.op <- st.op + 1

        let close_normal (st:t): unit =
          assert (st.opr = 0);
          assert (st.oar = 0);
          if st.op > 0 then
            st.op <- st.op - 1
          else
            (assert (st.oe > 0);
             st.oe <- st.oe - 1)

        let active_to_effective (st:t): unit =
          assert (st.opr = 0);
          assert (st.oar = 0);
          assert (st.op0 = 0);
          st.oe <- st.oe + st.op;
          st.op <- 0

        let start_buffering (st:t): unit =
          assert (0 < st.op);
          st.op0 <- st.op

        let is_pending_open (st:t): bool =
          (* Is the group of the pending line break still open? *)
          assert (0 < st.op0);
          let res = st.op0 <= st.op in
          if res then
            (assert (st.opr = 0);
             assert (st.oar = 0);
             assert (st.op > 0)
            );
          res

        let is_pending_closed (st:t): bool =
          (* Is the group of the pending line break already closed? *)
          assert (0 < st.op0);
          st.op < st.op0

        let is_active_open (st:t): bool =
          (* Is there still a group enclosing the pending line break open? *)
          let res = st.op > 0 in
          if res then
            assert (st.oar = 0);
          res

        let is_active_closed (st:t): bool =
          (* Are all groups enclosing the pending line break closed? *)
          st.op = 0

        let flush_flatten (st:t): unit =
          assert (is_pending_closed st);
          if is_active_closed st then
            (st.op <- st.oar;
             st.oar <- 0);
          st.op0 <- 0

        let flush_effective (st:t): unit =
          (* All open groups enclosing the pending line break (the active
             groups) become effective, all groups to the right of the pending
             group become the new active groups. *)
          st.oe <- st.oe + st.op;
          st.op <- st.opr + st.oar;
          st.opr <- 0;
          st.oar <- 0;
          st.op0 <- 0

        let open_buffering (st:t): unit =
          if is_pending_open st then
             st.op <- st.op + 1
          else if is_active_open st then
             st.opr <- st.opr + 1
          else
            (assert (st.op = 0);
             assert (st.opr = 0);
             st.oar <- st.oar + 1)

        let close_buffering (st:t): unit =
          if is_pending_open st then
             st.op <- st.op - 1
          else if is_active_open st then
             if st.opr > 0 then
               st.opr <- st.opr - 1
             else
               st.op <- st.op - 1
          else
            (assert (st.op = 0);
             assert (st.opr = 0);
             assert (st.oar > 0);
             st.oar <- st.oar - 1)
      end (* Group *)

    let start (indent:int) (width:int) (ribbon:int): t =
      assert (0 <= indent);
      assert (0 <= width);
      assert (0 <= ribbon);
      {width; ribbon;
       current_indent = indent;   line_indent = indent;
       p = 0;  pn = 0;
       oe = 0; op = 0; op0 = 0; opr = 0; oar = 0;
       buf = []
      }

    let normal (st:t): bool =
      st.buf = []

    let buffering (st:t): bool =
      st.buf <> []


    let fits (len:int) (st:t): bool =
      let newpos = st.p + len
      in
      newpos <= st.width
      && newpos - st.line_indent <= st.ribbon

    let out_text(len:length) (st:t): unit =
      assert (normal st);
      st.p <- st.p + len

    let out_line (st:t): unit =
      assert (normal st);
      assert (st.op = 0);  (* Otherwise we must start buffering. *)
      assert (st.opr = 0); (* There is no active group. *)
      assert (st.oar = 0); (* ... therefore nothing to the right of it. *)
      st.p <- st.current_indent;
      st.line_indent <- st.current_indent

    let active_to_effective (st:t): unit =
      assert (normal st);
      Group.active_to_effective st


    let start_buffering (s:alternative_text) (st:t): unit =
      assert (normal st);
      let len = String.length s in
      assert (fits len st);
      st.buf <- Line (s, st.current_indent) :: st.buf;
      Group.start_buffering st;
      st.p <- st.p + len;
      st.pn <- st.current_indent


    let flush (flatten:bool) (st:t): command list =
      assert (buffering st);
      if flatten then
        Group.flush_flatten st
      else
        (Group.flush_effective st;
         st.p   <- st.pn);
      let buf = List.rev st.buf in
      st.buf <- [];
      buf


    let buffer_text (start:start) (len:length) (s:string) (st:t): unit =
      assert (buffering st);
      assert (fits len st);
      st.buf <- Text (start,len,s) :: st.buf;
      st.p <- st.p + len;
      st.pn <- st.pn + len


    let buffer_line (s:alternative_text) (st:t): unit =
      assert (buffering st);
      let len = String.length s in
      assert (fits len st);
      assert (Group.is_pending_open st);
      st.buf <- Line (s,st.current_indent) :: st.buf;
      st.p   <- st.p + len;
      st.pn  <- st.current_indent


    let increment_indent (i:indent) (st:t): unit =
      st.current_indent <- st.current_indent + i


    let decrement_indent (i:indent) (st:t): unit =
      assert (i <= st.current_indent);
      st.current_indent <- st.current_indent - i


    let open_group (st:t): unit =
      if normal st then
        Group.open_normal st
      else
        Group.open_buffering st


    let close_group (st:t): unit =
      if normal st then
        Group.close_normal st
      else
        Group.close_buffering st
  end (* State *)





module Make  (P:PRINTER) =
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

    let out_command (flatten:bool) (c:command): unit P.t =
      match c with
      | Text (start,len,s) ->
         P.put_substring start len s
      | Line (s, i) ->
         if flatten then
           P.put_string s
         else
           P.(putc '\n' >>= fun _ -> fill ' ' i)

    let out_text (start:start) (len:length) (s:string) (st:state): unit P.t =
      State.out_text len st;
      P.put_substring start len s


    let flush (flatten:bool) (st:state): unit P.t =
      let buf = State.flush flatten st in
      let rec write buf =
        match buf with
        | [] ->
           assert false (* buffer cannot be empty *)
        | [c] ->
           out_command flatten c
        | c :: buf ->
           P.(out_command flatten c >>= fun _ ->
              write buf)
      in
      write buf

    let text_sub (start:int) (len:int) (s:string) (st:state): unit P.t =
      assert (0 <= start);
      assert (start+len <= String.length s);
      if State.normal st then
        out_text start len s st
      else if State.fits len st then
        (State.buffer_text start len s st;
         print_nothing)
      else
        (flush false >>= fun _ -> out_text start len s) st


    let text (s:string): unit t =
      text_sub 0 (String.length s) s

    let line_normal (s:alternative_text) (st:state): unit P.t =
      assert (State.normal st);
      let len = String.length s
      in
      if State.Group.is_active_open st && State.fits len st then
          (State.start_buffering s st;
           print_nothing)
      else
        (if State.Group.is_active_open st then
           State.active_to_effective st;
         State.out_line st;
         P.(putc '\n' >>= fun _ ->
            fill ' ' st.State.line_indent))


    let line_buffering (s:alternative_text) (st:state): unit P.t =
      assert (State.buffering st);
      if State.Group.is_pending_open st then
        if State.fits (String.length s) st then
          (State.buffer_line s st;
           print_nothing)
        else
          (flush false >>= fun _ -> line_normal s) st
      else
        (flush true >>= fun _ -> line_normal s) st


    let line (s:string) (st:state): unit P.t =
      if State.normal st then
        line_normal s st
      else
        line_buffering s st



    let cut: unit t =
      line ""

    let space: unit t =
      line " "

    let nest (i:int) (m:'a t): unit t =
      let start st =
        State.increment_indent i st;
        print_nothing
      and close st =
        State.decrement_indent i st;
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

    let fill_of_string (s:string) (st:state): unit P.t =
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


    let fill_of_stringlist (l:string list) (st:state): unit P.t =
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

  begin
    let str = "01234 6789 0 2 4 6 8 01 34 6789 0"
    and strlst = ["01234"; "6789 0 2"; "4 6 8 01 34"; "6789 0"]
    and res = "01234 6789\n0 2 4 6 8\n01 34 6789\n0"
    in
    assert (formatw false 10 (fill_of_string str) = res);
    assert (formatw false 10 (fill_of_stringlist strlst) = res);
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
    assert(
        formatw false 20 maybe
        = "class\n    Maybe(A)\ncreate\n    nothing; just(A)\nend"
      );
    assert(
        formatw false 15 maybe
        = "class\n    Maybe(A)\ncreate\n    nothing\n    just(A)\nend"
      )
  end
