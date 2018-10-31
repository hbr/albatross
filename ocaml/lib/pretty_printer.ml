open Common
open Printf

module Pending =
  struct
    type box = H of int | V of int*int | HV of int*int | HOV of int*int

    type action =
      | String of int * int * string
      | Break of string * int * int
      | Open of box
      | Close

    type t = {
        size: int;
        max_size: int;
        box: box;
        stack: box list;
        buffer: action list;
      }

    let make_box (box:box): t =
      {size = 0; max_size = 0; box; stack = []; buffer = []}

    let make_hv (ofs:int): t =
      make_box (HV (0,ofs))

    let make_hov (ofs:int): t =
      make_box (HOV (0,ofs))

    let is_top (p:t): bool =
      p.stack = []

    let stack_size (p:t): int =
      List.length p.stack

    let size (p:t): int =
      p.max_size

    let fold (f:'a -> action -> 'a) (a:'a) (p:t): 'a =
      List.fold_left f a (List.rev p.buffer)

    let actions (p:t): action list =
      List.rev p.buffer

    let put (start:int) (len:int) (s:string) (p:t): t =
      assert (0 <= start);
      assert (start + len <= String.length s);
      let size = p.size + len in
      let max_size = max size p.max_size in
      {p with size;
              max_size;
              buffer = String (start,len,s) :: p.buffer}

    let break (sep:string) (n:int) (ofs:int) (p:t): t =
      let standard () =
        let size = String.length sep + n + p.size in
        let max_size = max size p.max_size in
        {p with size;
                max_size;
                buffer = Break (sep,n,ofs) :: p.buffer}
      in
      match p.box with
      | H _ ->
         standard ()
      | V (start,ofsv) ->
         let size = start + ofsv + ofs in
         {p with size;
                 max_size = max size p.max_size;
                 buffer = Break(sep,n,ofs) :: p.buffer}
      | HV _ ->
         standard ()
      | HOV _ ->
         standard ()

    let hbox (p:t): t =
      let box = H p.max_size in
      {p with stack = p.box :: p.stack;
              box;
              buffer = Open box :: p.buffer}

    let vbox (ofs:int) (p:t): t =
      let box = V (p.max_size,ofs) in
      {p with stack = p.box :: p.stack;
              box;
              buffer = Open box :: p.buffer}

    let hvbox (ofs:int) (p:t): t =
      let box = HV (p.max_size,ofs) in
      {p with stack = p.box :: p.stack;
              box;
              buffer = Open box :: p.buffer}

    let hovbox (ofs:int) (p:t): t =
      let box = HOV (p.max_size,ofs) in
      {p with stack = p.box :: p.stack;
              box;
              buffer = Open box :: p.buffer}

    let close (p:t): t =
      match p.stack with
      | [] ->
         assert false
      | box :: tl ->
         {p with box; stack = tl}
  end (* Pending *)



module type PRINTER =
  sig
    include Monad.MONAD
    type out_file
    val putc: out_file -> char -> unit t
    val put_substring: out_file -> int -> int -> string -> unit t
    val fill: out_file  -> char -> int -> unit t
  end


module String_printer:
sig
  include PRINTER with type out_file = unit
  val run: int -> 'a t -> string
end =
  struct
    include Monad.String_buffer
    type out_file = unit
    let put_substring (fd:out_file) = put_substring
    let fill (fd:out_file) = fill
    let putc (fd:out_file) = putc
  end




module type PRETTY =
  sig
    type t
    type _ out
    type pp = t -> t out
    type out_file
    val make:   int -> out_file -> t out
    val hbox:   pp -> pp
    val vbox:   int -> pp -> pp
    val hvbox:  int -> pp -> pp
    val hovbox: int -> pp -> pp
    val fill:   char -> int -> pp
    val put:    string -> pp
    val put_left:  int -> string -> pp
    val put_right: int -> string -> pp
    val put_sub: int -> int -> string -> pp
    val put_wrapped: string list -> pp
    val cut:    pp
    val space:  pp
    val break:  string -> int -> int -> pp
    val chain:  pp list -> pp
    val (>>=):  'a out -> ('a -> 'b out) -> 'b out
    val stop:   t -> unit out
  end



module Make (P:PRINTER) =
  struct
    type 'a out = 'a P.t

    type out_file = P.out_file

    type box =
      | H (** Horizontal box. All break hints are printed as spaces and no
             line break occurs. This box needs no start position and offset
             because it does not break lines. *)
      | V of int * int  (** start position of the box, offset for a
                           newline. All material is printed immediately. A
                           break hint generates a newline with indentation
                           'start + offset + offset(break)' *)
      | HV of
          int * int
          * Pending.t (** start, offset, pending. All material is put into
                         pending. If the pending material gets too big to fit
                         on a line the hvbox is converted to a vbox and the
                         pending material is replayed on the vbox. If the box
                         is closed and the pending material fits on a line
                         then all material is printed as if it were a hbox. *)
      | HOV of
          int * int (** start, offset.  All material is printed immediately
                       until a break hint occurs. If the printed material with
                       the space exceeds the line, the line is broken and
                       continues as a hovbox initially. If the material still
                       fits on the line after the first break hint, the box is
                       converted into a HOVP box and more material is added as
                       pending material. *)
      | HOVP of
          int * int * string * int * int
          * Pending.t (** start, offset, separator, nspaces, break offset,
                         pending. State of a hovbox after receiving a break
                         hint within the line bounds. Additional material
                         without break or with a break hint with stacked
                         material pending exceeding the line width generates a
                         newline and a replay of the pending material in an
                         initial hovbox. An additional break hint at the top
                         level cause printing either on the same line of after
                         a line break depending on the size of the pending
                         material. *)
    type t = {
        current: int;
        channel: out_file;
        width: int;
        box: box;
        stack: box list
      }

    type pp = t -> t out

    let string_of_box (b:box): string =
      match b with
      | H ->
         "H"
      | V _ ->
         "V"
      | HV _ ->
         "HV"
      | HOV _ ->
         "HOV"
      | HOVP _ ->
         "HOVP"


    let make (width:int) (channel:out_file): t out =
      P.make {current = 0; width; channel; box = H; stack = []}

    let push (box:box) (p:t): t out =
      P.make {p with box; stack = p.box :: p.stack}

    let pop (p:t): t out=
      match p.stack with
      | [] ->
         assert false (* illegal call *)
      | box :: stack ->
         P.make {p with box; stack}


    let pending_exceeds (add:int) (pend:Pending.t) (p:t): bool =
      p.current + add +  Pending.size pend > p.width

    let puts (start:int) (len:int) (s:string) (p:t): t out =
      P.(put_substring p.channel start len s >>= fun _ ->
         make {p with current = len + p.current})

    let newline (indent:int) (p:t) (box:box): t out =
      P.(putc p.channel '\n' >>= fun _ ->
         fill p.channel ' ' indent >>= fun _ ->
         P.make {p with box; current = indent})

    let space_size (sep:string) (n:int): int =
      String.length sep + n

    let space (sep:string) (n:int) (p:t) (box:box): t out =
      let len = String.length sep in
      P.(put_substring p.channel 0 len sep >>= fun _ ->
         fill p.channel ' ' n  >>= fun _ ->
         P.make {p with box; current = len + n + p.current})

    let (>>=) = P.(>>=)

    let has_pending (p:t): bool =
      match p.box with
      | HV _ | HOVP _ ->
         true
      | _ ->
         false

    let is_top (p:t): bool =
      p.stack = []


    let rec replay_pending (pend:Pending.t): t -> t out =
      actions (Pending.actions pend)

    and actions (l:Pending.action list) (p:t): t out =
      match l with
      | [] ->
         P.make p
      | a :: tl ->
         P.(action a p >>= actions tl)

    and action (a:Pending.action) (p:t): t out =
      match a with
      | Pending.String (start,len,s) ->
         put_sub start len s p
      | Pending.Break (sep,n,ofs) ->
         break sep n ofs p
      | Pending.Open b ->
         begin
           match b with
           | Pending.H start ->
              hbox0 p
           | Pending.V (start,ofs) ->
              vbox0 ofs p
           | Pending.HV (start,ofs) ->
              hvbox0 ofs p
           | Pending.HOV (start,ofs) ->
              hovbox0 ofs p
         end
      | Pending.Close ->
         close p

    and put_sub (sstart:int) (len:int) (s:string) (p:t): t out =
      assert (0 <= sstart);
      assert (sstart + len <= String.length s);
      match p.box with
      | HV (start,ofs,pend) ->
         let pend = Pending.put sstart len s pend in
         if pending_exceeds 0 pend p then
           replay_pending pend {p with box = V (start,ofs)}
         else
           P.make {p with box = HV (start,ofs,pend)}
      | HOVP (start,ofs,sep,n,ofsbr,pend) ->
         let pend = Pending.put sstart len s pend in
         if pending_exceeds (space_size sep n) pend p then
           newline (start+ofs+ofsbr) p (HOV (start,ofs))
           >>= replay_pending pend
         else
           P.make {p with box = HOVP (start,ofs,sep,n,ofsbr,pend)}
      | _ ->
         puts sstart len s p

    and break (sep:string) (n:int) (ofs:int) (p:t): t out =
      match p.box with
      | H ->
         space sep n p p.box
      | V (start,ofsv) ->
         let indent = start + ofsv + ofs in
         newline indent p p.box
      | HV (start,ofshv,pend) ->
         let pend = Pending.break sep n ofs pend in
         if pending_exceeds 0 pend p then
           replay_pending pend {p with box = V (start,ofshv)}
         else
           P.make {p with box = HV(start,ofshv,pend)}
      | HOV (start,ofshov) ->
         let sp_size = space_size sep n in
         if p.width <= p.current + sp_size then
           newline (start+ofshov) p p.box
         else
           P.make
             {p with
               box = HOVP (start,ofshov,sep,n,ofs,Pending.make_hov ofshov)}
      | HOVP (start,ofshov,sephov,nbr,ofsbr,pend) ->
         let pend1 = Pending.break sep n ofs pend in
         let box = HOV (start,ofshov) in
         if pending_exceeds (space_size sephov nbr) pend p then
           let indent = start + ofshov + ofsbr in
           newline indent p box >>= replay_pending pend1
         else if Pending.is_top pend then
           space sephov nbr p box >>= replay_pending pend1
         else
           P.make {p with box = HOVP (start,ofshov,sephov,nbr,ofsbr,pend1)}

    and hbox0 (p:t): t out =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs, Pending.hbox pend)}
      | HOVP (start,ofshov,sep,n,ofsbr,pend) ->
         P.make
           {p with
             box = HOVP (start, ofshov, sep, n, ofsbr, Pending.hbox pend)}
      | _ ->
         push H p

    and vbox0 (ofs:int) (p:t): t out =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs,
                             Pending.vbox ofs pend)}
      | HOVP (start,ofshov,sep,n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, sep, n, ofsbr,
                               Pending.vbox ofs pend)}
      | _ ->
         push (V (p.current, ofs)) p

    and hvbox0 (ofs:int) (p:t): t out =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs, Pending.hvbox ofs pend)}
      | HOVP (start,ofshov,sep, n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, sep, n, ofsbr,
                               Pending.hvbox ofs pend)}
      | _ ->
         push (HV (p.current, ofs, Pending.make_hv ofs)) p

    and hovbox0 (ofs:int) (p:t): t out =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs, Pending.hovbox ofs pend)}
      | HOVP (start,ofshov,sep,n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, sep, n, ofsbr,
                               Pending.hovbox ofs pend)}
      | _ ->
           push (HOV (p.current, ofs)) p

    and close (p:t): t out =
      match p.box with
      | HV (start,ofs,pend) ->
         (*printf "close HV box %s is_top %b stack %d\n"
           (string_of_box p.box) (Pending.is_top pend)
           (Pending.stack_size pend);*)
         if Pending.is_top pend then
           P.(actions
                (Pending.actions pend)
                {p with
                  box =
                    if p.current + Pending.size pend > p.width then
                      V (start,ofs)
                    else
                      H}
           >>= close)
         else
           P.make {p with box = HV (start, ofs, Pending.close pend)}
      | HOVP (start,ofshov,sep,n,ofsbr,pend) ->
         if Pending.is_top pend then
           let box = HOV (start,ofshov) in
           (if pending_exceeds (space_size sep n) pend p then
              newline (start+ofshov+ofsbr) p box
            else
              space sep n p box)
           >>= replay_pending pend
           >>= close
         else
           P.make
             {p with box = HOVP (start, ofshov, sep, n, ofsbr,
                                 Pending.close pend)}
      | _ ->
         (*printf "close general\n";*)
         pop p

    let hbox (f:t->t out) (p:t): t out =
      hbox0 p >>= f >>= close

    let vbox (ofs:int) (f:t->t out) (p:t): t out =
      vbox0 ofs p >>= f >>= close

    let hvbox (ofs:int) (f:t->t out) (p:t): t out =
      (*printf "hvbox\n";*)
      hvbox0 ofs p >>= f >>= fun p ->
      (*printf "close hvbox\n";*)
      close p

    let hovbox (ofs:int) (f:t->t out) (p:t): t out =
      hovbox0 ofs p >>= f >>= close

    let put (s:string) (p:t): t out =
      put_sub 0 (String.length s) s p

    let fill (c:char) (n:int) (p:t): t out =
      put (String.make n c) p

    let put_left (width:int) (s:string) (p:t): t out =
      let len = String.length s in
      if len < width then
        put s p >>= fill ' ' (width - len)
      else
        put s p

    let put_right (width:int) (s:string) (p:t): t out =
      let len = String.length s in
      if len < width then
        fill ' ' (width - len) p >>= put s
      else
        put s p

    let cut (p:t): t out =
      break "" 0 0 p

    let space (p:t): t out =
      break "" 1 0 p

    let put_wrapped (l:string list) (p:t): t out =
      let rec wrap first l p =
        match l with
        | [] ->
           P.make p
        | str :: tl ->
           let word_start i = String_.find (fun c -> c <> ' ') i str in
           let word_end i = String_.find (fun c -> c = ' ') i str in
           let len = String.length str in
           let rec parse (first:bool) (i:int) (p:t): t out =
             if i = len then
               P.make p
             else
               begin
                 assert (i < len); (* There is a word! *)
                 let j = word_end i in
                 let put = put_sub i (j-i) str in
                 (if first then
                    put p
                  else
                    space p >>= put)
                 >>= parse false (word_start j)
               end
           in
           let prse = parse true (word_start 0) in
           (if first then
              prse p
            else
              space p >>= prse)
           >>= wrap false tl
      in
      wrap true l p

    let chain (lst:pp list): pp =
      assert (lst <> []);
      let rec chn (p:t out) (lst:pp list): t out =
        match lst with
        | [] ->
           p
        | a :: tl ->
           chn (p >>= a) tl
      in
      match lst with
      | [] ->
         assert false (* illegal call *)
      | [a] ->
         a
      | a :: tl ->
         fun p -> chn (a p) tl



    let stop (p:t): unit out =
      assert (is_top p);
      P.make ()
  end









let test (): unit =
  Printf.printf "test pretty printer\n";
  let module PP = Make (String_printer) in
  let open PP in
  let buf = String_printer.run 200 in
  (*assert
    begin
      let str =
      (make 100 ()
       >>= hvbox 0
             (chain [put "(a:Natural) :="; break "" 1 2;
                     hvbox 0
                       (chain [put "inspect"; break "" 1 2;
                               (hvbox 0
                                  (chain [put "exp"; break ";" 1 0; put "res"]));
                               space; put "case"; space; put "end"])
             ]))
      |> buf
      in
      printf "%s\n" str;
      str = ""
    end;*)
  assert
    begin
      (make 12 () >>=
         hovbox 0
           (chain [put "inspect"; break "" 1 2;
                   (hvbox 0
                      (chain [put "exp"; break ";" 1 0; put "res"]));
                   space; put "case"; space; put "end"]
           ))
      |> buf
      = "inspect\n  exp; res\ncase end"
    end;
  assert
    begin
      (make 5 () >>= vbox 0 (put_wrapped ["123";"456"]))
      |> buf
      = "123\n456"
    end;
  assert
    begin
      (make 5 () >>= vbox 1 (put_wrapped ["123";"456"]))
      |> buf
      = "123\n 456"
    end;
  assert
    begin
      (make 7 () >>= hvbox 0 (put_wrapped ["123";"456"]))
      |> buf
      = "123 456"
    end;
  assert
    begin
      (make 6 () >>= hvbox 0 (put_wrapped ["123";"456"]))
      |> buf
      = "123\n456"
    end;
  assert
    begin
      (make 6 () >>= hvbox 2 (put_wrapped ["123";"456"]))
      |> buf
      = "123\n  456"
    end;
  assert
    begin
        (make 5 () >>= put "bla"
         >>= hvbox 0 (put_wrapped ["123";"456"]))
        |> buf
        = "bla123\n   456"
    end;
  assert
    begin
      (make 20 ()
       >>= vbox 0
             (chain [put "line1"; cut; put "line2"; cut;
                     vbox 2
                       (chain [put "line3"; cut; put "line4"])]))
      |> buf
      = "line1\nline2\nline3\n  line4"
    end;
  assert
    begin
      (make 10 ()
       >>= hovbox 0
             (chain [put "1234567"; space; put "90"; space;
                     put "12345"; space; put "1234567890"]))
      |> buf
      = "1234567 90\n12345\n1234567890"
    end;
  assert
    begin
      (make 3 ()
       >>= hvbox 0
             (chain [put "a"; break ";" 0 0; put "b"]))
      |> buf
      = "a;b"
    end;
  assert
    begin
      (make 2 ()
       >>= hvbox 0
             (chain [put "a"; break ";" 0 0; put "b"]))
      |> buf
      = "a\nb"
    end;
  assert
    begin
      (make 10 ()
       >>= hovbox 0
             (chain [put "1234567"; space; put "90"; space;
                     put "12345"; space; put "1234567890"]))
      |> buf
      = "1234567 90\n12345\n1234567890"
    end;
  assert
    begin
      (make 3 ()
       >>= hovbox 0
             (chain [put "a"; break ";" 0 0; put "b"]))
      |> buf
      = "a;b"
    end;
  assert
    begin
      (make 2 ()
       >>= hovbox 0
             (chain [put "a"; break ";" 0 0; put "b"]))
      |> buf
      = "a\nb"
    end


(*
let _ =
  let open Ocaml_io in
  let module PP = Make (IO) in
  let open PP in
  let str_list =
    ["This    is the first part of a very very long string splitted into";
     "several substrings which might appear on different lines of a";
     "paragraph";
     "which might    consist of arbitrary long elements."] in
  let pp = make 30 IO.stdout
           >>= hovbox 0
           >>= put_wrapped str_list
           >>= close >>= stop
  in
  IO.execute pp
 *)
