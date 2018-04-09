open Common
open Printf

module Pending =
  struct
    type box = H of int | V of int*int | HV of int*int | HOV of int*int

    type action =
      | String of int * int * string
      | Break of int * int
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

    let break (n:int) (ofs:int) (p:t): t =
      let standard () =
        let size = n + p.size in
        let max_size = max size p.max_size in
        {p with size;
                max_size;
                buffer = Break (n,ofs) :: p.buffer}
      in
      match p.box with
      | H _ ->
         standard ()
      | V (start,ofsv) ->
         let size = start + ofsv + ofs in
         {p with size;
                 max_size = max size p.max_size;
                 buffer = Break(n,ofs) :: p.buffer}
      | HV _ ->
         standard ()
      | HOV _ ->
         standard ()

    let hbox (p:t): t =
      {p with stack = p.box :: p.stack;
              box = H p.max_size}

    let vbox (ofs:int) (p:t): t =
      {p with stack = p.box :: p.stack;
              box = V (p.max_size,ofs)}

    let hvbox (ofs:int) (p:t): t =
      {p with stack = p.box :: p.stack;
              box = HV (p.max_size,ofs)}

    let hovbox (ofs:int) (p:t): t =
      {p with stack = p.box :: p.stack;
              box = HOV (p.max_size,ofs)}

    let close (p:t): t =
      match p.stack with
      | [] ->
         assert false
      | box :: tl ->
         {p with box = box; stack = tl}
  end (* Pending *)



module type PRINTER =
  sig
    include Monad.MONAD
    type channel
    val put: int -> int -> string -> channel -> unit t
    val space: int -> channel -> unit t
    val newline: int -> channel -> unit t
  end


module type PRETTY =
  sig
    module P: PRINTER
    type t
    val make:   int -> P.channel -> t P.t
    val hbox:   t -> t P.t
    val vbox:   int -> t -> t P.t
    val hvbox:  int -> t -> t P.t
    val hovbox: int -> t -> t P.t
    val close:  t -> t P.t
    val put:    string -> t -> t P.t
    val put_sub: int -> int -> string -> t -> t P.t
    val put_wrapped: string list -> t -> t P.t
    val cut:    t -> t P.t
    val space:  t -> t P.t
    val break:  int -> int -> t -> t P.t
    val (>>):   'a P.t -> 'b P.t -> 'b P.t
    val (>>=):  'a P.t -> ('a -> 'b P.t) -> 'b P.t
  end


module Make (P:PRINTER): PRETTY with module P = P =
  struct
    module P = P
    type box =
      | H
      | V of int * int  (* start, offset *)
      | HV of int * int * Pending.t (* start, offset, pending *)
      | HOV of int * int (* start, offset *)
      | HOVP of int * int * int * int * Pending.t (* start, offset, nspaces,
                                                     break offset, pending *)
    type t = {
        current: int;
        channel: P.channel;
        width: int;
        box: box;
        stack: box list
      }

    let make (width:int) (channel:P.channel): t P.t =
      P.make {current = 0; width; channel; box = H; stack = []}

    let push (box:box) (p:t): t P.t =
      P.make {p with box; stack = p.box :: p.stack}

    let pop (p:t): t P.t=
      match p.stack with
      | [] ->
         assert false (* illegal call *)
      | box :: stack ->
         P.make {p with box; stack}

    let pending_exceeds (pend:Pending.t) (p:t): bool =
      p.current + Pending.size pend > p.width

    let puts (start:int) (len:int) (s:string) (p:t): t P.t =
      P.(put start len s p.channel
         >> make {p with current = len + p.current})

    let newline (indent:int) (p:t) (box:box): t P.t =
      P.(newline indent p.channel >> P.make {p with box; current = indent})

    let space (n:int) (p:t) (box:box): t P.t =
      P.(space n p.channel >> P.make {p with box; current = n + p.current})

    let (>>) = P.(>>)
    let (>>=) = P.(>>=)

    let rec replay_pending (pend:Pending.t) (p:t): t P.t =
      actions (Pending.actions pend) p

    and actions (l:Pending.action list) (p:t): t P.t =
      match l with
      | [] ->
         P.make p
      | a :: tl ->
         P.(action a p >>= actions tl)

    and action (a:Pending.action) (p:t): t P.t =
      match a with
      | Pending.String (start,len,s) ->
         put_sub start len s p
      | Pending.Break (n,ofs) ->
         break n ofs p
      | Pending.Open b ->
         begin
           match b with
           | Pending.H start ->
              hbox p
           | Pending.V (start,ofs) ->
              vbox ofs p
           | Pending.HV (start,ofs) ->
              hvbox ofs p
           | Pending.HOV (start,ofs) ->
              hovbox ofs p
         end
      | Pending.Close ->
         close p

    and newline_pending (indent:int) (pend:Pending.t) (box:box) (p:t)
        : t P.t =
      if pending_exceeds pend p then
        newline indent p p.box >>= replay_pending pend
      else
        P.make {p with box}

    and put_sub (sstart:int) (len:int) (s:string) (p:t): t P.t =
      assert (0 <= sstart);
      assert (sstart + len <= String.length s);
      match p.box with
      | HV (start,ofs,pend) ->
         let pend = Pending.put sstart len s pend in
         if pending_exceeds pend p then
           replay_pending pend {p with box = V (start,ofs)}
         else
           P.make {p with box = HV (start,ofs,pend)}
      | HOVP (start,ofs,n,ofsbr,pend) ->
         let pend = Pending.put sstart len s pend in
         if pending_exceeds pend p then
           newline (start+ofs) p (HOV (start,ofs))
           >>= replay_pending pend
         else
           P.make {p with box = HOVP (start,ofs,n,ofsbr,pend)}
      | _ ->
         puts sstart len s p

    and break (n:int) (ofs:int) (p:t): t P.t =
      match p.box with
      | H ->
         space n p p.box
      | V (start,ofsv) ->
         let indent = start + ofsv + ofs in
         newline indent p p.box
      | HV (start,ofshv,pend) ->
         let pend = Pending.break n ofs pend in
         if pending_exceeds pend p then
           replay_pending pend {p with box = V (start,ofshv)}
         else
           P.make {p with box = HV(start,ofshv,pend)}
      | HOV (start,ofshov) ->
         P.make
           {p with box = HOVP (start,ofshov,n,ofs,Pending.make_hov ofshov)}
      | HOVP (start,ofshov,nbr,ofsbr,pend) ->
         let pend = Pending.break n ofs pend in
         let box = HOV (start,ofshov) in
         if pending_exceeds pend p then
           let indent = start + ofshov + ofsbr in
           newline indent p box >>= replay_pending pend
         else
           space nbr p box >>= replay_pending pend

    and hbox (p:t): t P.t =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs, Pending.hbox pend)}
      | HOVP (start,ofshov,n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, n, ofsbr, Pending.hbox pend)}
      | _ ->
         push H p

    and vbox (ofs:int) (p:t): t P.t =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs,
                             Pending.vbox ofs pend)}
      | HOVP (start,ofshov,n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, n, ofsbr,
                               Pending.vbox ofs pend)}
      | _ ->
         push (V (p.current, ofs)) p

    and hvbox (ofs:int) (p:t): t P.t =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs, Pending.hvbox ofs pend)}
      | HOVP (start,ofshov,n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, n, ofsbr,
                               Pending.hvbox ofs pend)}
      | _ ->
         push (HV (p.current, ofs, Pending.make_hv ofs)) p

    and hovbox (ofs:int) (p:t): t P.t =
      match p.box with
      | HV (start,ofs,pend) ->
         P.make
           {p with box = HV (start, ofs, Pending.hovbox ofs pend)}
      | HOVP (start,ofshov,n,ofsbr,pend) ->
         P.make
           {p with box = HOVP (start, ofshov, n, ofsbr,
                               Pending.hovbox ofs pend)}
      | _ ->
           push (HOV (p.current, ofs)) p

    and close (p:t): t P.t =
      match p.box with
      | HV (start,ofs,pend) ->
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
      | HOVP (start,ofshov,n,ofsbr,pend) ->
         if Pending.is_top pend then
           let box = HOV (start,ofshov) in
           (if pending_exceeds pend p then
              newline (start+ofshov) p box
            else
              space n p box)
             >>= replay_pending pend
             >>= close
         else
           P.make
             {p with box = HOVP (start, ofshov, n, ofsbr,
                                 Pending.close pend)}
      | _ ->
         pop p

    let put (s:string) (p:t): t P.t =
      put_sub 0 (String.length s) s p

    let cut (p:t): t P.t =
      break 0 0 p

    let space (p:t): t P.t =
      break 1 0 p

    let put_wrapped (l:string list) (p:t): t P.t =
      let rec wrap first l p =
        match l with
        | [] ->
           P.make p
        | str :: tl ->
           let word_start i = String_.find (fun c -> c <> ' ') i str in
           let word_end i = String_.find (fun c -> c = ' ') i str in
           let len = String.length str in
           let rec parse (first:bool) (i:int) (p:t): t P.t =
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
  end






module String_printer:
sig
  include PRINTER with type channel = unit
  val run: int -> 'a t -> string
end =
  struct
    include Monad.String_buffer
    type channel = unit
    let put (start:int) (len:int) (s:string) (): unit t =
      put_substring start len s
    let space (n:int) (): unit t =
      put_blanks n
    let newline (indent:int) (): unit t =
      putc '\n' >> space indent ()
  end




module Outfile_of_io (IO:Ocaml_io.IO_TYPE) =
  struct
    include IO
    type channel = file_descr
    let put_f (n:int) (f:int -> char) (fd:channel): unit t =
      let rec g i (): unit t =
        if i = n then
          make ()
        else
          putc fd (f i) >>= g (i+1)
      in
      g 0 ()

    let put (start:int) (len:int) (s:string) (fd:channel): unit t =
      put_f len (fun i -> s.[start+i]) fd

    let space (n:int) (fd:channel): unit t =
      put_f n (fun _ -> ' ') fd

    let newline (n:int) (fd:channel): unit t =
      putc fd '\n' >> space n fd
  end



let test (): unit =
  let module PP = Make (String_printer) in
  let open PP in
  let str_list =
    ["This    is the first part of a very very long string splitted into";
     "several substrings which might appear on different lines of a";
     "paragraph";
     "which might    consist of arbitrary long elements."] in
  let buf = String_printer.run 200 in
  assert
    begin
      (make 5 () >>= vbox 0 >>= put_wrapped ["123";"456"] >>= close)
      |> buf
      = "123\n456"
    end;
  assert
    begin
      (make 5 () >>= vbox 1 >>= put_wrapped ["123";"456"] >>= close)
      |> buf
      = "123\n 456"
    end;
  assert
    begin
      (make 7 () >>= hvbox 0 >>= put_wrapped ["123";"456"] >>= close)
      |> buf
      = "123 456"
    end;
  assert
    begin
      (make 6 () >>= hvbox 0 >>= put_wrapped ["123";"456"] >>= close)
      |> buf
      = "123\n456"
    end;
  assert
    begin
      (make 6 () >>= hvbox 2 >>= put_wrapped ["123";"456"] >>= close)
      |> buf
      = "123\n  456"
    end;
  assert
    begin
      (make 5 () >>= put "bla"
       >>= hvbox 0 >>= put_wrapped ["123";"456"] >>= close)
      |> buf
      = "bla123\n   456"
    end;
  let pp =
    make 30 () >>= put "Start: "
    >>= hovbox 5
    >>= put_wrapped str_list
    >>= close
  and buf = String_printer.run 200
  in
  printf "test3\n%s\n" (buf pp)
