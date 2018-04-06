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

type item =
  | String of string
  | Sub of (int*int*string)
  | Space of int
  | Newline of int

type box =
  | H
  | V of int * int  (* start, offset *)
  | HV of int * int * Pending.t (* start, offset, pending *)
  | HOV of int * int (* start, offset *)
  | HOVP of int * int * int * int * Pending.t (* start, offset, nspaces,
                                                     break offset, pending *)

module Out =
  struct
    type t = {
        current:int;
        out: item list
      }
    let current (o:t): int =
      o.current
    let empty: t =
      {current = 0; out = []}
    let put (s:string) (o:t): t =
      {current = o.current + String.length s;
       out = String s :: o.out}
    let put_sub (start:int) (len:int) (s:string) (o:t): t =
      {current = o.current + len;
       out = Sub (start,len,s) :: o.out}
    let space (n:int) (o:t): t =
      {current = o.current + n; out = Space n :: o.out}
    let newline (n:int) (o:t): t =
      {current = n; out = Newline n :: o.out}
  end

type t = {
    width: int;
    box: box;
    stack: box list;
    out: Out.t
  }

let has_pending (p:t): bool =
  match p.box with
  | HV _ | HOVP _ ->
     true
  | H | V _ | HOV _ ->
     false

let fold (f:'a -> item -> 'a) (a:'a) (p:t): 'a =
  List.fold_left f a (List.rev p.out.Out.out)

let make (width:int): t =
  {width;
   box = H;
   stack = [];
   out = Out.empty}

let push (box:box) (p:t): t =
  {p with box; stack = p.box :: p.stack}

let pop (p:t): t =
  match p.stack with
  | [] ->
     assert false (* illegal call *)
  | box :: stack ->
     {p with box; stack}

let rec action (p:t) (a: Pending.action): t =
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


and put_sub (sstart:int) (len:int) (s:string) (p:t): t =
  match p.box with
  | HV (start,ofs,pend) ->
     let pend = Pending.put sstart len s pend in
     if Out.current p.out + Pending.size pend > p.width then
       Pending.fold
         action
         {p with box = V (start,ofs);
                 out = Out.newline (start+ofs) p.out}
         pend
     else
       {p with box = HV (start, ofs, pend)}
  | HOVP (start,ofs,n,ofsbr,pend) ->
     let pend = Pending.put sstart len s pend in
     if Out.current p.out + Pending.size pend > p.width then
       begin
         Pending.fold
           action
           {p with box = HOV (start,ofs);
                   out = Out.newline (start+ofs+ofsbr) p.out}
           pend
       end
     else
       {p with box = HOVP (start,ofs,n,ofsbr, pend)}
  | _ ->
     {p with out = Out.put_sub sstart len s p.out}


and break (n:int) (ofs:int) (p:t): t =
  match p.box with
  | H ->
     {p with out = Out.space n p.out}
  | V (start,ofsv) ->
     {p with out = Out.newline (start+ofsv+ofs) p.out}
  | HV (start,ofshv,pend) ->
     let pend = Pending.break n ofs pend in
     if Out.current p.out + Pending.size pend > p.width then
       Pending.fold
         action
         {p with box = V (start,ofshv)}
         pend
     else
       {p with box = HV(start,ofshv,pend)}
  | HOV (start,ofshov) ->
     {p with box = HOVP (start,ofshov,n,ofs,Pending.make_hov ofshov)}
  | HOVP (start,ofshov,nbr,ofsbr,pend) ->
     let pend = Pending.break n ofs pend in
     let replay out =
       Pending.fold action {p with out; box = HOV(start,ofshov)} pend
     in
     if Out.current p.out + nbr + Pending.size pend > p.width then
       begin
         replay (Out.newline (start+ofshov+ofsbr) p.out)
       end
     else
       begin
         replay (Out.space nbr p.out)
       end

and hbox (p:t): t =
  match p.box with
  | HV (start,ofs,pend) ->
     {p with box = HV (start, ofs, Pending.hbox pend)}
  | HOVP (start,ofshov,n,ofsbr,pend) ->
     {p with box = HOVP (start, ofshov, n, ofsbr, Pending.hbox pend)}
  | _ ->
     push H p

and vbox (ofs:int) (p:t): t =
  match p.box with
  | HV (start,ofs,pend) ->
     {p with box = HV (start, ofs, Pending.vbox ofs pend)}
  | HOVP (start,ofshov,n,ofsbr,pend) ->
     {p with box = HOVP (start, ofshov, n, ofsbr, Pending.vbox ofs pend)}
  | _ ->
     push (V (Out.current p.out, ofs)) p

and hvbox (ofs:int) (p:t): t =
  match p.box with
  | HV (start,ofs,pend) ->
     {p with box = HV (start, ofs, Pending.hvbox ofs pend)}
  | HOVP (start,ofshov,n,ofsbr,pend) ->
     {p with box = HOVP (start, ofshov, n, ofsbr, Pending.hvbox ofs pend)}
  | _ ->
     push (HV (Out.current p.out, ofs, Pending.make_hv ofs)) p

and hovbox (ofs:int) (p:t): t =
  match p.box with
  | HV (start,ofs,pend) ->
     {p with box = HV (start, ofs, Pending.hovbox ofs pend)}
  | HOVP (start,ofshov,n,ofsbr,pend) ->
     {p with box = HOVP (start, ofshov, n, ofsbr, Pending.hovbox ofs pend)}
  | _ ->
     push (HOV (Out.current p.out, ofs)) p

and close (p:t): t =
  match p.box with
  | HV (start,ofs,pend) ->
     if Pending.is_top pend then
       close
         (if Out.current p.out + Pending.size pend > p.width then
            Pending.fold
              action
              {p with box = V (start,ofs)}
              pend
          else
            Pending.fold
              action
              {p with box = H}
              pend
         )
     else
       {p with box = HV (start, ofs, Pending.close pend)}
  | HOVP (start,ofshov,n,ofsbr,pend) ->
     if Pending.is_top pend then
       close
         (if Out.current p.out + Pending.size pend > p.width then
            Pending.fold
              action
              {p with box = HOV (start,ofshov);
                      out = Out.newline (start+ofshov) p.out}
           pend
          else
            Pending.fold
              action
              {p with box = HOV (start,ofshov);
                      out = Out.space n p.out}
              pend
         )
     else
       {p with box = HOVP (start, ofshov, n, ofsbr, Pending.close pend)}
  | _ ->
     pop p


let put (s:string) (p:t): t =
  put_sub 0 (String.length s) s p


let put_wrapped (l: string list) (p:t): t =
  close
    (let p,_ =
       List.fold_left
         (fun (p,first) str ->
           let word_start i = String_.find (fun c -> c <> ' ') i str in
           let word_end i = String_.find (fun c -> c = ' ') i str in
           let len = String.length str in
           let p =
             if first then
               p
             else
               break 1 0 p
           in
           let rec parse i p =
             if i = len then
               p
             else
               let j = word_end i in
               let p = put_sub i (j-i) str p in
               if j = len then
                 p
               else
                 parse (word_start j) (break 1 0 p)
           in
           parse (word_start 0) p, false)
         (hovbox 0 p,true)
         l
     in
     p)

let test (): unit =
  let str_list =
    ["This    is the first part of a very very long string splitted into";
     "several substrings which might appear on different lines of a";
     "paragraph";
     "which might consist of arbitrary long elements"] in
  let p =
    put_wrapped str_list (make 80)
    (*List.fold_left
      (fun p str ->
        let len = String.length str in
        let non_blank i = String_.find (fun c -> c <> ' ') i str in
        let word i = String_.find (fun c -> c = ' ') i str in
        let rec string_action i p =
          if i = len then
            p
          else
            begin
              let j = word i in
              string_action
                (non_blank j)
                (break 1 0 (put_sub i (j-i) str p))
            end
        in
        string_action (non_blank 0) p
      )
      (hovbox 0 (make 80))
      str_list*)
  in
  fold
    (fun _ a ->
      match a with
      | String s ->
         printf "%s" s
      | Sub (start,len,s) ->
         printf "%s" (String.sub s start len)
      | Space n ->
         printf "%s" (String.make n ' ')
      | Newline n ->
         printf "\n%s" (String.make n ' ')
    )
    ()
    p;
  printf "\n"
