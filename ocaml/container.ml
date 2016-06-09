(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

module Option: sig
  val has:   'a option -> bool
  val value: 'a option -> 'a
end = struct
  let has (o: 'a option): bool =
    match o with None -> false | Some _ -> true
  let value (o: 'a option): 'a =
    match o with
      None -> assert false (* illegal call *)
    | Some x -> x
end


type ('a, 'b) either =
    Left of 'a
  | Right of 'b


module Search: sig
  val binsearch_max: 'a -> 'a array -> int
  val binsearch:     'a -> 'a array -> int
  val array_find_min: ('a -> bool) -> 'a array -> int
end = struct
  let binsearch_max (el:'a) (arr: 'a array) =
    (** The maximal index where [el] can be inserted into the array [arr]
        without disturbing the order.

        The algorithm assumes that the array is sorted *)
    let len = Array.length arr
    in
    (* all k: 0<=k<=i => arr.(k)<=el   *)
    (*        j<=k<len => el < arr.(k) *)
    let rec search i j =
      assert (0<=i); assert (i<=j); assert (j<=len);
      if (j-i) <= 1 then
        if i<j && el<arr.(i) then i else j
      else
        let m = i + (j-i)/2
        in
        if arr.(m)<=el then search m j
        else                search i m
    in
    let idx = search 0 len
    in
    assert (0<=idx && idx<=Array.length arr);
    idx


  let binsearch (el:'a) (arr: 'a array) =
    let insert_pos = binsearch_max el arr in
    if insert_pos = 0 || arr.(insert_pos-1) <> el then
      raise Not_found
    else
      insert_pos - 1


  let array_find_min (p:'a -> bool) (arr: 'a array) =
    let len = Array.length arr in
    let rec search i =
      if i=len then raise Not_found
      else begin
        assert (0<=i); assert (i<len);
        if p arr.(i)  then i
        else search (i+1)
      end
    in
    search 0
end




module IntSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = int
end)

module IntMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = int
end)


let string_of_intset (set:IntSet.t): string =
  "{"
  ^ String.concat
      ","
      (List.map string_of_int (IntSet.elements set))
  ^ "}"



let string_of_intlist (lst:int list): string =
  "["
  ^ String.concat
      ","
      (List.map string_of_int lst)
  ^ "]"


let string_of_intarray (arr:int array): string =
  string_of_intlist (Array.to_list arr)


let interval_fold (f:'a->int->'a) (a0:'a) (start:int) (beyond:int): 'a =
  assert (start <= beyond);
  let rec fold i a =
    if i = beyond then
      a
    else
      fold (i+1) (f a i)
  in
  fold 0 a0



let interval_find (f:int -> bool) (start:int) (beyond:int): int =
  assert (start <= beyond);
  let rec find i =
    if beyond <= i then
      raise Not_found
    else if f i then
      i
    else
      find (i+1)
  in
  find start


let interval_exist (f: int -> bool) (start:int) (beyond:int): bool =
  assert (start <= beyond);
  try ignore (interval_find f start beyond); true
  with Not_found -> false


let interval_for_all (f: int -> bool) (start:int) (beyond:int): bool =
  assert (start <= beyond);
  not (interval_exist (fun i -> not (f i)) start beyond)


let interval_iter (f:int -> unit) (start:int) (beyond:int): unit =
  assert (start <= beyond);
  let rec iter i =
    if i = beyond then
      ()
    else begin
      f i;
      iter (i+1)
    end
  in
  iter start




module StringSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = string
end)

module StringMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = string
end)



module Mylist: sig

  val is_empty:     'a list -> bool
  val is_singleton: 'a list -> bool
  val iteri:        (int -> 'a -> unit) -> 'a list -> unit
  val mapi:         (int -> 'a -> 'b) -> 'a list -> 'b list

  val sum:          ('a -> int) -> int -> 'a list -> int

  val has_duplicates: 'a list -> bool

  val combine:      'a list -> 'b list -> ('a*'b) list
end = struct

  let is_empty (l:'a list): bool = match l with [] -> true | _ -> false

  let is_singleton (l: 'a list): bool =
    match l with
      [_] -> true
    | _   -> false

  let iteri (f:int->'a->unit) (l:'a list): unit =
    let pos = ref 0 in
    let rec itrec l =
      match l with
        [] -> ()
      | h::t -> begin
          f !pos h;
          pos := !pos + 1;
          itrec t
      end
    in
    itrec l

  let mapi (f:int->'a->'b) (l:'a list): 'b list =
    let rec maprec l i =
      match l with
        [] -> []
      | h::tl -> (f i h)::(maprec tl (i+1))
    in
    maprec l 0

  let sum (f:'a->int) (start:int) (l:'a list): int =
    List.fold_left (fun cum e -> cum + f e) start l

  let rec has_duplicates (l:'a list): bool =
    match l with
      [] -> false
    | h::t ->
        List.mem h t || has_duplicates t

  let combine (l1: 'a list) (l2: 'b list): ('a*'b) list =
    let rec comb l1 l2 res =
      match l1, l2 with
        [], _  -> res
      | _ , [] -> res
      | a::l1, b::l2 -> comb l1 l2 ((a,b)::res)
    in
    List.rev (comb l1 l2 [])
end




module Myarray: sig

  val combine: 'a array -> 'b array -> ('a*'b) array
  val split:   ('a*'b) array -> 'a array * 'b array
  val sum: int -> int array -> int

end = struct

  let combine (a: 'a array) (b: 'b array): ('a*'b) array =
    let n = Array.length a in
    assert (n = Array.length b);
    Array.init n (fun i -> a.(i),b.(i))

  let split (c: ('a*'b) array): 'a array * 'b array =
    let a = Array.map (fun (x,_) -> x) c
    and b = Array.map (fun (_,y) -> y) c in
    a,b

  let sum (start:int) (arr:int array): int =
    Array.fold_left (fun sum n -> sum + n) start arr
end




module Mystring: sig
  val rev_split: string -> char -> string list
  val split: string -> char -> string list
  val for_all: (char -> bool) -> string -> bool
end = struct
  let rev_split (str:string) (sep:char): string list =
    let start    = ref 0
    and lst      = ref []
    and len      = String.length str
    in
    while !start < len do
      try
        let nxt = String.index_from str !start sep in
      if !start < nxt then
        lst := (String.sub str !start (nxt - !start)) :: !lst;
        start := nxt + 1
      with Not_found ->
        lst := (String.sub str !start (len - !start)) :: !lst;
        start := len
    done;
    !lst

  let split (str:string) (sep:char): string list =
    List.rev (rev_split str sep)

  let for_all (f:char->bool) (s:string): bool =
    let n = String.length s in
    let rec forall i =
      if i = n then
        true
      else
        f s.[i] && forall (i+1)
    in
    forall 0
end



module Seq: sig
  type 'a t
  val empty: unit -> 'a t
  val singleton: 'a -> 'a t
  val make:  int -> 'a -> 'a t
  val count: 'a t -> int
  val is_empty: 'a t -> bool
  val elem:  int -> 'a t -> 'a
  val first: 'a t -> 'a
  val last:  'a t -> 'a
  val copy:  'a t -> 'a t
  val put:   int -> 'a -> 'a t -> unit
  val push:  'a -> 'a t -> unit
  val pop:   int -> 'a t -> unit
  val pop_last: 'a t -> 'a
  val keep:  int -> 'a t -> unit
  val remove: int -> 'a t -> unit
  val iter:  ('a->unit) -> 'a t -> unit
  val iteri: (int->'a->unit) -> 'a t -> unit
  val find_min: ('a -> bool) -> 'a t -> int
end = struct
  type 'a t = {mutable cnt:int;
               mutable arr: 'a array}

  let empty () = {cnt=0; arr=[||]}

  let singleton (e:'a) = {cnt=1; arr=Array.make 1 e}

  let make (n:int) (e:'a) = {cnt=n; arr=Array.make n e}

  let count (seq:'a t): int  = seq.cnt

  let is_empty (seq:'s t): bool =  (count seq = 0)

  let elem (i:int) (seq:'a t): 'a =
    assert (i<seq.cnt);
    seq.arr.(i)

  let first (seq:'a t): 'a =
    assert (0 < count seq);
    elem 0 seq

  let last (seq:'a t): 'a =
    assert (0 < count seq);
    elem (count seq - 1) seq

  let copy (s:'a t): 'a t =
    {cnt = s.cnt; arr = Array.copy s.arr}

  let put (i:int) (e:'a) (seq:'a t): unit =
    assert (i<seq.cnt);
    seq.arr.(i) <- e

  let push (elem:'a) (seq:'a t): unit =
    let cnt = seq.cnt
    in
    let _ =
      if cnt = Array.length seq.arr then
        let narr =
          Array.make (1+2*cnt) elem
        in
        Array.blit seq.arr 0 narr 0 cnt;
        seq.arr <- narr
      else
        seq.arr.(cnt) <- elem
    in
    assert (cnt < Array.length seq.arr);
    seq.cnt <- cnt+1

  let pop (n:int) (seq: 'a t): unit =
    assert (n <= count seq);
    seq.cnt <- seq.cnt - n

  let keep (n:int) (seq: 'a t): unit =
    assert (n <= count seq);
    seq.cnt <- n


  let pop_last (seq:'a t): 'a =
    assert (0 < count seq);
    let e = last seq in
    pop 1 seq; e


  let iter (f:'a->unit) (s:'a t) =
    let rec iter0 i =
      if i=s.cnt then ()
      else begin
        f (elem i s);
        iter0 (i+1)
      end
    in iter0 0

  let iteri (f:int->'a->unit) (s:'a t) =
    let rec iter0 i =
      if i=s.cnt then ()
      else begin
        f i (elem i s);
        iter0 (i+1)
      end
    in iter0 0

  let find_min (f:'a->bool) (s:'a t): int =
    let cnt = count s in
    let rec find (start:int): int =
      if start = cnt then
        raise Not_found
      else if f (elem start s) then
        start
      else
        find (start+1)
    in
    find 0

  let remove (i:int) (s:'a t): unit =
    assert (i < count s);
    s.arr <-
      Array.init
        (Array.length s.arr - 1)
        (fun j ->
          if j < i then s.arr.(j)
          else s.arr.(j+1));
    s.cnt <- s.cnt - 1
end

type 'a seq = 'a Seq.t





module Key_table: sig
  type 'a t
  val empty:  unit -> 'a t
  val count:  'a t -> int
  val index:  'a  -> 'a t -> int
  val key:    int -> 'a t -> 'a
  val find:   'a -> 'a t -> int
  val iter:   ('a -> unit) -> 'a t -> unit
  val iteri:  (int->'a->unit) -> 'a t -> unit
end = struct
  type 'a t = {seq: 'a Seq.t;
               map: ('a,int) Hashtbl.t}

  let empty () = {seq=Seq.empty (); map=Hashtbl.create 53}

  let count (st:'a t)   = Seq.count st.seq

  let added (elem:'a) (st:'a t): int =
    let cnt = Seq.count st.seq
    in
    Seq.push elem st.seq;
    Hashtbl.add st.map elem cnt;
    cnt

  let find (elem:'a)  (st:'a t): int = Hashtbl.find st.map elem

  let index (elem:'a) (st:'a t): int =
    try
      Hashtbl.find st.map elem
    with
      Not_found ->
        added elem st

  let key (s:int) (st:'a t): 'a =
    assert (s < Seq.count st.seq);
    Seq.elem s st.seq

  let iter (f:'a->unit) (t:'a t) =
    Seq.iter f t.seq

  let iteri (f:int->'a->unit) (t:'a t) =
    Seq.iteri f t.seq
end







module type Set = sig
  type 'a t
  val empty:      unit -> 'a t
  val mem:        'a -> 'a t -> bool
  val plus_elem:  'a -> 'a t -> 'a t
  val plus_set:   'a t -> 'a t -> 'a t
  val test:       unit -> unit
end


module ArrayedSet: Set = struct
  type 'a t = 'a array

  let empty () = Array.init 0 (fun _ -> assert false)

  let mem (el:'a) (set:'a t) =
    let idx = Search.binsearch_max el set
    in
    0<idx && set.(idx-1)=el

  let plus_elem (el:'a) (set:'a t): 'a t =
    let i = Search.binsearch_max el set;
    and len = Array.length set
    in
    if 0<i  && set.(i-1)=el then
      set
    else
      Array.init (len+1)
        (fun j ->
          if j<i then set.(j)
          else if j=i then el
          else set.(j-1))

  let plus_set (s1:'a t) (s2:'a t): 'a t =
    let rec plus i =
      if i=0 then s1
      else plus_elem s2.(i-1) s1
    in
    plus (Array.length s2)

  let test () =
    let len = 10
    in
    let rec ins n =
      if n=0 then empty ()
      else plus_elem (len-n) (plus_elem (len-n) (ins (n-1)))
    in
    let set = ins len
    in
    let rec check n =
      if n=0 then true
      else ((n-1)=set.(n-1)) && mem (n-1) set && check (n-1)
    in
    assert (check len);
    assert (not (mem len set))
end
