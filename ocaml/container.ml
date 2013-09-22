module Search: sig
  val binsearch_max: 'a -> 'a array -> int
  val array_find_min: 'a -> 'a array -> int
end = struct
  let binsearch_max (el:'a) (arr: 'a array) =
    (* returns the maximal index where el can to be inserted *)
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

  let array_find_min (el:'a) (arr: 'a array) =
    let len = Array.length arr in
    let rec search i =
      if i=len then raise Not_found
      else begin
        assert (0<=i); assert (i<len);
        if arr.(i) = el then i
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


let intset_to_string (set:IntSet.t): string =
  "{"
  ^ String.concat
      ","
      (List.map string_of_int (IntSet.elements set))
  ^ "}"



module Mylist: sig

  val is_empty:     'a list -> bool
  val is_singleton: 'a list -> bool
  val iteri:        (int -> 'a -> unit) -> 'a list -> unit
  val mapi:         (int -> 'a -> 'b) -> 'a list -> 'b list

  val sum:          ('a -> int) -> int -> 'a list -> int

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
end


module Seq: sig
  type 'a sequence
  val empty: unit -> 'a sequence
  val singleton: 'a -> 'a sequence
  val count: 'a sequence -> int
  val elem:  'a sequence -> int -> 'a
  val push:  'a sequence -> 'a -> unit
  val iter:  ('a->unit) -> 'a sequence -> unit
  val iteri: (int->'a->unit) -> 'a sequence -> unit
end = struct
  type 'a sequence = {mutable cnt:int;
                      mutable arr: 'a array}
  let empty () = {cnt=0; arr=Array.init 0 (function _ -> assert false)}
  let singleton e = {cnt=1; arr=Array.make 1 e}
  let count seq  = seq.cnt
  let elem seq i =
    assert (i<seq.cnt);
    seq.arr.(i)
  let push seq elem =
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
        ()
    in
    assert (cnt < Array.length seq.arr);
    seq.arr.(cnt) <- elem;
    seq.cnt <- cnt+1

  let iter f s =
    let rec iter0 i =
      if i=s.cnt then ()
      else begin
        f (elem s i);
        iter0 (i+1)
      end
    in iter0 0

  let iteri f s =
    let rec iter0 i =
      if i=s.cnt then ()
      else begin
        f i (elem s i);
        iter0 (i+1)
      end
    in iter0 0
end

type 'a seq = 'a Seq.sequence





module Key_table: sig
  type 'a table
  val empty:  unit -> 'a table
  val count:  'a table -> int
  val index:  'a table -> 'a -> int
  val key:    'a table -> int -> 'a
  val find:   'a table -> 'a  -> int
  val iter:   ('a -> unit) -> 'a table -> unit
  val iteri:  (int->'a->unit) -> 'a table -> unit
end = struct
  type 'a table = {seq: 'a Seq.sequence;
                   map: ('a,int) Hashtbl.t}

  let empty () = {seq=Seq.empty (); map=Hashtbl.create 53}

  let count st   = Seq.count st.seq

  let added st elem =
    let cnt = Seq.count st.seq
    in
    Seq.push st.seq elem;
    Hashtbl.add st.map elem cnt;
    cnt

  let find  st elem = Hashtbl.find st.map elem

  let index st elem =
    try
      Hashtbl.find st.map elem
    with
      Not_found ->
        added st elem

  let key st (s:int) =
    assert (s < Seq.count st.seq);
    Seq.elem st.seq s

  let iter f t =
    Seq.iter f t.seq

  let iteri f t =
    Seq.iteri f t.seq
end

type 'a key_table = 'a Key_table.table







module type Set = sig
  type 'a set
  val empty:      unit -> 'a set
  val mem:        'a -> 'a set -> bool
  val plus_elem:  'a -> 'a set -> 'a set
  val plus_set:   'a set -> 'a set -> 'a set
  val test:       unit -> unit
end


module ArrayedSet: Set = struct
  type 'a set = 'a array

  let empty () = Array.init 0 (fun _ -> assert false)

  let mem (el:'a) (set:'a set) =
    let idx = Search.binsearch_max el set
    in
    0<idx && set.(idx-1)=el

  let plus_elem (el:'a) (set:'a set) =
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

  let plus_set s1 s2 =
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
    (*Printf.printf "arr = [";
    Array.iter (fun e -> Printf.printf "%d " e) set;
    Printf.printf "]\n";*)
    assert (check len);
    assert (not (mem len set))
end

type 'a arrayed_set = 'a ArrayedSet.set
