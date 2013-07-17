module type Search_sig = sig
  val binsearch: 'a -> 'a array -> int
end

module Search = struct
  let binsearch (el:'a) (arr: 'a array) =
    (* returns the index where el had to be inserted *)
    let len = Array.length arr
    in
    (* all k: 0<=k<=i => arr.(k)<=el   *)
    (*        j<=k<len => el < arr.(k) *)
    let rec search i j =
      assert (0<=i);
      assert (i<=j);
      assert (j<=len);
      if (j-i) <= 1 then
        if i<j && el<arr.(i) then i else j
      else
        let _ = assert (i+1<j)
        and m = i + (j-i)/2
        in
        let _ = assert (0<=m && m<(Array.length arr))
        in
        if arr.(m)<=el then
          search m j
        else
          search i m
    in
    let idx = search 0 len
    in
    assert (0<=idx && idx<=Array.length arr);
    idx
end
  

module type Set_sig = sig
  type 'a set
  val empty:      unit -> 'a set
  val isin:       'a -> 'a set -> bool
  val plus_elem:  'a -> 'a set -> 'a set
  val plus_set:   'a set -> 'a set -> 'a set
  val test:       unit -> unit
end


module Set = struct
  type 'a set = 'a array

  let empty () = Array.init 0 (fun _ -> assert false)

  let plus_elem el set =
    let i = Search.binsearch el set;
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
      else ((n-1)=set.(n-1)) && check (n-1)
    in
    (*Printf.printf "arr = [";
    Array.iter (fun e -> Printf.printf "%d " e) set;
    Printf.printf "]\n";*)
    assert (check len)
end
