open Term
open Container


exception Reject


(* Substitution for the first [nsub] formal generics of [tvs1] where
   tvs1 has [n] substitutable formal generics.

   tvs1 without the first [n] formal generics is an outer environment for
   tvs2.

   tvs1 is the environment for the subtitutable formal generics and tvs2 is
   the environment for the substitution.  that the substitution applied to
   [tp1] results in [tp2].

        tvs1:      vars1 vars2   fgs                  |vars1 vars2| = n
        tvs2:                    ....   fgs
 *)

type t = {
    n: int;         (* Number of variables in tvs1 *)
    sub: type_term array;
    mutable gp1: int; (* Greatest substituted variable + 1 *)
    tvs1: Tvars.t;  (* Environment of the substituted types *)
    tvs2: Tvars.t;  (* Environment of the substitution types *)
    delta: int;     (* Number of fgs more in tvs2 than in tvs1 *)
    ct: Class_table.t
  }

let count (s:t): int = s.n

let greatest_plus1 (s:t): int = s.gp1

let has (i:int) (s:t): bool =
  assert (i < count s);
  s.sub.(i) <> empty_term

let get (i:int) (s:t): type_term =
  assert (has i s);
  s.sub.(i)

let put (i:int) (t:type_term) (s:t): unit =
  assert (i < count s);
  if not (Class_table.satisfies t s.tvs2 (Tvars.concept i s.tvs1) s.tvs1 s.ct) then
    raise Reject;
  if not (has i s) then
    begin
      s.sub.(i) <- t;
      s.gp1 <- max (i+1) s.gp1
    end
  else if not (Term.equivalent (get i s) t) then
    raise Reject

let array (len:int) (s:t): type_term array =
  assert (len <= count s);
  Array.sub s.sub 0 len


let unify (t1:type_term) (t2:type_term) (s:t): unit =
  let unicls i1 i2 =
    if i1 - s.n + s.delta = i2 then
      ()
    else
      raise Reject
  in
  let rec uni t1 t2 =
    match t1, t2 with
    | Variable i1, _ when i1 < s.n ->
       put i1 t2 s
    | Variable i1, Variable i2 ->
       unicls i1 i2
    | VAppl(i1,args1,_,_), VAppl(i2,args2,_,_) ->
       unicls i1 i2;
       uniargs args1 args2
    | Variable _, VAppl _ | VAppl _, Variable _ ->
       raise Reject
    | _, _ ->
       assert false (* cannot happen with wellformed types *)
  and uniargs args1 args2 =
    let len = Array.length args1 in
    assert (len = Array.length args2);
    for k = 0 to len - 1 do
      uni args1.(k) args2.(k)
    done
  in
  uni t1 t2

let make (n:int) (tvs1:Tvars.t) (tvs2:Tvars.t) (ct:Class_table.t): t =
  assert (Tvars.has_no_variables tvs1);
  assert (Tvars.has_no_variables tvs2);
  assert (n <= Tvars.count_fgs tvs1);
  let nfgs = Tvars.count_fgs tvs1 - n in
  assert (nfgs <= Tvars.count_fgs tvs2);
  let delta = Tvars.count_fgs tvs2 - nfgs in
  assert (
      let ok =
        interval_for_all
          (fun i ->
            Term.equivalent
              (try
                 Term.shift delta 0 (Tvars.concept i tvs1)
               with
                 Term_capture ->
                 assert false (* cannot happen *)
              )
              (Tvars.concept (i - n + delta) tvs2)
          )
          n (Tvars.count_fgs tvs1)
      in
      ok
    );
  {n; gp1 = 0; sub = Array.make n empty_term; delta; tvs1; tvs2; ct}
