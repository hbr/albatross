open Container
open Term

type t = {
    nlocal:int;                  (* local type variables without concept *)
    concepts: type_term array;   (* global type variables with concept
                                    coming from used functions           *)
    fgconcepts: type_term array; (* concepts of the formal generics      *)
    fgnames:    int array        (* names of the formal generics         *)
  }


let empty: t =
  {nlocal=0;concepts=[||];fgconcepts=[||];fgnames=[||]}



let count_fgs (tvs:t): int = Array.length tvs.fgnames


let fgconcepts (tvs:t): type_term array = tvs.fgconcepts


let fgnames (tvs:t): int array = tvs.fgnames


let has_fg (name:int) (tvs:t): bool =
  try
    let _ = Search.array_find_min (fun n -> n=name) tvs.fgnames in
    true
  with Not_found ->
    false


let make_fgs (nms: int array) (cpts:type_term array): t =
  {nlocal=0;concepts=[||];fgnames=nms;fgconcepts=cpts}


let count_local (tvs:t): int = tvs.nlocal

let count_global (tvs:t): int = Array.length tvs.concepts

let count (tvs:t): int    = tvs.nlocal + count_global tvs

let count_all(tvs:t): int = tvs.nlocal + count_global tvs + count_fgs tvs



let concept (i:int) (tvs:t): type_term =
  assert (count_local tvs <= i);
  assert (i < count_all tvs);
  if i < count tvs then
    tvs.concepts.(i - count_local tvs)
  else
    tvs.fgconcepts.(i - count tvs)

let concepts (tvs:t): type_term array = tvs.concepts



let add_fgs (tvs_new:t) (tvs:t): t =
  let nfgs0   = count_fgs tvs in
  let nfgs_delta = count_fgs tvs_new - nfgs0 in
  assert (0 <= nfgs_delta);
  assert (tvs.fgnames =
          Array.sub tvs_new.fgnames nfgs_delta nfgs0);
  assert (nfgs_delta = 0); (* remove the first time greater 0 *)
  let cnt0 = count tvs
  and cnt1 = count tvs_new in
  assert (cnt1 <= cnt0);
  let cnt_delta = cnt0 - cnt1 in
  let fgconcepts =
    Array.map (fun tp -> Term.up cnt_delta tp) tvs_new.fgconcepts
  and concepts =
    Array.map (fun tp -> Term.upbound  nfgs_delta cnt0 tp) tvs.concepts
  in
  {tvs with
   concepts   = concepts;
   fgnames    = tvs_new.fgnames;
   fgconcepts = fgconcepts}



let remove_fgs (tvs_new:t) (tvs:t): t =
  let nfgs0      = count_fgs tvs in
  let nfgs_delta = nfgs0 - count_fgs tvs_new in
  assert (0 <= nfgs_delta);
  assert (nfgs_delta = 0); (* remove the first time greater 0 *)
  let cnt0 = count tvs
  and cnt1 = count tvs_new in
  assert (cnt1 <= cnt0);
  let cnt_delta = cnt0 - cnt1 in
  try
    let fgconcepts =
      Array.map (fun tp -> Term.up cnt_delta tp) tvs_new.fgconcepts
    and concepts =
      Array.map (fun tp -> Term.down_from nfgs_delta cnt0 tp) tvs.concepts
    in
    {tvs with
     concepts   = concepts;
     fgnames    = tvs_new.fgnames;
     fgconcepts = fgconcepts}
  with Term_capture ->
    assert false (* cannot happen *)





let add_global (cs:type_term array) (tvs:t): t =
  let nglob1 = Array.length cs
  and cnt    = count tvs
  and nfgs0  = count_fgs tvs
  in
  let concepts0 = Array.map (fun tp -> Term.upbound nglob1 cnt tp) tvs.concepts
  and concepts1 = Array.map (fun tp -> Term.upbound nfgs0 nglob1 tp) cs
  in
  let concepts1 = Array.map (fun tp -> Term.up cnt tp) concepts1 in
  {tvs with
   concepts   = Array.append concepts0 concepts1;
   fgconcepts = Array.map (fun tp -> Term.upbound nglob1 cnt tp) tvs.fgconcepts}






let add_local (n:int) (tvs:t): t =
  {tvs with
   nlocal     = tvs.nlocal + n;
   concepts   = Array.map (fun tp -> Term.up n tp) tvs.concepts;
   fgconcepts = Array.map (fun tp -> Term.up n tp) tvs.fgconcepts}





let remove_local (n:int) (tvs:t): t =
  assert (n <= (count_local tvs));
  try
    {tvs with
     nlocal     = tvs.nlocal - n;
     concepts   = Array.map (fun tp -> Term.down n tp) tvs.concepts;
     fgconcepts = Array.map (fun tp -> Term.down n tp) tvs.fgconcepts}
  with Term_capture ->
    assert false (* cannot happen *)





let augment_fgs
    (fgnames: int array)
    (fgconcepts:type_term array)
    (tvs:t): t =
  let nfgs1 = Array.length fgconcepts in
  assert (Array.length fgnames = nfgs1);
  let cnt = count tvs
  and nfgs0 = count_fgs tvs in
  let fgconcepts0 =
    Array.map (fun tp -> Term.upbound nfgs1 cnt tp) tvs.fgconcepts
  and fgconcepts1 =
    Array.map (fun tp -> Term.upbound nfgs0 nfgs1 tp) fgconcepts
  in
  let fgconcepts1 = Array.map (fun tp -> Term.up cnt tp) fgconcepts1 in
  {tvs with
   fgnames    = Array.append fgnames    tvs.fgnames;
   fgconcepts = Array.append fgconcepts1 fgconcepts0}




let fgs_to_global (tvs:t):t =
  assert (count tvs = 0);
  {nlocal   = 0;
   concepts = tvs.fgconcepts;
   fgnames  = [||];
   fgconcepts = [||]}




let involved_classes (tp:type_term) (tvs:t) (set0:IntSet.t): IntSet.t =
  let rec clss (tp:type_term) (tvs:t) (set0:IntSet.t) (n:int): IntSet.t =
    assert (0 <= n);
    let nloc = count_local tvs
    and nall = count_all   tvs in
    Term.fold
      (fun set i ->
        if i < nloc then
          set
        else if i < nall then
          clss (concept i tvs) empty set (n-1)
        else
          IntSet.add i set
      )
      set0
      tp
  in
  clss tp tvs set0 (count_all tvs)
