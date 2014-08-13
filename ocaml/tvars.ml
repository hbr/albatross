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


let is_equal (tp1:type_term) (tvs1:t) (tp2:type_term) (tvs2:t): bool =
  let nall1 = count_all tvs1
  and nall2 = count_all tvs2
  and nloc1 = count_local tvs1
  and nloc2 = count_local tvs2
  in
  let rec is_eq (tp1:type_term) (tp2:type_term) (nmax:int): bool =
    match tp1, tp2 with
      Variable i, Variable j when i < nloc1 || j < nloc2 ->
        false
    | Variable i, Variable j when i < nall1 && j < nall2 ->
        assert (0 < nmax);
        is_eq (concept i tvs1) (concept j tvs2) (nmax-1)
    | Variable i, Variable j when nall1 <= i && nall2 <= j ->
        (i - count_all tvs1) = (j - count_all tvs2)
    | Application (Variable i,args1), Application(Variable j,args2) ->
        let n1 = Array.length args1
        and n2 = Array.length args2 in
        let res = ref (n1 = n2 && is_eq (Variable i) (Variable j) nmax) in
        begin
          try
            for k = 0 to n1-1 do
              res := !res && is_eq args1.(k) args2.(k) nmax;
            if not !res then raise Not_found
            done;
            true
          with Not_found -> false
        end
    | _ -> false
  in
  is_eq
    tp1
    tp2
    (let n1,n2 = nall1-nloc1,nall2-nloc2 in
    if n1<=n2 then n2 else n1)



let is_equal_or_fg (tp1:type_term) (tvs1:t) (tp2:type_term) (tvs2:t): bool =
  match tp1 with
    Variable i when count_local tvs1 <= i && i < count_all tvs1 ->
      is_equal (concept i tvs1) tvs1 tp2 tvs2
  | _ -> is_equal tp1 tvs1 tp2 tvs2



let principal_class (tp:type_term) (tvs:t): int =
  let nloc = count_local tvs
  and nall = count_all tvs
  in
  let rec pcls (tp:type_term): int =
    match tp with
      Variable i when i < nloc ->
        assert false
    | Variable i when i < nall ->
        pcls (concept i tvs)
    | Variable i ->
        i - nall
    | Application (Variable i,_) ->
        pcls (Variable i)
    | _ ->
        assert false
  in
  pcls tp


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


let dummy_fgnames (n:int): int array =
  Array.init
    n
    (fun i ->
      let str = "@" ^ (string_of_int i) in
      Support.ST.symbol str)


let insert_fgs (tvs1:t) (i:int) (tvs2:t): t =
  assert (count tvs1 = 0);
  assert (count tvs2 = 0);
  assert (i <= count_fgs tvs1);
  let nfgs1  = count_fgs tvs1
  and nfgs2  = count_fgs tvs2 in
  let fgnames1 = dummy_fgnames nfgs1 in
  let fgnames =
    Array.init
      (nfgs1 + nfgs2)
      (fun j ->
        if j < i then
          fgnames1.(j)
        else if j < i + nfgs2 then
          tvs2.fgnames.(j - i)
        else
          fgnames1.(j - i - nfgs2))
  and fgconcepts =
    Array.init
      (nfgs1 + nfgs2)
      (fun j ->
        if j < i then
          Term.upbound nfgs2 i tvs1.fgconcepts.(j)
        else if j < i + nfgs2 then
          let cpt = Term.upbound (nfgs1-i) nfgs2 tvs2.fgconcepts.(j-i) in
          Term.up i cpt
        else
          Term.up nfgs2 tvs1.fgconcepts.(j-i-nfgs2))
  in
  {tvs1 with fgnames=fgnames; fgconcepts=fgconcepts}



let update_fg (i:int) (cpt:type_term) (tvs:t): t =
  assert (count tvs = 0);
  assert (i < count_fgs tvs);
  let fgconcepts = Array.copy tvs.fgconcepts in
  fgconcepts.(i) <- cpt;
  {tvs with fgconcepts = fgconcepts}



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
  let nloc = count_local tvs
  and nall = count_all   tvs in
  let rec clss (tp:type_term) (set0:IntSet.t) (n:int): IntSet.t =
    assert (0 <= n);
    Term.fold
      (fun set i ->
        if i < nloc then
          set
        else if i < nall then
          clss (concept i tvs) set (n-1)
        else
          IntSet.add (i-nall) set
      )
      set0
      tp
  in
  clss tp set0 (count_all tvs)
