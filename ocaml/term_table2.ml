open Term
open Container

type 'a t = {mutable tab: Term_table.t;
             seq: ('a*bool) seq}

let make (): 'a t = {tab = Term_table.empty; seq = Seq.empty ()}

let count_seq (t:'a t): int = Seq.count t.seq


let index_of (v:'a) (tab:'a t): int =
  Seq.find_min (fun (e,del) -> not del && e = v) tab.seq


let has (v:'a) (tab:'a t): bool =
  try
    let _ = index_of v tab in true
  with Not_found ->
    false


let terms (tab:'a t): ('a*int*int*term) list =
  let lst = Term_table.terms tab.tab in
  List.map
    (fun (idx,nbt,nbenv,t) ->
      assert (idx < count_seq tab);
      let e,del = Seq.elem idx tab.seq in
      assert (not del);
      e, nbt, nbenv, t)
    lst


let check_consistent (tab:'a t): unit =
  let lst = Term_table.terms tab.tab
  and cnt = count_seq tab in
  assert (List.for_all (fun (idx,_,_,_) -> idx < cnt) lst)
 

let add (t:term) (nargs:int) (nbenv:int) (e:'a) (tab:'a t): unit =
  assert (not (has e tab));
  let cnt = count_seq tab in
  tab.tab <- Term_table.add t nargs nbenv cnt tab.tab;
  Seq.push (e,false) tab.seq;
  check_consistent tab



let unify
    (t:term) (nargs:int) (tab:'a t)
    : ('a * Term_sub.t) list =
  check_consistent tab;
  let lst = Term_table.unify t nargs tab.tab in
  List.map
    (fun (idx,sub) ->
      assert (idx < count_seq tab);
      let e,del = Seq.elem idx tab.seq in
      assert (not del);
      e, sub)
    lst


let unify_with
    (t:term) (nargs:int) (nbenv:int) (tab:'a t)
    : ('a * Term_sub.t) list =
  let lst = Term_table.unify_with t nargs nbenv tab.tab in
  List.map
    (fun (idx,sub) ->
      assert (idx < count_seq tab);
      let e,del = Seq.elem idx tab.seq in
      assert (not del);
      e, sub)
    lst


let remove (v:'a) (tab:'a t): unit =
  try
    let idx = index_of v tab in
    let e,del = Seq.elem idx tab.seq in
    tab.tab <- Term_table.remove idx tab.tab;
    Seq.put idx (e,true) tab.seq;
    check_consistent tab
  with Not_found ->
    ()
