open Container
open Type
open Term

type node = {
    avarmap: int IntMap.t;   (* idx -> argument variable *)
    ovarmap: (int*int) IntMap.t;
                             (* idx -> other variable (free or bound),
                                       first_free *)
    fapp:    (node * node array) IntMap.t;
                             (* one for each number of arguments *)
  }


type 'a t = {
    count: int;
    root:  node;
    data:  (int * 'a) IntMap.t
  }



let empty_node = {
  avarmap = IntMap.empty;
  ovarmap = IntMap.empty;
  fapp    = IntMap.empty
}



let empty = {count = 0; root = empty_node; data = IntMap.empty}

let count (t:'a t): int = t.count

let data  (i:int) (t:'a t): int * 'a =
  assert (i < count t);
  IntMap.find i t.data


exception Term_found of term


let termtab (idx:int) (tab:node) (nb:int): term =
  (* The term associated with index 'idx' of the node 'tab' with 'nb'
     bound variables.
   *)
  let rec termtab0 (tab:node) (nb:int): term =
    let aterm (avarmap: int IntMap.t): unit =
      try
        let i = IntMap.find idx avarmap in
        raise (Term_found (Variable i))
      with Not_found ->
        ()
    and oterm (ovarmap: (int*int) IntMap.t): unit =
      try
        let i,_ = IntMap.find idx ovarmap in
        raise (Term_found (Variable i))
      with Not_found ->
        ()
    and fapp_term (fapp: (node * node array) IntMap.t): unit =
      IntMap.iter
        (fun len (ftab,argtabs) ->
          assert (len = (Array.length argtabs));
          try
            let f = termtab0 ftab nb
            and args = Array.map (fun tab -> termtab0 tab nb) argtabs
            in
            raise (Term_found (Application (f,args)))
          with Not_found ->
            ()
        )
        fapp
    in
    try
      fapp_term tab.fapp;
      oterm     tab.ovarmap;
      aterm     tab.avarmap;
      raise Not_found
    with Term_found t ->
      t
  in
  termtab0 tab nb

let term (idx:int) (table:'a t): term =
  (* The term associated with index 'idx' in the table represented by the
     root node 'tab'
   *)
  assert (idx < count table);
  termtab idx table.root 0



let join_map (m1: substitution IntMap.t) (m2: substitution IntMap.t)
    : substitution IntMap.t =
  (* Join the two disjoint maps 'm1' and 'm2' *)
  IntMap.fold
    (fun idx sub2 map ->
      assert (not (IntMap.mem idx m1)); (* maps must be disjoint! *)
      IntMap.add idx sub2 map
    )
    m2  (* map to fold *)
    m1  (* start map   *)




let merge_map (m1: substitution IntMap.t) (m2: substitution IntMap.t)
    : substitution IntMap.t =
  (* Merge the two maps 'm1' and 'm2'

     The domain of the merge is the subset of the intersection of both domains
     where the corresponding substitutions are mergeable (i.e. do not have
     different terms for the same variable).
   *)
  IntMap.fold
    (fun idx sub1 res ->
      try
        let sub2 = IntMap.find idx m2 in
        try
          let sub  = Term_sub.merge sub1 sub2 in
          IntMap.add idx sub res
        with Not_found ->
          res
          (*IntMap.remove idx res*)
      with Not_found ->
        res
    )
    m1
    IntMap.empty



let write_map (map: substitution IntMap.t) (level:int): unit =
  IntMap.iter
    (fun idx sub ->
      Printf.printf "%d: idx=%d, sub=%s\n" level idx (Term_sub.to_string sub)
    )
    map


let unify (t:term) (nbt:int) (table:'a t)
    :  (int * int * 'a * substitution) list =
  (* Unify the term 't' which comes from an environment with 'nbt' bound
     variables with the terms in the table 'table'.

     The result is a list of tuples (nargs,idx,data,sub) where the unified
     term 'ut' has 'nargs' arguments, it has the index 'idx', it is associated
     with the data 'data' and applying the substitution 'sub' to 'ut' yields
     the term 't'.  *)
  (*Printf.printf "unify size=%d nbt=%d term=%s\n"
    (count table) nbt (Term.to_string t);*)
  let rec uni (t:term) (tab:node) (nb:int) (level:int): substitution IntMap.t =
    assert (nb=0); (* as long as there are no lambda terms *)
    let map: substitution IntMap.t =
      IntMap.map (fun avar ->
        Term_sub.singleton (avar-nb) t) tab.avarmap
    and ffreet = nb+nbt  (* first free variable in the term 't' *)
    in
    match t with
      Variable i when nb<=i && i<ffreet ->
        map
    | Variable i ->
          IntMap.fold
          (fun idx (ovar,ffree) map ->
            if (i<nb && ovar=i) || ffreet<=i && ovar-ffree = i-ffreet then
              IntMap.add idx Term_sub.empty map
            else
              map
          )
          tab.ovarmap
          map
    | Application (f,args) ->
        let res =
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapp in
            let fmap = ref (uni f ftab nb (level+1)) in
            Array.iteri
              (fun i a ->
                let amap = uni a argtabs.(i) nb (level+1) in
                fmap := merge_map !fmap amap;
              )
              args;
            (*!fmap      (* join with map !!! *)*)
            join_map map !fmap
          with Not_found ->
            map
        end in
        (*Printf.printf "%d: App map\n" level;
        write_map res level;*)
        res
    | Lam (tarr,t) ->
        assert false
  in
  try
    let map = uni t table.root 0 0 in
    let res =
      IntMap.fold
        (fun i sub lst ->
          let nargs,data = IntMap.find i table.data in
          (nargs,i,data,sub)::lst
        )
        map
        []
    in
    (*Printf.printf "  uni result map:\n";
    List.iter
      (fun (nargs,idx,_,sub) ->
        Printf.printf "  nargs=%d, idx=%d, sub=%s\n"
          nargs idx (Term_sub.to_string sub)
      ) res;*)
    res
  with Not_found ->
    (*Printf.printf "not found\n";*)
    raise Not_found








let add_term (t:term) (nargs:int) (idx:int) (tab:node): node =
  (* Associate the term 't' which has 'nargs' arguments to the index 'idx'
     within the node 'tab'
   *)
  let rec add0 (t:term) (nb:int) (tab:node): node =
    let tab =
      match t with
        Variable i when nb<=i && i<nb+nargs ->
          (* variable is a formal argument which can be substituted *)
          {tab with avarmap = IntMap.add idx i tab.avarmap}
      | Variable i ->
          (* variable is either bound or free (not an argument) *)
          {tab with ovarmap = IntMap.add idx (i,nb+nargs) tab.ovarmap}
      | Application (f,args) ->
          let len = Array.length args in
          let ftab,argtabs =
            try
              IntMap.find len tab.fapp
            with Not_found ->
              empty_node, Array.make len empty_node
          in
          let ftab    = add0 f nb ftab
          and argtabs =
            Array.mapi (fun i tab  -> add0 args.(i) nb tab) argtabs
          in
          {tab with fapp = IntMap.add len (ftab,argtabs) tab.fapp}
      | Lam (tarr,t) ->
          assert false
    in
    tab
  in
  add0 t 0 tab







let add (t:term) (nargs:int) (dat:'a) (table:'a t): 'a t =
  (* Add the term 't' which has 'nargs' arguments to the table 'table' and
     associate with it the data 'dat'.
   *)
  let idx = count table
  in
  let table =
    { count = idx+1;
      root  = add_term t nargs idx table.root;
      data  = IntMap.add idx (nargs,dat) table.data } in
  assert (t = term ((count table)-1) table);
  assert ((nargs,dat) = data ((count table)-1) table);
  let lst = unify t nargs table in
  let all_injective =
    List.for_all
      (fun (_,_,_,sub) ->
        Term_sub.is_injective sub
      )
      lst
  in
  (*Printf.printf "added idx=%d, nargs=%d, term=%s\n"
    idx nargs (Term.to_string t);
  (if not all_injective then
    (Printf.printf "term = %s\n" (Term.to_string t);
     List.iter
       (fun (nargs,idx,_,sub) ->
         let t = term idx table in
         Printf.printf "nargs=%d, idx=%d, term=%s, sub=%s\n"
           nargs idx (Term.to_string t) (Term_sub.to_string sub)
       )
       lst)
  else
    ());*)
  (*assert all_injective;*) (* too strong ?! *)
  table


let write (table: 'a t): unit =
  let n = count table in
  let rec writ (i:int): unit =
    if i=0 then ()
    else
      (Printf.printf "  %2d: %s\n"
         (n-i)
         (Term.to_string (term (n-i) table));
       writ (i-1))
  in
  writ n
