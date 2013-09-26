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
    (*fapp:    node IntMap.t;  (* one node for the function term
                                and one node for each argument   *)
    lammap:  (typ array * node) IntMap.t (* Rework ??? *)*)
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




let merge_map (m1: substitution IntMap.t) (m2: substitution IntMap.t)
    : substitution IntMap.t =
  (* Merge the two maps 'm1' and 'm2'

     The domain of the merge is the subset of the intersection of both domains
     where the corresponding substitutions are mergeable (i.e. do not have
     different terms for the same variable).

     Note: The algorithm is more efficient if 'm1' has the smaller domain,
     because the algorithm iterates over the domain of 'm1'.
   *)
  IntMap.fold
    (fun idx sub1 res ->
      try
        let sub2 = IntMap.find idx m2 in
        try
          let sub  = Term_sub.merge sub1 sub2 in
          IntMap.add idx sub res
        with Not_found ->
          IntMap.remove idx res
      with Not_found ->
        res
    )
    m1
    IntMap.empty




let unify (t:term) (nbt:int) (table:'a t)
    :  (int * int * 'a * substitution) list =
  (* Unify the term 't' which comes from an environment with 'nbt' bound
     variables with the terms in the table 'table'.

     The result is a list of tuple (nargs,idx,data,sub) where the unified
     term 'ut' has 'nargs' arguments, it is associated with the data 'data'
     and applying the substitution 'sub' to 'ut' yields the term 't'.
   *)
  let rec uni (t:term) (tab:node) (nb:int): substitution IntMap.t =
    let map: substitution IntMap.t =
      IntMap.map (fun avar -> Term_sub.singleton (avar-nb) t) tab.avarmap
    in
    match t with
      Variable i when nb<=i && i<nbt ->
        map
    | Variable i ->
          IntMap.fold
          (fun idx (ovar,ffree) map ->
            if (i<nb && ovar=i) || ovar-ffree = i-nbt then
              IntMap.add idx Term_sub.empty map
            else
              map
          )
          tab.ovarmap
          map
    | Application (f,args) ->
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapp in
            let fmap = ref (uni f ftab nb) in
            Array.iteri
            (fun i a ->
              let amap = uni a argtabs.(i) nb in
              fmap := merge_map !fmap amap)
              args;
            !fmap
          with Not_found ->
            IntMap.empty
        end
    | Lam (tarr,t) ->
        assert false
  in
  let map = uni t table.root 0 in
    IntMap.fold
    (fun i sub lst ->
      let nargs,data = IntMap.find i table.data in
      (nargs,i,data,sub)::lst
    )
    map
    []






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
  assert
    (List.for_all
       (fun (nargs2,_,_,sub) ->
         nargs2=nargs && Term_sub.is_permutation sub
       )
       lst
    );
  table
