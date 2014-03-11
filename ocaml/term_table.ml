(*
We use a tree like datastructure which contains the structure of all terms in
the table.

A term is a recursive structure which is either a variable, an application
(i.e. a function term and a sequence of argument terms) or a lambda
abstraction (i.e. a number of arguments which are bound in the abstraction and
a term).

We need to distinguish three type of variables:

- Argument variables: They can be substituted by any term

- Bound variables: These are variables bound by some lambda abstraction. They
                   can be unified only with the same variable

- Constants: They refer to some global features and can be unified only with
             the same variable


The first type of variables are called `avar's` (argument variables), the
second and third type are called `ovar's` (other variables).

Each node of the tree has the following information

- avarmap: There is an entry in this map for each assertion which has an
           argument variable in this position. It maps assertion ids to the
           corresponding argument variable

- ovarmap: There is an entry in this map for each other variable which appears
           in any of the assertions at this position. The map maps the other
           variable to the set of assertion id's.

- fappmap: There is an entry in this map for each number of arguments where a
           function application appears in any of the assertions with this
           number of arguments at that position. The map maps the number of
           arguments to a node (for the function term) and a node array (for
           the argument terms).

- lammap:  There is an entry in this map for each number of arguments where a
           lambda term appears in any of the assertions with this number of
           arguments at that position. The map maps the number of bound
           variables to a node for the abstracted term.
*)

open Container
open Term


type node = {
    avarmap: int IntMap.t;      (* idx -> argument variable *)
    ovarmap: IntSet.t IntMap.t; (* ovar -> idx set *)
    fapp:    (node * node array) IntMap.t;
                                (* one for each number of arguments *)
    lammap:  node IntMap.t      (* one for each number of bindings *)
  }


type 'a t = {
    count: int;
    root:  node;
    data:  (int * 'a) IntMap.t
  }



let empty_node = {
  avarmap = IntMap.empty;
  ovarmap = IntMap.empty;
  fapp    = IntMap.empty;
  lammap  = IntMap.empty
}



let empty = {count = 0; root = empty_node; data = IntMap.empty}

let count (t:'a t): int = t.count

let data  (i:int) (t:'a t): int * 'a =
  assert (i < count t);
  IntMap.find i t.data


exception Term_found of term


let termtab (idx:int) (nargs:int) (tab:node) (nb:int): term =
  (* The term associated with index 'idx' of the node 'tab' with 'nb'
     bound variables.
   *)
  let rec termtab0 (tab:node) (nb:int): term =
    let aterm (avarmap: int IntMap.t): unit =
      try
        let i = nb + IntMap.find idx avarmap in
        raise (Term_found (Variable i))
      with Not_found ->
        ()
    and oterm (ovarmap: IntSet.t IntMap.t): unit =
      IntMap.iter
        (fun ovar set ->
          if IntSet.mem idx set then
            let ivar = if ovar<nb then ovar else ovar+nargs in
            raise (Term_found (Variable ivar))
        )
        ovarmap
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
    and lam_term (lammap: node IntMap.t): unit =
      IntMap.iter
        (fun n ttab ->
          let t = termtab0 ttab (nb+n) in
          raise (Term_found (Lam (n,t))))
        lammap
    in
    try
      fapp_term tab.fapp;
      oterm     tab.ovarmap;
      aterm     tab.avarmap;
      lam_term  tab.lammap;
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
  let nargs,_ = data idx table in
  termtab idx nargs table.root 0


let add_set_to_map
    (set:IntSet.t)
    (map: Term_sub.t IntMap.t)
    : Term_sub.t IntMap.t =
  (** Add for each index of the set [set] and empty substitution to the map
      [map] *)
  IntSet.fold
    (fun idx map ->
      assert (not (IntMap.mem idx map));  (* Cannot overwrite a substitution
                                             for an index *)
      IntMap.add idx Term_sub.empty map)
    set
    map



let join_map (m1: Term_sub.t IntMap.t) (m2: Term_sub.t IntMap.t)
    : Term_sub.t IntMap.t =
  (* Join the two disjoint maps 'm1' and 'm2' *)
  IntMap.fold
    (fun idx sub2 map ->
      assert (not (IntMap.mem idx m1)); (* maps must be disjoint! *)
      IntMap.add idx sub2 map
    )
    m2  (* map to fold *)
    m1  (* start map   *)




let merge_map (m1: Term_sub.t IntMap.t) (m2: Term_sub.t IntMap.t)
    : Term_sub.t IntMap.t =
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
      with Not_found ->
        res
    )
    m1
    IntMap.empty




let write_map (map: Term_sub.t IntMap.t) (level:int): unit =
  IntMap.iter
    (fun idx sub ->
      Printf.printf "%d: idx=%d, sub=%s\n" level idx (Term_sub.to_string sub)
    )
    map






let unify (t:term) (nbt:int) (table:'a t)
    :  (int * int * 'a * Term_sub.t) list =
  (* Unify the term 't' which comes from an environment with 'nbt' bound
     variables with the terms in the table 'table'.

     The result is a list of tuples (nargs,idx,data,sub) where the unified
     term 'ut' has 'nargs' arguments, it has the index 'idx', it is associated
     with the data 'data' and applying the substitution 'sub' to 'ut' yields
     the term 't'.
   *)
  let rec uni (t:term) (tab:node) (nb:int): Term_sub.t IntMap.t =
    assert (nb=0); (* as long as there are no lambda terms *)
    let map: Term_sub.t IntMap.t =
      IntMap.map (fun avar ->
        Term_sub.singleton avar t) tab.avarmap
    and ffreet = nb+nbt  (* first free variable in the term 't' *)
    in
    match t with
      Variable i when nb<=i && i<ffreet ->
        map
    | Variable i ->
        let ovar = if i<nb then i else i-nbt in
        begin
          try
            add_set_to_map (IntMap.find ovar tab.ovarmap) map
          with Not_found -> map
        end
    | Application (f,args) ->
        let res =
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapp in
            let fmap = ref (uni f ftab nb) in
            Array.iteri
              (fun i a ->
                let amap = uni a argtabs.(i) nb in
                fmap := merge_map !fmap amap;
              )
              args;
            join_map map !fmap
          with Not_found ->
            map
        end in
        res
    | Lam (n,t) ->
        try
          let ttab = IntMap.find n tab.lammap in
          let tmap = uni t ttab (nb+n) in
          join_map map tmap
        with Not_found ->
          map
  in
  try
    let map = uni t table.root 0 in
    let res =
      IntMap.fold
        (fun i sub lst ->
          let nargs,data = IntMap.find i table.data in
          (nargs,i,data,sub)::lst
        )
        map
        []
    in
    res
  with Not_found ->
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
          {tab with avarmap = IntMap.add idx (i-nb) tab.avarmap}
      | Variable i ->
          (* variable is either bound or free (not an argument) *)
          let ovar = if i<nb then i else i-nargs in
          let ovarmap =
            try
              let idxset = IntMap.find ovar tab.ovarmap in
              let idxset = IntSet.add idx idxset in
              IntMap.add ovar idxset tab.ovarmap
            with Not_found ->
              IntMap.add ovar (IntSet.singleton idx) tab.ovarmap
          in
          {tab with ovarmap = ovarmap}
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
      | Lam (n,t) ->
          let ttab =
            try IntMap.find n tab.lammap
            with Not_found -> empty_node
          in
          let ttab = add0 t (nb+n) ttab in
          {tab with lammap = IntMap.add n ttab tab.lammap}
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
