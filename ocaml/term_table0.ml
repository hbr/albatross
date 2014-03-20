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

- avars:   There is an entry in this map for each assertion which has an
           argument variable in this position. It maps assertion ids to the
           corresponding argument variable

- bvars:   There is an entry in this map for each bound variable which appears
           in any of the assertions at this position. The map maps the bound
           variable to the set of assertion id's where the other variable
           appears at this position.

- cvars:   This is a list of pairs (nb,map) which might be empty. For each
           pair nb is the number of bound variables of the environment (i.e. 0
           for the global environment) and in the map there is an entry for
           each constant variable (i.e. variables which are neither bound by
           an abstraction nor substitutable argument variables) which appears
           in any of the assertions at this position. The map maps the
           constant variable to the set of assertion is's where the constant
           variable appears at this position.

- fapps:   There is an entry in this map for each number of arguments where a
           function application appears in any of the assertions with this
           number of arguments at that position. The map maps the number of
           arguments to a node (for the function term) and a node array (for
           the argument terms).

- lams:    There is an entry in this map for each number of arguments where a
           lambda term appears in any of the assertions with this number of
           arguments at that position. The map maps the number of bound
           variables to a node for the abstracted term.
*)

open Container
open Term


type node = {
    avars: int IntMap.t;      (* idx -> argument variable *)
    bvars: IntSet.t IntMap.t; (* bvar -> idx set *)
    cvars: (int * IntSet.t IntMap.t) list;
                              (* [nbenv, cvar -> idx set] *)
    fapps:    (node * node array) IntMap.t;
                                (* one for each number of arguments *)
    lams:  node IntMap.t      (* one for each number of bindings *)
  }


type t = {
    count: int;
    nbenv: int;
    root:  node;
  }



let empty_node = {
  avars = IntMap.empty;
  bvars = IntMap.empty;
  cvars = [];
  fapps = IntMap.empty;
  lams  = IntMap.empty
}



let global = {count = 0; nbenv = 0; root = empty_node}


let local (nb: int) (t: t): t =
  assert (0 <= nb);
  {t with nbenv = nb + t.nbenv}



let count (t:t): int = t.count

let count_environment (t:t): int = t.nbenv



exception Term_found of term


let termtab (idx:int) (nargs:int) (tab:node) (nb:int): term =
  (** The term associated with index [idx] having [nargs] argument variables
      of the node [tab] with [nb] bound variables.
   *)
  let rec termtab0 (tab:node) (nb:int): term =
    let aterm (avar: int IntMap.t): unit =
      try
        let i = nb + IntMap.find idx avar in
        raise (Term_found (Variable i))
      with Not_found ->
        ()
    and oterm (ovars: IntSet.t IntMap.t) (n:int): unit =
      IntMap.iter
        (fun ovar set ->
          if IntSet.mem idx set then
            raise (Term_found (Variable (ovar+n)))
        )
        ovars
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
    and lam_term (lam: node IntMap.t): unit =
      IntMap.iter
        (fun n ttab ->
          let t = termtab0 ttab (nb+n) in
          raise (Term_found (Lam (n,[||],t))))
        lam
    in
    try
      fapp_term tab.fapps;
      oterm     tab.bvars 0;
      List.iter
        (fun (_,map) ->
          oterm map (nb+nargs))
        tab.cvars;
      aterm     tab.avars;
      lam_term  tab.lams;
      raise Not_found
    with Term_found t ->
      t
  in
  termtab0 tab nb




let term (idx:int) (nargs:int) (table:t): term =
  (** The term associated with index [idx] with [nargs] arguments  in the
      table [table].
   *)
  assert (idx < count table);
  termtab idx nargs table.root 0





let add_set_to_map
    (set:IntSet.t)
    (map: Term_sub.t IntMap.t)
    : Term_sub.t IntMap.t =
  (** Add for each index of the set [set] an empty substitution to the map
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





let unify (t:term) (nbt:int) (table:t)
    :  (int * Term_sub.t) list =
  (** Unify the term [t] which comes from an environment with [nbt] bound
      variables with the terms in the table 'table'.

      The result is a list of tuples (idx,sub) where the unified
      term [ut] has the index [idx], and applying
      the substitution [sub] to [ut] yields the term [t].
   *)
  let rec uni (t:term) (tab:node) (nb:int): Term_sub.t IntMap.t =
    assert (nb=0); (* as long as there are no lambda terms *)
    let basic_subs: Term_sub.t IntMap.t =
      IntMap.map (fun avar -> Term_sub.singleton avar t) tab.avars
    and subs
        (i:int)
        (mp:IntSet.t IntMap.t)
        (base:Term_sub.t IntMap.t) : Term_sub.t IntMap.t =
      try
        add_set_to_map (IntMap.find i mp) base
      with Not_found -> base
    in
    match t with
      Variable i when i < nb ->
        subs i tab.bvars basic_subs
    | Variable i ->
        assert (nb <= i);
        List.fold_left
          (fun base (nbenv,map) ->
            assert (nbenv <= nbt);
            if nbt-nbenv <= i-nb then
              subs (i-nb - (nbt-nbenv)) map base
            else
              base)
          basic_subs
          tab.cvars
    | Application (f,args) ->
        let res =
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapps in
            let fmap = ref (uni f ftab nb) in
            Array.iteri
              (fun i a ->
                let amap = uni a argtabs.(i) nb in
                fmap := merge_map !fmap amap;
              )
              args;
            join_map basic_subs !fmap
          with Not_found ->
            basic_subs
        end in
        res
    | Lam (n,_,t) ->
        try
          let ttab = IntMap.find n tab.lams in
          let tmap = uni t ttab (nb+n) in
          join_map basic_subs tmap
        with Not_found ->
          basic_subs
  in
  try
    let map = uni t table.root 0 in
    let res =
      IntMap.fold
        (fun i sub lst -> (i,sub)::lst)
        map
        []
    in
    res
  with Not_found ->
    raise Not_found








let add_term
    (t:term) (nargs:int)
    (idx:int)
    (tab:node) (nbenv:int): node =
  (** Associate the term [t] which has [nargs] arguments to the index [idx]
      within the node [tab] which pertains to an environment with [nbnev]
      bound variables
   *)
  let newmap (i:int) (map: IntSet.t IntMap.t): IntSet.t IntMap.t =
    try
      let idxset = IntMap.find i map in
      let idxset = IntSet.add idx idxset in
      IntMap.add i idxset map
    with Not_found ->
      IntMap.add i (IntSet.singleton idx) map
  in
  let rec add0 (t:term) (nb:int) (tab:node): node =
    let tab =
      match t with
        Variable i when nb<=i && i<nb+nargs ->
          (* variable is a formal argument which can be substituted *)
          {tab with avars = IntMap.add idx (i-nb) tab.avars}
      | Variable i when nb+nargs <= i ->
          (* variable is a constant (i.e. not substitutable *)
          {tab with cvars =
           let cvars = tab.cvars in
           match cvars with
             [] ->
               (nbenv, newmap (i-nargs-nb) IntMap.empty) :: cvars
           | (nbnd,map)::tl ->
               assert (nbnd <= nbenv);
               if nbnd = nbenv then
                 (nbnd, newmap (i-nargs-nb) map) :: tl
               else
                 (nbenv, newmap (i-nargs-nb) IntMap.empty) :: cvars}
      | Variable i ->
          (* variable is bound by some abstraction *)
          assert (i < nb);
          {tab with bvars = newmap i tab.bvars}
      | Application (f,args) ->
          let len = Array.length args in
          let ftab,argtabs =
            try
              IntMap.find len tab.fapps
            with Not_found ->
              empty_node, Array.make len empty_node
          in
          let ftab    = add0 f nb ftab
          and argtabs =
            Array.mapi (fun i tab  -> add0 args.(i) nb tab) argtabs
          in
          {tab with fapps = IntMap.add len (ftab,argtabs) tab.fapps}
      | Lam (n,_,t) ->
          let ttab =
            try IntMap.find n tab.lams
            with Not_found -> empty_node
          in
          let ttab = add0 t (nb+n) ttab in
          {tab with lams = IntMap.add n ttab tab.lams}
    in
    tab
  in
  add0 t 0 tab







let add (t:term) (nargs:int) (table:t): t =
  (** Add the term [t] which has [nargs] arguments to the table [table].
   *)
  let idx = count table
  in
  let table =
    { table with
      count = idx+1;
      root  = add_term t nargs idx table.root table.nbenv} in
  assert (t = term ((count table)-1) nargs table);
  table
