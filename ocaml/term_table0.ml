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


type nd = {
    avars: (int*int) IntMap.t;(* idx -> (argument variable, nargs) *)
    bvars: IntSet.t IntMap.t; (* bvar -> idx set *)
    cvars: (int * IntSet.t IntMap.t) list;
                              (* [nbenv, cvar -> idx set] *)
    fapps: (nd * nd array) IntMap.t;
                              (* one for each number of arguments *)
    lams:  nd IntMap.t        (* one for each number of bindings *)
  }

type t = {node:nd;  next_idx: int}


let empty_node = {
  avars = IntMap.empty;
  bvars = IntMap.empty;
  cvars = [];
  fapps = IntMap.empty;
  lams  = IntMap.empty}

let empty = {node     = empty_node;
             next_idx = 0}




exception Term_found of term


let termtab (idx:int) (nargs:int) (tab:nd) (nb:int): term =
  (** The term associated with index [idx] having [nargs] argument variables
      of the node [tab] with [nb] bound variables.
   *)
  let rec termtab0 (tab:nd) (nb:int): term =
    let aterm (avar: (int*int) IntMap.t): unit =
      try
        let i,_ = IntMap.find idx avar in
        raise (Term_found (Variable (nb+i)))
        (*let i = nb + IntMap.find idx avar in
        raise (Term_found (Variable i))*)
      with Not_found ->
        ()
    and oterm (ovars: IntSet.t IntMap.t) (n:int): unit =
      IntMap.iter
        (fun ovar set ->
          if IntSet.mem idx set then
            raise (Term_found (Variable (ovar+n)))
        )
        ovars
    and fapp_term (fapp: (nd * nd array) IntMap.t): unit =
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
    and lam_term (lam: nd IntMap.t): unit =
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
  termtab idx nargs table.node 0





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



let map_to_list(map: Term_sub.t IntMap.t): (int * Term_sub.t) list =
  IntMap.fold
    (fun i sub lst -> (i,sub)::lst)
    map
    []


let unify (t:term) (nbt:int) (table:t)
    :  (int * Term_sub.t) list =
  (** Unify the term [t] which comes from an environment with [nbt] bound
      variables with the terms in the table 'table'.

      The result is a list of tuples (idx,sub) where the unified
      term [ut] has the index [idx], and applying
      the substitution [sub] to [ut] yields the term [t].
   *)
  let rec uni (t:term) (tab:nd) (nb:int): Term_sub.t IntMap.t =
    assert (nb=0); (* as long as there are no lambda terms *)
    let basic_subs: Term_sub.t IntMap.t =
      IntMap.map (fun (avar,nargs) -> Term_sub.singleton avar t) tab.avars
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
  map_to_list (uni t table.node 0)




let closed_terms (table:t): (term * int) list =
  (** The list of all closed terms in the table together with the
      indices.
   *)
  let rec terms (tab:nd) (nb:int) (lst:(term*int)list): (term * int) list =
    let idxset2lst (idxset:IntSet.t) (lst:(term*int)list) (var:int)
        : (term*int)list =
      let t = Variable var in
      IntSet.fold
        (fun idx lst ->
          (t,idx)::lst)
        idxset
        lst
    in
    let bterms lst =
      IntMap.fold
        (fun bvar idxset lst ->
          assert (bvar < nb);
          idxset2lst idxset lst bvar)
        tab.bvars
        lst
    and cterms lst =
      List.fold_left
        (fun lst (nbenv,idxmap) ->
          IntMap.fold
            (fun cvar idxset lst->
              idxset2lst idxset lst (cvar+nb))
            idxmap
            lst
        )
        lst
        tab.cvars
    and fapps lst = assert false
    and lams  lst = assert false
    in
    lams (fapps (cterms (bterms lst)))
  in
  terms table.node 0 []



let unify_with (t:term) (nargs:int) (nbenv:int) (table:t)
    :  (int * Term_sub.t) list =
  (** Unify the terms in the table [table] with term [t] which has [nargs]
      arguments and comes from an environment with [nbenv] variables.

      The result is a list of tuples (idx,sub) where applying the substitution
      [sub] to the term [t] yields the term at [idx].
   *)
  let rec uniw (t:term) (tab:t) (nb:int): Term_sub.t IntMap.t =
    match t with
      Variable i when i < nb ->
        assert false
    | Variable i ->
        assert false
    | Application (f,args) ->
        assert false
    | Lam (n,_,t) ->
        assert false
  in
  map_to_list (uniw t table 0)





let add
    (t:term) (nargs:int) (nbenv:int)
    (idx:int)
    (table:t): t =
  (** Associate the term [t] which has [nargs] arguments and comes from an
      environment with [nvenv] variables to the index [idx]
      within the node [tab].
   *)
  assert (table.next_idx <= idx);
  let newmap (i:int) (map: IntSet.t IntMap.t): IntSet.t IntMap.t =
    try
      let idxset = IntMap.find i map in
      assert (not (IntSet.mem idx idxset));
      let idxset = IntSet.add idx idxset in
      IntMap.add i idxset map
    with Not_found ->
      IntMap.add i (IntSet.singleton idx) map
  in
  let rec add0 (t:term) (nb:int) (tab:nd): nd =
    let tab =
      match t with
        Variable i when nb<=i && i<nb+nargs ->
          (* variable is a formal argument which can be substituted *)
          assert (not (IntMap.mem idx tab.avars));
          {tab with avars = IntMap.add idx ((i-nb),nargs) tab.avars}
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
  {node = add0 t 0 table.node; next_idx = idx+1}
