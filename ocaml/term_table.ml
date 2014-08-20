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

- fvars:   This is a list of pairs (nb,map) which might be empty. For each
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

type submap  = Term_sub.t IntMap.t   (* idx -> sub *)
type sublist = (int*Term_sub.t) list


type t = {
    terms: (int*int*int*term) list; (* idx,nargs,nbenv,term *)
    avars: (int*int*int) list;      (* [idx, argument variable, nargs] *)
    bvars: sublist IntMap.t;        (* bvar -> [idx,sub] *)
    fvars: (int * sublist IntMap.t) list; (* [nbenv, fvar -> [idx,sub]] *)
    fapps: (t * t array) IntMap.t;
                              (* one for each number of arguments *)
    lams:  t IntMap.t         (* one for each number of bindings *)
  }


let empty = {
  terms = [];
  avars = [];
  bvars = IntMap.empty;
  fvars = [];
  fapps = IntMap.empty;
  lams  = IntMap.empty}


let next_index (tab:t): int =
  match tab.terms with
    [] -> 0
  | (idx,_,_,_)::_ -> idx+1


let count  (tab:t): int =
  List.length tab.terms

exception Term_found of term


let terms (tab:t): (int*int*int*term) list =
  (** All the terms as a list [idx,nargs,nbenv,term] of the table [tab] in the
      reverse order in which they have been inserted.  *)
  tab.terms

let print_tab (nb:int) (tab:t): unit =
  let terms = List.rev tab.terms in
  List.iter
    (fun (idx,nargs,nbenv,t) ->
      Printf.printf "\tnb %d, idx %d, nargs %d, nbenv %d, t %s\n"
        nb idx nargs nbenv (Term.to_string t))
    terms


let termtab (idx:int) (nargs:int) (tab:t) (nb:int): term =
  (** The term associated with index [idx] having [nargs] argument variables
      of the node [tab] with [nb] bound variables.
   *)
  let rec termtab0 (tab:t) (nb:int): term =
    let aterm (avar: (int*int*int) list): unit =
      try
        let _,i,_ = List.find (fun (i,_,_) -> i = idx) avar in
        (*let i,_ = IntMap.find idx avar in*)
        raise (Term_found (Variable (nb+i)))
      with Not_found ->
        ()
    and oterm (ovars: sublist IntMap.t) (n:int): unit =
      IntMap.iter
        (fun ovar lst ->
          if List.exists (fun (i,_) -> i=idx) lst then
            raise (Term_found (Variable (ovar+n)))
        )
        ovars
    and fapp_term (fapp: (t * t array) IntMap.t): unit =
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
    and lam_term (lam: t IntMap.t): unit =
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
        tab.fvars;
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
  termtab idx nargs table 0


let join_lists (l1: sublist) (l2:sublist): sublist =
  (** Join the two disjoint lists [l1] and [l2].
   *)
  let rec join l1 l2 res =
    match l1, l2 with
      [], _  -> List.rev_append l2 res
    | _, []  -> List.rev_append l1 res
    | (idx1,sub1)::tail1, (idx2,sub2)::tail2 ->
        assert (idx1 <> idx2);
        if idx1 < idx2 then
          join l1 tail2 ((idx2,sub2)::res)
        else
          join tail1 l2 ((idx1,sub1)::res)
  in
  List.rev (join l1 l2 [])



let merge_lists (l1: sublist) (l2:sublist): sublist =
  (** Merge the two lists [l1] and [l2].

      The merged list contains only the indices which occur in both lists
      and on which the substitutions of both lists are mergable.
   *)
  let rec merge l1 l2 res =
    match l1, l2 with
      [], _  -> res
    | _ , [] -> res
    | (idx1,sub1)::tail1, (idx2,sub2)::tail2 ->
        if idx1 < idx2 then
          merge l1 tail2 res
        else if idx1 > idx2 then
          merge tail1 l2 res
        else begin
          try
            let sub = Term_sub.merge sub1 sub2 in
            merge tail1 tail2 ((idx1,sub)::res)
          with Not_found ->
            merge tail1 tail2 res
        end
  in
  List.rev (merge l1 l2 [])





let join_map (m1: submap) (m2: submap)
    : submap =
  (* Join the two disjoint maps 'm1' and 'm2' *)
  IntMap.fold
    (fun idx sub2 map ->
      assert (not (IntMap.mem idx m1)); (* maps must be disjoint! *)
      IntMap.add idx sub2 map
    )
    m2  (* map to fold *)
    m1  (* start map   *)




let merge_map (m1: submap) (m2: submap)
    : submap =
  (* Merge the two maps 'm1' and 'm2'

     The domain of the merge is the subset of the intersection of both domains
     where the corresponding substitutions are mergeable (i.e. do not have
     different terms for the same variable).
   *)
  if IntMap.is_empty m1 || IntMap.is_empty m2 then
    raise Not_found;
  let merged_res =
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
  in
  if IntMap.is_empty merged_res then
    raise Not_found
  else
    merged_res







let map_to_list(map: submap): (int * Term_sub.t) list =
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

      Note: The substitutions are valid in the environment of [t] because
            they consist of subterms of [t]. Before applying them to the
            the term [ut] at the corresponding index [idx] the term [ut]
            has to be transformed into the environment of [t].
   *)
  let rec uni (t:term) (tab:t) (nb:int): sublist =
    let basic_subs: sublist =
      try
        let t = Term.down nb t in
        List.map (fun (idx,avar,nargs) -> idx,Term_sub.singleton avar t) tab.avars
      with Term_capture ->
        []
    and subs
        (i:int)
        (mp: sublist IntMap.t)
        (base: sublist) : sublist =
      try
        join_lists (IntMap.find i mp) base
      with Not_found -> base
    in
    match t with
      Variable i when i < nb ->
        IntMap.find i tab.bvars
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
          tab.fvars
    | Application (f,args) ->
        let res =
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapps in
            let list_of (t:term) (tab:t): sublist =
              let res = uni t tab nb in
              if res=[] then raise Not_found;
              res
            in
            let res_lst = ref (list_of f ftab) in
            for i=0 to len-1 do
              let alst = list_of args.(i) argtabs.(i) in
              res_lst := merge_lists !res_lst alst
            done;
            join_lists basic_subs !res_lst
          with Not_found ->
            basic_subs
        end in
        res
    | Lam (n,_,t) ->
        try
          let ttab = IntMap.find n tab.lams in
          let tlst = uni t ttab (nb+n) in
          join_lists basic_subs tlst
        with Not_found ->
          basic_subs
  in
  try
    uni t table 0
  with Not_found ->
    []







let unify_with (t:term) (nargs:int) (nbenv:int) (table:t)
    :  (int * Term_sub.t) list =
  (** Unify the terms in the table [table] with term [t] which has [nargs]
      arguments and comes from an environment with [nbenv] variables.

      The result is a list of tuples (idx,sub) where applying the substitution
      [sub] to the term [t] yields the term at [idx].

      Note: The substitutions are valid in the environment of the term
            at idx because they are subterms of the term at [idx]. Before
            applying the substitutions to [t] [t] has to be transformed
            into the environment of the term at [idx] (e.g. in the term [t]
            space has to be made for the variables of the term at [idx]).
   *)
  let rec uniw (t:term) (tab:t) (nb:int): sublist =
    match t with
      Variable i when i < nb ->
        (* bound variable of [t] *)
        IntMap.find i tab.bvars
    | Variable i when i < nb+nargs ->
        (* argument variable of [t] *)
        List.fold_left
          (fun lst (idx,nargs_0,nbenv_0,t_0) ->
            assert (nbenv_0 <= nbenv);
            assert (not (List.exists (fun (i,_) -> i=idx) lst));
            (*if nargs_0 = 0 then*)  (* has to be checked!!! *)
              (idx, Term_sub.singleton (i-nb) t_0)::lst
            (*else lst*))
          []
          (List.rev tab.terms)
    | Variable i ->
        (* free variable of [t] *)
        let fvar = i - nargs - nb in
        let sublist =
          List.fold_left
            (fun lst (nbenv_1,fvar2sublist) ->
              assert (nbenv_1 <= nbenv);
              let fvar = fvar - (nbenv - nbenv_1) in
              if 0 <= fvar then
                try
                  let sublist = IntMap.find fvar fvar2sublist in
                  join_lists sublist lst
                with Not_found ->
                  lst
              else
                lst
            )
            []
            tab.fvars
        in
        if sublist=[] then
          raise Not_found
        else
          sublist
    | Application (f,args) ->
        let len = Array.length args in
        let ftab, argtabs = IntMap.find len tab.fapps in
        let flst = ref (uniw f ftab nb) in
        Array.iteri
          (fun i a ->
            let alst = uniw a argtabs.(i) nb in
            flst := merge_lists !flst alst)
          args;
        !flst
    | Lam (n,_,t) ->
        let ttab = IntMap.find n tab.lams in
        uniw t ttab (nb+n)
  in
  try
    uniw t table 0
  with Not_found ->
    []



let add
    (t:term) (nargs:int) (nbenv:int)
    (idx:int)
    (table:t): t =
  (** Associate the term [t] which has [nargs] arguments and comes from an
      environment with [nbenv] variables to the index [idx]
      within the node [tab].
   *)
  assert (next_index table <= idx);
  let newmap (i:int) (map: sublist IntMap.t): sublist IntMap.t =
    try
      let sublist = IntMap.find i map in
      assert (not (List.exists (fun (i,_) -> i=idx) sublist));
      let sublist = (idx,Term_sub.empty):: sublist in
      IntMap.add i sublist map
    with Not_found ->
      IntMap.add i [idx,Term_sub.empty] map
  in
  let rec add0 (t:term) (nb:int) (tab:t): t =
    assert (next_index tab <= idx);
    let tab =
      match t with
        Variable i when nb<=i && i<nb+nargs ->
          (* variable is a formal argument which can be substituted *)
          assert (not (List.exists (fun (i,_,_) -> i=idx) tab.avars));
          {tab with avars = (idx, (i-nb),nargs) :: tab.avars}
      | Variable i when nb+nargs <= i ->
          (* variable is a free variable (i.e. not substitutable *)
          let fvar = i-nargs-nb in
          {tab with fvars =
           let fvars = tab.fvars in
           match fvars with
             [] ->
               (nbenv, newmap fvar IntMap.empty) :: fvars
           | (nbnd,map)::tl ->
               assert (nbnd <= nbenv);
               if nbnd = nbenv then
                 (nbnd, newmap fvar map) :: tl
               else
                 (nbenv, newmap fvar IntMap.empty) :: fvars}
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
              empty, Array.make len empty
          in
          let ftab    = add0 f nb ftab
          and argtabs =
            Array.mapi (fun i tab  -> add0 args.(i) nb tab) argtabs
          in
          {tab with fapps = IntMap.add len (ftab,argtabs) tab.fapps}
      | Lam (n,_,t) ->
          let ttab =
            try IntMap.find n tab.lams
            with Not_found -> empty
          in
          let ttab = add0 t (nb+n) ttab in
          {tab with lams = IntMap.add n ttab tab.lams}
    in
    {tab with terms = (idx,nargs,nbenv,t)::tab.terms}
  in
  add0 t 0 table



let remove (i:int) (tab:t): t =
  let lst = List.rev tab.terms in
  List.fold_left
    (fun tab (idx,nargs,nbenv,term) ->
      if idx <> i then
        add term nargs nbenv idx tab
      else
        tab)
    empty
    lst


let unify_unique (t:term) (nbt:int) (table:t)
    : int * Term_sub.t =
  let lst = unify t nbt table in
  match lst with
    []  -> raise Not_found
  | [e] -> e
  | _   -> assert false


let unify_unique_with (t:term) (nargs:int) (nbenv:int) (table:t)
    : int * Term_sub.t =
  let lst = unify_with t nargs nbenv table in
  match lst with
    []  -> raise Not_found
  | [e] -> e
  | _   -> assert false
