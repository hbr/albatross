(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term

type submap  = Term_sub.t IntMap.t   (* idx -> sub *)
type sublist = (int*Term_sub.t) list


type t = {
    terms: (int*int*int*int*term) list;   (* idx,nb,nargs,nbenv,term *)
    avars: (int*int*int) list;            (* [idx, argument variable, nargs] *)
    bvars: sublist IntMap.t;              (* bvar -> [idx,sub] *)
    fvars: (int * sublist IntMap.t) list; (* [nbenv, fvar -> [idx,sub]] *)
    apps:  (t array) IntMap.t; (* one for each function variable *)
    fapps: (t * t array) IntMap.t;
                              (* one for each number of arguments *)
    lams:  t option;
    alls:  t IntMap.t;        (* one for each number of bindings *)
    somes: t IntMap.t         (* one for each number of bindings *)
  }


let empty = {
  terms = [];
  avars = [];
  bvars = IntMap.empty;
  fvars = [];
  apps  = IntMap.empty;
  fapps = IntMap.empty;
  lams  = None;
  (*lams  = IntMap.empty;*)
  alls  = IntMap.empty;
  somes = IntMap.empty}


let count  (tab:t): int =
  List.length tab.terms

exception Term_found of term

let find_lam (tab:t): t =
  match tab.lams with
    None -> raise Not_found
  | Some tab -> tab
  (*IntMap.find 1 tab.lams*)

let add_lam (n:int) (lamtab:t) (tab:t): t =
  {tab with lams = Some lamtab}
  (*{tab with lams = IntMap.add 1 lamtab tab.lams}*)


let terms0 (tab:t): (int*int*int*int*term) list =
  (** All the terms as a list [idx,nb,nargs,nbenv,term] of the table [tab] in the
      reverse order in which they have been inserted.  *)
  tab.terms


let terms (tab:t): (int*int*int*term) list =
  (** All the terms as a list [idx,nargs,nbenv,term] of the table [tab] in the
      order in which they have been inserted.  *)
  List.rev_map (fun (idx,_,nargs,nbenv,term) -> idx,nargs,nbenv,term) tab.terms


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



let qmap (is_all:bool) (tab:t): t IntMap.t =
  if is_all then
    tab.alls
  else
    tab.somes


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
    let list_of (t:term) (tab:t): sublist =
      let res = uni t tab nb in
      if res=[] then raise Not_found;
      res
    in
    let arglst
        (args:term array) (argtabs:t array) (lst:sublist) (use_lst:bool): sublist =
      let len = Array.length args in
      assert (len = Array.length argtabs);
      let res_lst = ref lst in
      for i=0 to len-1 do
        let alst = list_of args.(i) argtabs.(i) in
        res_lst :=
          if i=0 && not use_lst then alst else merge_lists !res_lst alst
      done;
      join_lists basic_subs !res_lst
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
    | VAppl (i,args) ->
        assert (nb + nbt <= i);
        let idx = i - nb - nbt in
        begin try
          let argtabs = IntMap.find idx tab.apps in
          arglst args argtabs [] false
        with Not_found ->
          basic_subs
        end
    | Application (f,args,_) ->
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapps in
            arglst args argtabs (list_of f ftab) true
          with Not_found ->
            basic_subs
        end
    | Lam (n,_,t,_) ->
        begin try
          let ttab = find_lam tab in
          let tlst = uni t ttab (1 + nb) in
          join_lists basic_subs tlst
        with Not_found ->
          basic_subs
        end
    | QExp (n,_,t,is_all) ->
        begin try
          let ttab = IntMap.find n (qmap is_all tab) in
          let tlst = uni t ttab (n+nb) in
          join_lists basic_subs tlst
        with Not_found ->
          basic_subs
        end
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
          (fun lst (idx,nb_0,nargs_0,nbenv_0,t_0) ->
            assert (nbenv_0 <= nbenv);
            assert (not (List.exists (fun (i,_) -> i=idx) lst));
            try
              let t_0 = Term.down nb_0 t_0 in
              (idx, Term_sub.singleton (i-nb) t_0)::lst
            with Term_capture ->
              lst)
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
    | VAppl (i,args) ->
        assert (nb + nargs + nbenv <= i);
        let idx = i - nb - nargs - nbenv in
        let argtabs = IntMap.find idx tab.apps in
        let lst = ref [] in
        Array.iteri
          (fun i a ->
            let alst = uniw a argtabs.(i) nb in
            lst := if i = 0 then alst else merge_lists !lst alst)
          args;
        !lst
    | Application (f,args,_) ->
        let len = Array.length args in
        let ftab, argtabs = IntMap.find len tab.fapps in
        let flst = ref (uniw f ftab nb) in
        Array.iteri
          (fun i a ->
            let alst = uniw a argtabs.(i) nb in
            flst := merge_lists !flst alst)
          args;
        !flst
    | Lam (n,_,t,_) ->
        let ttab = find_lam tab in
        uniw t ttab (1 + nb)
    | QExp (n,_,t,is_all) ->
        let ttab = IntMap.find n (qmap is_all tab) in
        uniw t ttab (n+nb)
  in
  try
    uniw t table 0
  with Not_found ->
    []


let newmap (i:int) (idx:int) (map: sublist IntMap.t): sublist IntMap.t =
  try
    let sublist = IntMap.find i map in
    assert (not (List.exists (fun (i,_) -> i=idx) sublist));
    let sublist = (idx,Term_sub.empty):: sublist in
    IntMap.add i sublist map
  with Not_found ->
    IntMap.add i [idx,Term_sub.empty] map


let has (idx:int) (table:t): bool =
  List.exists (fun (i,_,_,_,_) -> i = idx) table.terms


let add
    (t:term) (nargs:int) (nbenv:int)
    (idx:int)
    (table:t): t =
  (** Associate the term [t] which has [nargs] arguments and comes from an
      environment with [nbenv] variables to the index [idx]
      within the node [tab].
   *)
  assert (not (has idx table));
  let rec add0 (t:term) (nb:int) (tab:t): t =
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
               (nbenv, newmap fvar idx IntMap.empty) :: fvars
           | (nbnd,map)::tl ->
               assert (nbnd <= nbenv);
               if nbnd = nbenv then
                 (nbnd, newmap fvar idx map) :: tl
               else
                 (nbenv, newmap fvar idx IntMap.empty) :: fvars}
      | Variable i ->
          (* variable is bound by some abstraction *)
          assert (i < nb);
          {tab with bvars = newmap i idx tab.bvars}
      | VAppl (i,args) ->
          assert (nb + nargs + nbenv <= i);
          let len = Array.length args in
          let fidx = i - nb - nargs - nbenv in
          let argtabs =
            try IntMap.find fidx tab.apps
            with Not_found -> Array.make len empty in
          let argtabs =
            Array.mapi (fun i tab  -> add0 args.(i) nb tab) argtabs in
          {tab with apps = IntMap.add fidx argtabs tab.apps}
      | Application (f,args,_) ->
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
      | Lam (n,_,t,_) ->
          let ttab =
            try find_lam tab
            with Not_found -> empty
          in
          let ttab = add0 t (1 + nb) ttab in
          add_lam n ttab tab
      | QExp (n,_,t,is_all) ->
          let ttab =
            try IntMap.find n (qmap is_all tab)
            with Not_found -> empty
          in
          let ttab = add0 t (nb+n) ttab in
          if is_all then
            {tab with alls = IntMap.add n ttab tab.alls}
          else
            {tab with somes = IntMap.add n ttab tab.somes}
    in
    {tab with terms = (idx,nb,nargs,nbenv,t)::tab.terms}
  in
  add0 t 0 table



let remove (i:int) (tab:t): t =
  let lst = terms tab in
  List.fold_left
    (fun tab (idx,nargs,nbenv,term) ->
      if idx <> i then
        add term nargs nbenv idx tab
      else
        tab)
    empty
    lst
