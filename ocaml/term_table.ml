(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term

type sublist = (int*Term_sub.t) list

module FlowMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = flow*int
end)

module IntPairMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = int*int
end)

type t = {
    terms: (int*int*int*int*term) list;    (* idx,nb,nargs,nbenv,term *)
    avars: (int*int*int) list;             (* [idx, argument variable, nargs] *)
    bvars: sublist IntMap.t;               (* bvar -> [idx,sub] *)
    fvars: (int * sublist IntMap.t) list;  (* [nbenv, fvar -> [idx,sub]] *)
    apps:  (t array * sublist) IntMap.t;   (* one for each function variable *)
    fapps: (t * t array) IntMap.t;         (* one for each number of arguments *)
    lams:  (t list * t) IntMap.t;
                              (* one for each number of preconditions *)
    alls:  t IntMap.t;        (* one for each number of bindings *)
    somes: t IntMap.t;        (* one for each number of bindings *)
    flows: (t array) FlowMap.t;
         (* one for each flow control with the number of arguments*)
    inds: (t array) IntPairMap.t;
         (* one for each pair (nsets,nrules) *)
  }


let empty = {
  terms = [];
  avars = [];
  bvars = IntMap.empty;
  fvars = [];
  apps  = IntMap.empty;
  fapps = IntMap.empty;
  lams  = IntMap.empty;
  alls  = IntMap.empty;
  somes = IntMap.empty;
  flows = FlowMap.empty;
  inds  = IntPairMap.empty}


let count  (tab:t): int =
  List.length tab.terms

exception Term_found of term

let find_lam (n:int) (tab: t): t list * t =
  IntMap.find n tab.lams

let add_lam (n:int) (lamtab:t list * t) (tab:t): t =
  {tab with lams = IntMap.add n lamtab tab.lams}


let terms0 (tab:t): (int*int*int*int*term) list =
  (** All the terms as a list [obj,nb,nargs,nbenv,term] of the table [tab] in the
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
        (mp:   sublist IntMap.t)
        (base: sublist) : sublist =
      try
        join_lists (IntMap.find i mp) base
      with Not_found -> base
    in
    let list_of (t:term) (nb:int) (tab:t): sublist =
      let res = uni t tab nb in
      if res=[] then raise Not_found;
      res
    in
    let arglst
        (args:term array) (nb:int) (argtabs:t array)
        (lst:sublist) (use_lst:bool)
        : sublist =
      let len = Array.length args in
      assert (len = Array.length argtabs);
      let res_lst = ref lst in
      for i=0 to len-1 do
        let alst = list_of args.(i) nb argtabs.(i) in
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
    | VAppl (i,args,_) ->
        assert (nb + nbt <= i);
        let idx = i - nb - nbt in
        begin try
          let argtabs,sublst = IntMap.find idx tab.apps in
          if Array.length argtabs = 0 then
            join_lists basic_subs sublst
          else
            arglst args nb argtabs [] false
        with Not_found ->
          basic_subs
        end
    | Application (f,args,_) ->
        begin
          try
            let len           = Array.length args in
            let ftab, argtabs = IntMap.find len tab.fapps in
            arglst args nb argtabs (list_of f nb ftab) true
          with Not_found ->
            basic_subs
        end
    | Lam (n,_,pres,t,_,_) ->
        let len = List.length pres in
        begin try
          let prestablst,ttab = find_lam len tab in
          let tlst = uni t ttab (1 + nb) in
          let rec addpres pres prestablst lst =
            match pres, prestablst with
              [], [] -> lst
            | p::pres, tab::prestablst ->
                let plst = uni p tab (1+nb) in
                let lst = merge_lists plst lst in
                addpres pres prestablst lst
            | _ -> assert false (* list must have the same size *)
          in
          let tlst = addpres pres prestablst tlst in
          join_lists basic_subs tlst
        with Not_found ->
          basic_subs
        end
    | QExp (n,_,_,t,is_all) ->
        begin try
          let ttab = IntMap.find n (qmap is_all tab) in
          let tlst = uni t ttab (n+nb) in
          join_lists basic_subs tlst
        with Not_found ->
          basic_subs
        end
    | Flow (ctrl,args) ->
        let len = Array.length args in
        begin try
          let argtabs = FlowMap.find (ctrl,len) tab.flows in
          arglst args nb argtabs [] false
        with Not_found ->
          basic_subs
        end
    | Indset (nme,tp,rs) ->
        let nrules = Array.length rs in
        begin try
          let argtabs = IntPairMap.find (1,nrules) tab.inds in
          arglst rs (1+nb) argtabs [] false
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
    | VAppl (i,args,_) ->
        assert (nb + nargs + nbenv <= i);
        let idx = i - nb - nargs - nbenv in
        let argtabs,sublst = IntMap.find idx tab.apps in
        if Array.length argtabs = 0 then
          sublst
        else begin
          let lst = ref [] in
          Array.iteri
            (fun i a ->
              let alst = uniw a argtabs.(i) nb in
              lst := if i = 0 then alst else merge_lists !lst alst)
            args;
          !lst
        end
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
    | Lam (n,_,pres,t,_,_) ->
        let len = List.length pres in
        let prestabs, ttab = find_lam len tab in
        let rec addpres pres prestabs lst =
          match pres, prestabs with
            [], [] -> lst
          | p::pres, tab::prestabs ->
              let plst = uniw p tab (1+nb) in
              let lst = merge_lists plst lst in
              addpres pres prestabs lst
          | _ -> assert false (* lists must have the same size *)
        in
        let tlst = uniw t ttab (1 + nb) in
        addpres pres prestabs tlst
    | QExp (n,_,_,t,is_all) ->
        let ttab = IntMap.find n (qmap is_all tab) in
        uniw t ttab (n+nb)
    | Flow (ctrl,args) ->
        let len = Array.length args in
        let argtabs = FlowMap.find (ctrl,len) tab.flows in
        let lst = ref [] in
        Array.iteri
          (fun i a ->
            let alst = uniw a argtabs.(i) nb in
            lst := if i = 0 then alst else merge_lists !lst alst)
          args;
        !lst
    | Indset (_,_,rs) ->
        let argtabs = IntPairMap.find (1,Array.length rs) tab.inds in
        let lst = ref [] in
        Array.iteri
          (fun i a ->
            let alst = uniw a argtabs.(i) (1+nb) in
            lst := if i = 0 then alst else merge_lists !lst alst)
          rs;
        !lst
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
  let rec add0 (t:term) (nb:int) (tab:t): t =
    let tab =
      match t with
        Variable i when nb<=i && i<nb+nargs ->
          (* variable is a formal argument which can be substituted *)
          (*assert (not (List.exists (fun (i,_,_) -> i=idx) tab.avars));*)
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
      | VAppl (i,args,_) ->
          assert (nb + nargs + nbenv <= i);
          let len  = Array.length args
          and item = idx, Term_sub.empty
          and fidx = i - nb - nargs - nbenv in
          let argtabs,sublst =
            try IntMap.find fidx tab.apps
            with Not_found ->
              Array.make len empty, [] in
          let argtabs =
            Array.mapi (fun i tab  -> add0 args.(i) nb tab) argtabs in
          {tab with apps = IntMap.add fidx (argtabs,item::sublst) tab.apps}
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
      | Lam (n,_,pres,t,_,_) ->
          let len = List.length pres in
          let rec addpres pres prestablst =
            match pres, prestablst with
              [], [] -> []
            | p::pres, tab::tablst ->
                let tablst = addpres pres tablst in
                (add0 p (1+nb) tab)::tablst
            | _ ->
                assert false (* lists must have the same length *)
          in
          let prestab,ttab =
            try find_lam len tab
            with Not_found ->
              let lst = Array.to_list (Array.make (List.length pres) empty) in
              lst, empty
          in
          let ttab = add0 t (1 + nb) ttab
          and prestab = addpres pres prestab
          in
          add_lam len (prestab,ttab) tab
      | QExp (n,_,_,t,is_all) ->
          let ttab =
            try IntMap.find n (qmap is_all tab)
            with Not_found -> empty
          in
          let ttab = add0 t (nb+n) ttab in
          if is_all then
            {tab with alls = IntMap.add n ttab tab.alls}
          else
            {tab with somes = IntMap.add n ttab tab.somes}
      | Flow (ctrl,args) ->
          let n = Array.length args in
          let argtabs =
            try FlowMap.find (ctrl,n) tab.flows
            with Not_found -> Array.make n empty
          in
          let argtabs =
            Array.mapi (fun i tab -> add0 args.(i) nb tab) argtabs in
          {tab with flows = FlowMap.add (ctrl,n) argtabs tab.flows}
      | Indset (_,_,rs) ->
          let n = 1 in
          let nrules = Array.length rs in
          let argtabs =
            try IntPairMap.find (n,nrules) tab.inds
            with Not_found -> Array.make (nrules) empty in
          let argtabs =
            Array.mapi (fun i tab -> add0 rs.(i) (n+nb) tab) argtabs in
          {tab with inds = IntPairMap.add (n,nrules) argtabs tab.inds}
    in
    {tab with terms = (idx,nb,nargs,nbenv,t)::tab.terms}
  in
  add0 t 0 table




let filter (f:int -> bool) (tab:t): t =
  let filt_sub sublst = List.filter (fun (obj,_) -> f obj) sublst in
  let rec filt tab =
    {terms = List.filter (fun (obj,_,_,_,_) -> f obj) tab.terms;
     avars = List.filter (fun (obj,_,_) ->     f obj) tab.avars;
     bvars = IntMap.map filt_sub tab.bvars;
     fvars = List.map (fun (nbenv,map) -> nbenv, IntMap.map filt_sub map) tab.fvars;
     apps  = IntMap.map (fun (args,sublst) -> Array.map filt args,sublst) tab.apps;
     fapps = IntMap.map (fun (f,args) -> filt f, Array.map filt args) tab.fapps;
     lams  = IntMap.map (fun (pres,exp) -> List.map filt pres, filt exp) tab.lams;
     alls  = IntMap.map filt tab.alls;
     somes = IntMap.map filt tab.somes;
     flows = FlowMap.map (fun args -> Array.map filt args) tab.flows;
     inds  = IntPairMap.map (fun args -> Array.map filt args) tab.inds}
  in
  filt tab



let remove (idx:int) (tab:t): t =
  filter (fun i -> i <> idx) tab
