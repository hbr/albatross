(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Signature
open Printf

type implementation_status = No_implementation | Builtin | Deferred


type definition = term

type formal     = int * term

type base_descriptor = {
    mutable spec:       Feature.Spec.t;
    mutable is_inh:     bool;
    mutable seeds:      IntSet.t;
    mutable variants:   int IntMap.t;  (* cls -> fidx *)
    mutable is_eq:      bool (* is equality inherited from ANY *)
  }

type descriptor = {
    mutable mdl: int;             (* -1: base feature, module not yet assigned*)
    cls:         int;             (* owner class *)
    anchor_cls:  int;
    anchor_fg:   int;
    fname:       feature_name;
    impl:        Feature.implementation;
    tvs:         Tvars.t;         (* only formal generics *)
    mutable anchored: int array;  (* formal generics anchored to the owner class *)
    argnames:    int array;
    sign:        Sign.t;
    mutable tp:  type_term;
    priv:        base_descriptor;
    mutable pub: base_descriptor option;
  }

type t = {
    mutable map: int Term_table2.t Feature_map.t;
    seq:         descriptor seq;
    mutable base:int list ref IntMap.t; (* module name -> list of features *)
    ct:          Class_table.t;
    verbosity:   int
  }


let implication_index: int =  0
let false_index:       int =  1
let true_index:        int =  2
let not_index:         int =  3
let and_index:         int =  4
let or_index:          int =  5
let eq_index:          int =  6
let in_index:          int =  7
let domain_index:      int =  8
let tuple_index:       int =  9
let first_index:       int = 10
let second_index:      int = 11


let empty (verbosity:int): t =
  {map  = Feature_map.empty;
   seq  = Seq.empty ();
   base = IntMap.empty;
   ct   = Class_table.base_table ();
   verbosity = verbosity}


let class_table (ft:t):  Class_table.t   = ft.ct
let module_table (ft:t): Module_table.t = Class_table.module_table ft.ct

let is_private (ft:t): bool = Class_table.is_private ft.ct
let is_public  (ft:t): bool = Class_table.is_public  ft.ct
let is_interface_check  (ft:t): bool = Class_table.is_interface_check ft.ct
let is_interface_use (ft:t): bool = Class_table.is_interface_use ft.ct


let count (ft:t): int =
  Seq.count ft.seq


let verbosity (ft:t): int = ft.verbosity

let descriptor (i:int) (ft:t): descriptor =
  assert (i < count ft);
  Seq.elem i ft.seq


let base_descriptor_priv (i:int) (ft:t): base_descriptor =
  assert (i < count ft);
  let desc = descriptor i ft in
  desc.priv



let signature (i:int) (ft:t): Tvars.t * Sign.t =
  let desc = descriptor i ft in
  desc.tvs, desc.sign

let class_of_feature (i:int) (ft:t): int =
  (descriptor i ft).cls


let arity (i:int) (ft:t): int =
  Sign.arity (descriptor i ft).sign


let string_of_signature (i:int) (ft:t): string =
  let desc = descriptor i ft in
  (feature_name_to_string desc.fname) ^
  (Class_table.string_of_complete_signature desc.sign desc.tvs ft.ct)


let is_feature_public (i:int) (ft:t): bool =
  assert (i < count ft);
  Option.has (descriptor i ft).pub


let feature_name (i:int) (ft:t): string =
  let desc = descriptor i ft in
  feature_name_to_string desc.fname


let base_descriptor (i:int) (ft:t): base_descriptor =
  assert (i < count ft);
  let desc = descriptor i ft in
  if is_private ft then
    desc.priv
  else
    match desc.pub with
      None ->
        printf "feature %d \"%s\" is not public\n" i (string_of_signature i ft);
        assert false (* cannot happen in public view *)
    | Some bdesc -> bdesc



let is_term_public (t:term) (nbenv:int) (ft:t): bool =
  let rec check_pub t nb =
    let check_pub_i i =
      let i = i - nb in
      assert (i < count ft);
      if not (is_feature_public i ft) then
        raise Not_found
      else
        ()
    and check_args args = Array.iter (fun t -> check_pub t nb) args
    and check_lst  lst n = List.iter  (fun t -> check_pub t (n+nb)) lst
    in
    match t with
      Variable i when i < nb ->
        ()
    | Variable i ->
        check_pub_i i
    | VAppl(i,args) ->
        check_pub_i i;
        check_args args;
    | Application(f,args,_) ->
        check_pub f nb;
        check_args args;
    | Lam(n,nms,pres0,t0,_) ->
        check_lst pres0 (1+nb);
        check_pub t0 (1+nb)
    | QExp(n,nms,t0,_) ->
        check_pub t0 (n+nb)
  in
  try
    check_pub t nbenv;
    true
  with Not_found ->
    false



(* removal of tuple accessors:
   We have to find pattern of the form

      0.second.second...second.first
      0.second.second...second.second

   where the sequence of second is less or equal [nargs-2].

   Example: nargs = 3

   [a,b,c]  ~> [0.first, 0.second.first, 0.second.second]

   There might be subexpressions of the following form in the original term:

      a.first   ~>   0.first.first
      a.second  ~>   0.first.second
      b.first   ~>   0.second.first.first
      b.second  ~>   0.second.first.second
      c.first   ~>   0.second.second.first
      c.second  ~>   0.second.second.second

   There is no ambiguity because none of these expressions fits the pattern of
   at most [nargs-2] seconds and a first or second as the outer function.
 *)



let remove_tuple_accessors (t:term) (nargs:int) (nbenv:int) (ft:t): term =
  (* Convert the inner term [t] which expects an [nargs] tuple back into its
     original form expecting [nargs] arguments.

     The function has to find subterms of the form
        0.second...first
        0.second...second
     where
        .second..
     is is zero up to [nargs-2] applications of [second] and replace them by
     the corresponding argument.  *)
  let rec untup (t:term) (nb:int) (outer:int) (nsnds:int) : term * int * int =
    (* outer 0: neither first nor second
             1: first
             2: second *)
    let first_id  = nb + 1 + nbenv + first_index
    and second_id = nb + 1 + nbenv + second_index
    and vappl i t   = VAppl (i + nargs - 1 , [|t|]), 0, 0
    in
    match t with
      Variable i when i < nb ->
        t, 0, 0
    | Variable i when i = nb ->
        assert (0 < outer);
        let nsnds2 = if nsnds <= nargs - 2 then nsnds else nargs - 2 in
        Variable (i + nsnds2 + outer - 1),
        outer,
        nsnds2
    | Variable i ->
        Variable (i + nargs - 1), 0 , 0
    | VAppl(i,args) when i = first_id ->
        assert (Array.length args = 1);
        let t,outer,nsnds = untup args.(0) nb 1 0 in
        assert (outer = 0 || outer = 1);
        assert (nsnds = 0);
        if outer = 1 then
          t, 0, 0
        else
          vappl i t
    | VAppl(i,args) when i = second_id && outer = 0 ->
        assert (Array.length args = 1);
        let t,outer,nsnds = untup args.(0) nb 2 0 in
        assert (outer = 0 || outer = 2);
        assert (nsnds = 0);
        if outer = 2 then
          t, 0, 0
        else
          vappl i t
    | VAppl(i,args) when i = second_id->
        assert (Array.length args = 1);
        assert (outer = 1 || outer = 2);
        let t1,outer1,nsnds1 = untup args.(0) nb outer (nsnds+1) in
        if outer1 = 0 || nsnds1 = 0 then
          vappl i t1
        else begin
          assert (outer1 = outer);
          t1, outer1, nsnds1-1
        end
    | VAppl(i,args) ->
        let args = Array.map (fun t -> untup0 t nb) args in
        VAppl(i + nargs - 1,args), 0, 0
    | Application(f,args,pr) ->
        let f = untup0 f nb
        and args = Array.map (fun t -> untup0 t nb) args in
        Application(f,args,pr), 0, 0
    | Lam (n,nms,pres0,t0,pr) ->
        let t0 = untup0 t0 (1+nb)
        and pres0 = untup0_lst pres0 (1+nb) in
        Lam(n,nms,pres0,t0,pr), 0, 0
    | QExp (n,nms,t0,is_all) ->
        let t0 = untup0 t0 (n+nb) in
        QExp(n,nms,t0,is_all), 0, 0
  and untup0 t nb =
    let t,_,_ = untup t nb 0 0 in t
  and untup0_lst lst nb =
    List.map (fun t -> untup0 t nb) lst
  in
  if nargs <= 1 then
      t
  else
    untup0 t 0



let beta_reduce_0
    (tlam: term) (nbenv:int) (arg:term) (ndelta:int) (ft:t): term =
  (* Beta reduce the term [tlam] which comes from an environment with [nbenv+1]
     variables where variable 0 is the argument variable. [arg] is the argument
     which is an optional tuple and comes from an environment with [nbenv+ndelta]
     variables. All possible transformations of the form [(a,b).first ~> a] and
     [(a,b).second ~> b] are done.

     The reduced term is in an environment with [nbenv+ndelta] variables. *)
  assert (ndelta = 0);
  let rec reduce (t:term) (nb:int): term =
    let first_id  = nb + 1 + nbenv + first_index
    and second_id = nb + 1 + nbenv + second_index
    and tuple_id  = nb + nbenv + ndelta + tuple_index
    in
    let reduce_args args = Array.map (fun a -> reduce a nb) args
    in
    let reduce_tuple arg fstsnd_id fstsnd =
      assert (fstsnd = 0 || fstsnd = 1);
      let tup = reduce arg nb in
      match tup with
        VAppl (i,args) when i = tuple_id ->
          assert (Array.length args = 2);
          args.(fstsnd)
      | _ ->
          VAppl (fstsnd_id - 1 + ndelta, [|tup|])
    in
    match t with
      Variable i when i < nb ->
        t
    | Variable i when i = nb ->
        Term.up nb arg
    | Variable i ->
        Variable (i - 1 + ndelta)
    | VAppl (i,args) when i = first_id ->
        assert (Array.length args = 1);
        reduce_tuple args.(0) i 0
    | VAppl (i,args) when i = second_id ->
        assert (Array.length args = 1);
        reduce_tuple args.(0) i 1
    | VAppl (i,args) ->
        let args = reduce_args args in
        VAppl (i - 1 + ndelta, args)
    | Application(f,args,pr) ->
        let f    = reduce f nb
        and args = reduce_args args in
        Application(f,args,pr)
    | Lam(n,nms,pres0,t0,pr) ->
        Lam(n, nms, pres0, reduce t0 (1+nb), pr)
    | QExp(n,nms,t0,is_all) ->
        QExp(n, nms, reduce t0 (n + nb), is_all)
  in
  reduce tlam 0




let args_of_tuple (t:term) (nbenv:int) (nargs:int) (ft:t): term array =
  (* The tuple (a,b,...) transformed into an argument array [a,b,...].
     If the tuple [t] is only an n-tuple and [m] arguments are needed with
     [n < m] the last tuple element [l] is used to generated the missing
     elements as

         l.first,  l.second.first, l.second...first, l.second...second
   *)
  assert (0 < nargs);
  let first_id  = nbenv + first_index
  and second_id = nbenv + second_index
  and tuple_id  = nbenv + tuple_index
  in
  let rec untup (t:term) (n:int) (lst:term list): int * term list =
    assert (n < nargs);
    if n + 1 = nargs then
      n + 1, t::lst
    else
      match t with
        VAppl(i,args) when i = tuple_id ->
          assert (Array.length args = 2);
          untup args.(1) (n+1) (args.(0)::lst)
      | _ ->
          n + 1, t::lst
  in
  let rec argument (i:int) (n:int) (t:term): term =
    assert (0 <= i);
    assert (i < n);
    assert (2 <= n);
    if i = 0 then
      VAppl (first_id, [|t|])
    else if i = 1 && n = 2 then
      VAppl (second_id, [|t|])
    else
      let t = VAppl(second_id, [|t|]) in
      argument (i-1) (n-1) t
  in
  let n, lst = untup t 0 [] in
  let lst =
    if n < nargs then begin
      match lst with
        [] ->
          assert false
      | h::tail ->
          let delta = nargs - n + 1 in
          let rec add_args_from i lst =
            if i = delta then
              lst
            else
              add_args_from (i + 1) ((argument i delta h) :: lst)
          in
          add_args_from 0 tail
    end else
      lst
  in
  assert (List.length lst = nargs);
  Array.of_list (List.rev lst)




let tuple_of_args (args:term array) (nbenv:int) (ft:t): term =
  (* The arguments [a,b,...] transformed to a tuple (a,b,...).
   *)
  let tup_id    = nbenv + tuple_index
  and nargs     = Array.length args in
  assert (0 < nargs);
  let rec to_tup (i:int) (t:term): term =
    if i = 0 then
      t
    else
      let i = i - 1 in
      let t = VAppl(tup_id, [|args.(i);t|]) in
      to_tup i t
  in
  let i = nargs - 1 in
  let t = args.(i) in
  let res = to_tup i t in
  assert (args = args_of_tuple res nbenv nargs ft);
  res




let add_tuple_accessors (t:term) (nargs:int) (nbenv:int) (ft:t): term =
  (* Convert the inner term [t] which has [nargs] arguments to a term with one
     argument expecting an [nargs] tuple.

     nargs = 4
     args: [0.first, 0.second.first, 0.second.second.first, 0.second.second.second]
   *)
  if nargs <= 1 then
    t
  else
    let args = args_of_tuple (Variable 0) (nbenv+1) nargs ft in
    (*let args = Array.init nargs (fun i -> argument i nargs (Variable 0)) in*)
    Term.sub t args 1



let make_lambda
    (n:int) (nms:int array) (pres:term list) (t:term) (pr:bool) (nbenv:int) (ft:t)
    : term =
  assert (0 < n);
  assert (Array.length nms = 0 || Array.length nms = n);
  let add_tup t = add_tuple_accessors t n nbenv ft in
  let t0 = add_tup t
  and pres0 = List.map add_tup pres in
  Lam(n,nms,pres0,t0,pr)



let make_application
    (f:term) (args:term array) (pred:bool) (nbenv:int) (ft:t): term =
  assert (Array.length args > 0);
  let args = [|tuple_of_args args nbenv ft|]
  in
  Application (f, args, pred)



let beta_reduce (n:int) (tlam: term) (args:term array) (nbenv:int) (ft:t): term =
  assert (0 < Array.length args);
  assert (Array.length args <= n);
  assert (Array.length args = 1);
  let t0   = remove_tuple_accessors tlam n nbenv ft in
  let args = args_of_tuple args.(0) nbenv n ft in
  Term.apply t0 args




let definition (i:int) (nb:int) (ft:t): int * int array * term =
  assert (nb <= i);
  assert (i  <= nb + count ft);
  let i = i - nb in
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  let nargs = Sign.arity desc.sign in
  let t = Feature.Spec.definition_term bdesc.spec in
  let t = Term.upbound nb nargs t in
  nargs, desc.argnames, t


let has_definition (i:int) (ft:t): bool =
  try let _ = definition i 0 ft in true
  with Not_found -> false




let preconditions (i:int) (nb:int) (ft:t): int * int array * term list =
  (* The preconditions (if there are some) of the feature [i] as optional number of
     arguments and a list of expressions transformed into an environment with [nb]
     bound variables.*)
  assert (nb <= i);
  let i = i - nb in
  let desc = descriptor i ft in
  let spec = (base_descriptor i ft).spec in
  let n = arity i ft in
  if Feature.Spec.has_preconditions spec then
    let lst = Feature.Spec.preconditions spec in
    let lst = List.map (fun t -> Term.upbound nb n t) lst in
    n, desc.argnames, lst
  else
    n, desc.argnames, []



let postconditions (i:int) (nb:int) (ft:t): int * int array * term list =
  assert (nb <= i);
  let i = i - nb in
  let desc = descriptor i ft in
  let spec = (base_descriptor i ft).spec in
  let n = arity i ft in
  if Feature.Spec.has_preconditions spec then
    let lst = Feature.Spec.postconditions spec in
    let lst = List.map (fun t -> Term.upbound nb n t) lst in
    n, desc.argnames, lst
  else
    raise Not_found



let specification (i:int) (nb:int) (ft:t): term list =
  let n, nms,  posts = postconditions i nb ft
  and n2,nms2, pres  = preconditions  i nb ft in
  let pres_rev = List.rev pres in
  assert (n = n2);
  assert (nms = nms2);
  let imp_id = n + nb + implication_index in
  List.map
    (fun t ->
      let chn = Term.make_implication_chain pres_rev t imp_id in
      QExp(n,nms,chn,true))
    posts



let owner (i:int) (ft:t): int =
  assert (i < count ft);
  (descriptor i ft).cls


let is_ghost_function (i:int) (ft:t): bool =
  assert (i < count ft);
  Sign.is_ghost (descriptor i ft).sign


let is_ghost_term (t:term) (nargs:int) (ft:t): bool =
  let rec is_ghost (t:term) (nb:int): bool =
    let rec ghost_args (args:term array) (i:int) (n:int): bool =
      if i = n then false
      else
        let ghost = is_ghost args.(i) nb in
        ghost || ghost_args args (i+1) n
    in
    match t with
      Variable i when i < nb+nargs -> false
    | Variable i ->
        is_ghost_function (i-nb-nargs) ft
    | Lam (n,_,_,t,_) ->
        is_ghost t (1+nb)
    | QExp(_,_,_,_) ->
        true
    | VAppl (i,args) ->
        is_ghost_function (i-nb-nargs) ft
    | Application (f,args,_) ->
        let fghost = is_ghost f nb in
        fghost || ghost_args args 0 (Array.length args)
  in
  is_ghost t 0


let is_total (i:int) (ft:t): bool =
  assert (i < count ft);
  true  (* nyi: features with preconditions *)

let is_predicate (i:int) (ft:t): bool =
  let desc = descriptor i ft in
  let sign = desc.sign
  and tvs  = desc.tvs in
  let nfgs = Tvars.count_all tvs in
  0 < Sign.arity sign &&
  is_total i ft &&
  Sign.has_result sign &&
  let res = Sign.result sign in
  match res with
    Variable i when nfgs <= i ->
      i - nfgs = Class_table.boolean_index
  | _ ->
      false


let standard_bdesc (i:int) (cls:int) (spec: Feature.Spec.t) (nb:int) (ft:t)
    : base_descriptor =
  {is_inh     = false;
   seeds      = IntSet.singleton i;     (* each feature is its own seed *)
   variants   = IntMap.singleton cls i; (* and own variant in its owner class *)
   spec       = spec;
   is_eq      = false}


let count_fgs (i:int) (ft:t): int =
  assert (i < count ft);
  Tvars.count_fgs (descriptor i ft).tvs


let anchor (i:int) (ft:t): int =
  let desc = descriptor i ft in
  (*let a = desc.anchor_fg in
  if a = -1 then
    raise Not_found
  else
    a*) (*anchor*)
  if Array.length desc.anchored = 1 then
    desc.anchored.(0)
  else
    raise Not_found


let has_anchor (i:int) (ft:t): bool =
  try let _ = anchor i ft in true
  with Not_found -> false



let variant (i:int) (cls:int) (ft:t): int =
  (* The variant of the feature [i] in the class [cls] *)
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  let seed_bdesc = base_descriptor (IntSet.min_elt bdesc.seeds) ft
  in
  IntMap.find cls seed_bdesc.variants



let private_variant (i:int) (cls:int) (ft:t): int =
  (* The privat variant of the feature [i] in the class [cls] *)
  assert (i < count ft);
  let bdesc      = base_descriptor_priv i ft in
  let seed_bdesc = base_descriptor_priv (IntSet.min_elt bdesc.seeds) ft in
  IntMap.find cls seed_bdesc.variants


let has_variant (i:int) (cls:int) (ft:t): bool =
  try let _ = variant i cls ft in true
  with Not_found -> false

let has_private_variant (i:int) (cls:int) (ft:t): bool =
  try let _ = private_variant i cls ft in true
  with Not_found -> false




let variant_postcondition
    (t:term) (i:int) (inew:int) (nb:int) (base_cls:int) (cls:int) (ft:t): term =
  (* The variant of the postcondition term [t] of the feature [i] with [nb]
     bound variables in the class [cls] where all features of [t] from the
     class [base_class] are transformed into their inherited variant in class
     [cls] *)
  assert (Class_table.has_ancestor cls base_cls ft.ct);
  let cnt = count ft in
  let f (j:int): int =
    if inew <> (-1) && j = i then
      cnt
    else if class_of_feature j ft = base_cls && has_anchor j ft then
      try variant j cls ft
      with Not_found ->
        printf "there is no variant of \"%s\" in class %s\n"
          (string_of_signature j ft)
          (Class_table.class_name cls ft.ct);
          assert false (* If [cls] inherits [base_cls] then there has to be a variant
                          in the descendant *)
    else
      j
  in
  Term.map_free f t nb



let variant_term (t:term) (nb:int) (base_cls:int) (cls:int) (ft:t): term =
  (* The variant of the term [t] with [nb] bound variables in the class [cls] where
     all features of [t] from the class [base_class] are transformed into their
         inherited variant in class [cls] *)
  variant_postcondition t (-1) (-1) nb base_cls cls ft



let variant_spec (i:int) (inew:int) (base_cls:int) (cls:int) (ft:t)
    : Feature.Spec.t =
  (* The variant of the specification of the feature [i] in the class [cls] where
     all features of [spec] from the class [base_class] are transformed into their
     inherited variant in class [cls] *)
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  let nargs,nms   = Feature.Spec.names bdesc.spec in
  let pres = List.map
      (fun t -> variant_term t nargs base_cls cls ft)
      (Feature.Spec.preconditions bdesc.spec)
  in
  if Feature.Spec.has_postconditions bdesc.spec then
    let posts =
      List.map
        (fun t -> variant_postcondition t i inew nargs base_cls cls ft)
        (Feature.Spec.postconditions bdesc.spec) in
    Feature.Spec.make_func_spec nms pres posts
  else
    let def = Feature.Spec.definition bdesc.spec in
    match def with
      None -> Feature.Spec.make_func_def nms None pres
    | Some defterm ->
        Feature.Spec.make_func_def
          nms (Some (variant_term defterm nargs base_cls cls ft)) pres


let definition_equality (i:int) (ft:t): term =
  assert (i < count ft);
  assert (has_definition i ft);
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  assert (Sign.has_result desc.sign);
  let nargs   = Sign.arity desc.sign
  and res_cls = Tvars.principal_class (Sign.result desc.sign) desc.tvs in
  assert (desc.cls <> -1);
  let eq_id = variant eq_index res_cls ft in
  let eq_id = nargs + eq_id
  and f_id  = nargs + i
  in
  let t = Option.value (Feature.Spec.definition bdesc.spec) in
  let f =
    if nargs = 0 then Variable f_id
    else VAppl (f_id, Array.init nargs (fun i -> Variable i))
  in
  let eq_term = Term.binary eq_id f t in
  if nargs = 0 then
    eq_term
  else
    Term.all_quantified nargs desc.argnames eq_term



let is_desc_deferred (desc:descriptor): bool =
  match desc.impl with
    Feature.Deferred -> true
  | _                -> false


let is_deferred (i:int) (ft:t): bool =
  assert (i < count ft);
  is_desc_deferred (descriptor i ft)


let names_of_formals (farr: formal array): int array =
  Array.map (fun (name,_) -> name) farr

let terms_of_formals (farr: formal array): term array =
  Array.map (fun (_,t) -> t) farr



let add_class_feature (i:int) (priv_only:bool) (pub_only:bool) (base:bool) (ft:t)
    : unit =
  (* Add the feature [i] as a class feature to the corresponding owner
     class and to the anchor class. *)
  assert (i < count ft);
  assert (not (priv_only && pub_only));
  let desc  = descriptor i ft in
  let _, anchor = Sign.anchor desc.tvs desc.sign in
  assert (0 <= desc.cls);
  Class_table.add_feature
    (i, desc.fname, desc.tp, Tvars.count_all desc.tvs)
    desc.cls
    (is_desc_deferred desc)
    priv_only
    pub_only
    base
    ft.ct;
  if anchor <> -1 && anchor <> desc.cls then begin
    (*printf "add feature %s to anchor class %s\n"
      (string_of_signature i ft)
      (Class_table.class_name anchor ft.ct);*)
    Class_table.add_feature
      (i, desc.fname, desc.tp, Tvars.count_all desc.tvs)
      anchor
      (is_desc_deferred desc)
      priv_only
      pub_only
      base
      ft.ct
  end



let export_feature (i:int) (ft:t): unit =
  (* Export the feature [i] unless it is already publicly available. *)
  assert (is_interface_check ft);
  assert (i < count ft);
  let desc = descriptor i ft in
  match desc.pub with
    None ->
      let nargs = Array.length desc.argnames in
      desc.pub <- Some (standard_bdesc i desc.cls desc.priv.spec nargs ft);
      add_class_feature i false true false ft;
  | Some _ ->
      ()



let has_equivalent (i:int) (ft:t): bool =
  false

let add_key (i:int) (ft:t): unit =
  (** Add the key of the feature [i] to the key table. *)
  assert (i < count ft);
  let desc  = Seq.elem i ft.seq in
  let ntvs  = Tvars.count_all desc.tvs
  in
  desc.tp <- Class_table.to_dummy ntvs desc.sign;
  let tab =
    try Feature_map.find desc.fname ft.map
    with Not_found ->
      let tab = Term_table2.make () in
      ft.map <- Feature_map.add desc.fname tab ft.map;
      tab
  in
  if has_equivalent i ft then
    assert false  (* raise some exception *)
  else(
    (*if Term_table2.has i tab then
      printf "add_key feature %d %s already in the table\n"
        i (feature_name_to_string desc.fname);*)
    Term_table2.add desc.tp ntvs 0 i tab)




let add_keys (ft:t): unit =
  for i = 0 to (count ft)-1 do
    add_key i ft
  done


let n_names_with_start (c:char) (size:int): int array =
  let code = Char.code c in
  Array.init size (fun i -> ST.symbol (String.make 1 (Char.chr (i + code))))

let standard_fgnames (size:int): int array =
  n_names_with_start 'A' size

let standard_argnames (size:int): int array =
  n_names_with_start 'a' size


let add_base
    (mdl_nme: string)
    (cls: int)
    (fn:feature_name)
    (concepts: type_term array)
    (argtypes: type_term array)
    (res:  type_term)
    (defer: bool)
    (ghost: bool)
    (spec: Feature.Spec.t)
    (ft:t)
    : unit =
  assert (not defer || not (Feature.Spec.has_definition spec));
  let mdl_nme            = ST.symbol mdl_nme
  in
  let sign =
    if ghost then
      Sign.make_ghost argtypes res
    else
      Sign.make_func argtypes res
  and ntvs = Array.length concepts
  and cnt  = count ft
  and nargs = Array.length argtypes
  in
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    match fn with
      FNoperator Allop
    | FNoperator Someop ->
        Some (standard_bdesc cnt cls spec nargs ft)
    | _ -> None
  in
  let tvs = Tvars.make_fgs (standard_fgnames ntvs) concepts in
  let anchored = Class_table.anchored tvs cls ft.ct in
  let anchor_fg, anchor_cls = Sign.anchor tvs sign in
  let lst =
    try IntMap.find mdl_nme ft.base
    with Not_found ->
      let lst = ref [] in
      ft.base <- IntMap.add mdl_nme lst ft.base;
      lst
  and desc = {
    mdl = -1;
    fname    = fn;
    cls      = cls;
    anchor_cls = anchor_cls;
    anchor_fg  = anchor_fg;
    impl     =
    if Feature.Spec.has_definition spec then Feature.Empty
    else if defer then Feature.Deferred
    else Feature.Builtin;
    tvs      = tvs;
    anchored = anchored;
    argnames = standard_argnames nargs;
    sign     = sign;
    tp       = Class_table.to_dummy ntvs sign;
    priv     = bdesc;
    pub      = bdesc_opt
  }
  in
  Seq.push desc ft.seq;
  lst := cnt :: !lst



let base_table (verbosity:int) : t =
  (** Construct a basic table which contains at least implication.  *)
  let bool    = Class_table.boolean_type 0 in
  let ft      = empty verbosity
  in
  let any1  = Variable (Class_table.any_index+1)
  and any2  = Variable (Class_table.any_index+2)
  and bool1 = Variable (Class_table.boolean_index+1)
  and g_tp  = Variable 0
  and a_tp  = Variable 0
  and b_tp  = Variable 1 in
  let p_tp1 = VAppl (Class_table.predicate_index+1, [|g_tp|])
  and p_tp2 = VAppl (Class_table.predicate_index+2, [|a_tp|])
  and f_tp  = VAppl (Class_table.function_index+2, [|a_tp;b_tp|])
  and tup_tp= VAppl (Class_table.tuple_index+2, [|a_tp;b_tp|])
  and spec_none n = Feature.Spec.make_func_def (standard_argnames n) None []
  and spec_term n t = Feature.Spec.make_func_def (standard_argnames n) (Some t) []
  in
  add_base (* ==> *)
    "boolean" Class_table.boolean_index (FNoperator DArrowop)
    [||] [|bool;bool|] bool false false (spec_none 2) ft;

  add_base (* false *)
    "boolean" Class_table.boolean_index FNfalse
    [||] [||] bool false false (spec_none 0) ft;

  let imp_id1   = 1 + implication_index
  and false_id1 = 1 + false_index
  and false_id2 = 2 + false_index
  and imp_id2   = 2 + implication_index
  and not_id2   = 2 + not_index
  in
  let not_term = Term.binary imp_id1 (Variable 0) (Variable false_id1)
  and or_term  =  Term.binary imp_id2 (Term.unary not_id2 (Variable 0)) (Variable 1)
  and and_term =
    Term.unary  not_id2
      (Term.binary imp_id2
         (Variable 0)
         (Term.binary imp_id2 (Variable 1) (Variable false_id2)))
  and true_term =
    Term.binary implication_index (Variable false_index) (Variable false_index)
  in
  add_base (* true *)
    "boolean" Class_table.boolean_index FNtrue
    [||] [||] bool false false (spec_term 0 true_term) ft;

  add_base (* not *)
    "boolean" Class_table.boolean_index (FNoperator Notop)
    [||] [|bool|] bool false false (spec_term 1 not_term) ft;

  add_base (* and *)
    "boolean" Class_table.boolean_index (FNoperator Andop)
    [||] [|bool;bool|] bool false false (spec_term 2 and_term) ft;

  add_base (* or *)
    "boolean" Class_table.boolean_index (FNoperator Orop)
    [||] [|bool;bool|] bool false false (spec_term 2 or_term) ft;

  add_base (* equality *)
    "any" Class_table.any_index (FNoperator Eqop)
    [|any1|] [|g_tp;g_tp|] bool1 true false (spec_none 2) ft;

  add_base (* in *)
    "predicate" Class_table.predicate_index (FNoperator Inop)
    [|any1|] [|g_tp;p_tp1|] bool1 false false (spec_none 2) ft;

  add_base (* domain *)
    "function" Class_table.function_index (FNname ST.domain)
    [|any2;any2|] [|f_tp|] p_tp2 false true (spec_none 1) ft;

  add_base (* tuple *)
    "tuple" Class_table.tuple_index (FNname ST.tuple)
    [|any2;any2|] [|a_tp;b_tp|] tup_tp false false (spec_none 2) ft;

  add_base (* first *)
    "tuple" Class_table.tuple_index (FNname ST.first)
    [|any2;any2|] [|tup_tp|] a_tp false false (spec_none 1) ft;

  add_base (* second *)
    "tuple" Class_table.tuple_index (FNname ST.second)
    [|any2;any2|] [|tup_tp|] b_tp false false (spec_none 1) ft;

  assert ((descriptor implication_index ft).fname = FNoperator DArrowop);
  assert ((descriptor false_index ft).fname       = FNfalse);
  assert ((descriptor not_index ft).fname         = FNoperator Notop);
  assert ((descriptor and_index ft).fname         = FNoperator Andop);
  assert ((descriptor or_index ft).fname          = FNoperator Orop);
  assert ((descriptor eq_index ft).fname          = FNoperator Eqop);
  assert ((descriptor domain_index ft).fname      = FNname ST.domain);
  assert ((descriptor tuple_index ft).fname       = FNname ST.tuple);
  assert ((descriptor first_index ft).fname       = FNname ST.first);
  assert ((descriptor second_index ft).fname      = FNname ST.second);
  ft




let find_with_signature (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t): int =
  (* Find the feature with the characteristics.  *)
  let ntvs = Tvars.count_all tvs in
  let tp   = Class_table.to_dummy ntvs sign in
  let ntvs = Tvars.count_all tvs
  and tab = Feature_map.find fn ft.map in
  let lst  = Term_table2.unify tp ntvs tab in
  let idx_lst =
    List.fold_left
      (fun lst (i,sub) ->
        let desc = descriptor i ft in
        if Tvars.is_equivalent tvs desc.tvs && Term_sub.is_identity sub then
          i :: lst
        else
          let ok =
            Term_sub.for_all
              (fun j t ->
                Class_table.satisfies
                  t tvs
                  (Tvars.concept j desc.tvs) desc.tvs
                  ft.ct)
              sub
          in
          if ok then begin
            let owner = Class_table.owner tvs sign ft.ct in
            try
              let ivar = variant i owner ft in
              ivar :: lst
            with Not_found ->
              assert false (* cannot happen, feature must be inherited *)
          end else
            lst)
      []
      lst
  in
  match idx_lst with
    [] -> raise Not_found
  | idx::rest ->
      assert (List.for_all (fun i -> i=idx) rest);
      idx


let has_with_signature (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t): bool =
  try
    let _ = find_with_signature fn tvs sign ft in true
  with Not_found -> false





let find_funcs
    (fn:feature_name)
    (nargs:int) (ft:t)
    : (int * Tvars.t * Sign.t) list =
  let tab = Feature_map.find fn ft.map in
  let lst =
    List.fold_left
      (fun lst (i,_,_,_) ->
        let desc = descriptor i ft in
        let sign = desc.sign in
        let arity = Sign.arity sign
        and tvs   = Tvars.fgs_to_global desc.tvs
        in
        let nfgs = Tvars.count_all tvs in
        if is_public ft && not (Option.has desc.pub) then
          lst
        else if arity <= nargs then
          (i,tvs,sign) :: lst
        else if nargs = 0 then begin (* upgrade *)
          assert (0 < arity);
          let is_pred = is_predicate i ft in
          let tp = Class_table.upgrade_signature nfgs is_pred sign in
          let s  = Sign.make_const tp in
          (i,tvs,s) :: lst
        end else
          lst
      )
      []
      (Term_table2.terms tab)
  in
  if lst = [] then raise Not_found
  else lst


let adapt_names (nms:int array) (names:int array): int array =
  let nms  = Array.copy nms in
  let nnms = Array.length nms in
  let patch i =
    assert (i < nnms);
    let str = "$" ^ (ST.string nms.(i)) in
    nms.(i) <- ST.symbol str
  and has i =
    assert (i < nnms);
    try
      let _ = Search.array_find_min (fun nme -> nme = nms.(i)) names in
      true
    with Not_found ->
      false
  in
  let rec patch_until_ok i =
    if has i then begin
      patch i;
      patch_until_ok i
    end
  in
  for i = 0 to nnms - 1 do
    patch_until_ok i
  done;
  nms


let term_to_string
    (t:term)
    (norm:bool)
    (nanon: int)
    (names: int array)
    (ft:t)
    : string =
  (** Convert the term [t] in an environment with the named variables [names]
      to a string.
   *)
  let anon_symbol (i:int) (nanon:int): int =
      ST.symbol ("$" ^ (string_of_int (nanon+i)))
  in
  let rec to_string
      (t:term)
      (names: int array)
      (nanonused: int)
      (is_fun: bool)
      (outop: (operator*bool) option)
      : string =
    (* nanonused: number of already used anonymous variables
       is_fun: the term is used in a function position
       outop: the optional outer operator and a flag if the current term
              is the left operand of the outer operator
     *)
    let nnames = Array.length names
    and anon2sym (i:int): int = anon_symbol i nanonused
    in
    let find_op_int (i:int): operator =
      if nnames <= i then
        match (Seq.elem (i-nnames) ft.seq).fname with
          FNoperator op -> op
        | _ -> raise Not_found
      else
        raise Not_found
    in
    let var2str (i:int): string =
      if i < nnames then
        ST.string names.(i)
      else
        feature_name_to_string
          (Seq.elem (i-nnames) ft.seq).fname
    and find_op (f:term): operator  =
      match f with
        Variable i -> find_op_int i
      | _ -> raise Not_found
    and args2str (n:int) (nms:int array): string =
      let nnms  = Array.length nms in
      assert (nnms = n);
      let argsstr = Array.init n (fun i -> ST.string nms.(i)) in
      String.concat "," (Array.to_list argsstr)
    in
    let local_names (n:int) (nms:int array): int * int array =
      let nnms  = Array.length nms in
      if n = nnms then
        nanonused, nms
      else
        nanonused+n, Array.init n anon2sym
    in
    let lam_strs (n:int) (nms:int array) (ps:term list) (t:term)
        : string * string *string =
      let nanonused, nms = local_names n nms in
      let names = Array.append nms names in
      args2str n nms,
      String.concat ";" (List.map (fun t -> to_string t names nanonused false None) ps),
      to_string t names nanonused false None
    in
    let default_fapp (f:term) (argsstr:string): string =
      (to_string f names nanonused true None) ^ "(" ^ argsstr ^ ")" in
    let funiapp2str (i:int) (argsstr:string): string =
      if nnames <= i then
        let fn = (descriptor (i-nnames) ft).fname in
        begin match fn with
          FNname fsym ->
            if fsym = (ST.symbol "singleton") then
              "{" ^ argsstr ^ "}"
            else if fsym = ST.tuple then
              "(" ^ argsstr ^ ")"
            else
              default_fapp (Variable i) argsstr
        | _ -> default_fapp (Variable i) argsstr
        end
      else
        default_fapp (Variable i) argsstr
    in
    let funapp2str (f:term) (argsstr:string): string =
      match f with
        Variable i ->
          funiapp2str i argsstr
      | _ -> default_fapp f argsstr
    in
    let argsstr (args: term array): string =
      String.concat
        ","
        (List.map
           (fun t -> to_string t names nanonused false None)
           (Array.to_list args))
    in
    let op2str (op:operator) (args: term array): string =
      match op with
        Allop | Someop -> assert false (* cannot happen *)
      | _ ->
          let nargs = Array.length args in
          if nargs = 1 then
            (operator_to_rawstring op) ^ " "
            ^ (to_string args.(0) names nanonused false (Some (op,false)))
          else begin
            assert (nargs=2); (* only unary and binary operators *)
            (to_string args.(0) names nanonused false (Some (op,true)))
            ^ " " ^ (operator_to_rawstring op) ^ " "
        ^ (to_string args.(1) names nanonused false (Some (op,false)))
          end
    and lam2str (n:int) (nms: int array) (pres:term list) (t:term) (pr:bool): string =
      let argsstr, presstr, tstr = lam_strs n nms pres t in
      if pr then
        "{" ^ argsstr ^ ": " ^ tstr ^ "}"
      else
        match pres with
          [] -> "((" ^ argsstr ^ ") -> " ^ tstr ^ ")"
        | _ -> "agent (" ^ argsstr ^ ") require " ^
            presstr ^
            " ensure Result = " ^ tstr ^ " end"
    in
    let inop, str =
      match t with
        Variable i ->
          None, var2str i
      | VAppl (i,args) ->
          begin try
            let op = find_op_int i in
            Some op, op2str op args
          with Not_found ->
            None, funiapp2str i (argsstr args)
          end
      | Application (f,args,pr) ->
          begin
            try
              let op = find_op f in
              Some op, op2str op args
            with Not_found ->
              None, funapp2str f (argsstr args)
          end
      | Lam (n,nms,pres,t,pr) ->
          let nms = adapt_names nms names in
          let nbenv = Array.length names in
          let remove_tup t = remove_tuple_accessors t n nbenv ft in
          let pres, t =
            if norm then
              List.map remove_tup pres,
              remove_tup t
            else
              pres,t in
          None, lam2str n nms pres t pr
      | QExp (n,nms,t,is_all) ->
          let nms = adapt_names nms names in
          let op, opstr  = if is_all then Allop, "all"  else Someop, "some"
          and argsstr, _, tstr = lam_strs n nms [] t in
          Some op, opstr ^ "(" ^ argsstr ^ ") " ^ tstr
    in
    match inop, outop with
      Some iop, Some (oop,is_left) ->
        let _,iprec,iassoc = operator_data iop
        and _,oprec,oassoc = operator_data oop
        in
        let paren1 = iprec < oprec
        and paren2 = (iop = oop) &&
          match oassoc with
            Left     -> not is_left
          | Right    -> is_left
          | Nonassoc -> true
        and paren3 = (iprec = oprec) && (iop <> oop)
        in
        if  paren1 || paren2 || paren3 then
          "(" ^ str ^ ")"
        else
          str
    | Some iop, None when is_fun ->
        "(" ^ str ^ ")"
    | _ -> str
  in
  let nnames = Array.length names in
  let names = Array.init (nnames + nanon)
      (fun i ->
        if i<nanon then anon_symbol i 0
        else names.(i-nanon))
  in
  to_string t names nanon false None






let print (ft:t): unit =
  Seq.iteri
    (fun i fdesc ->
      let name   = feature_name_to_string fdesc.fname
      and mdlnme =
        if fdesc.mdl = -1
        then ""
        else
          Class_table.module_name fdesc.mdl ft.ct
      and tname  =
        Class_table.string_of_signature
          fdesc.sign fdesc.tvs ft.ct
      and bdyname spec =
        let def_opt = Feature.Spec.definition spec in
        match def_opt with
          None -> "Basic"
        | Some def -> term_to_string def true 0 fdesc.argnames ft
      and clsnme =
        if fdesc.cls = -1 then ""
        else Class_table.class_name fdesc.cls ft.ct
      in
      match fdesc.pub with
        None ->
          Printf.printf "%s.%s: %s %s = (%s)\n"
            mdlnme clsnme name tname (bdyname fdesc.priv.spec)
      | Some pdef ->
          Printf.printf "%s.%s: %s %s = (%s, %s)\n"
            mdlnme clsnme name tname
            (bdyname fdesc.priv.spec) (bdyname pdef.spec))
    ft.seq




let find_variant_candidate (i:int) (cls:int) (ft:t): int =
  (* Find the variant of the feature [i] in the class [cls] *)
  assert (has_anchor i ft); (* exactly one formal generic anchored
                               to the owner class *)
  let ct = class_table ft
  and desc = descriptor i ft in
  let nfgs = Tvars.count_all desc.tvs
  and fg_anchor = anchor i ft in
  let candidates = Class_table.find_features
      (desc.fname, desc.tp, nfgs)
      cls
      ct
  in
  let lst = List.filter
      (fun (idx,sub) ->
        try
          let desc_heir = descriptor idx ft in
          for k = 0 to nfgs - 1 do
            let tp1  = Term_sub.find k sub
            and tvs1 = desc_heir.tvs in
            if k = fg_anchor then
              let tp2,tvs2 = Class_table.class_type desc_heir.cls ct
              in
              if Tvars.is_equal_or_fg tp1 tvs1 tp2 tvs2
              then ()
              else raise Not_found
            else if Tvars.is_equal tp1 tvs1 (Variable k) desc.tvs
            then ()
            else raise Not_found
          done;
          true
        with Not_found ->
          false)
      candidates
  in
  match lst with
    [] -> raise Not_found
  | [i_variant,_] -> i_variant
  | _ -> assert false (* cannot happen *)



let has_variant_candidate (i:int) (cls:int) (ft:t): bool =
  (* Has the feature [i] a variant in the class [cls]? *)
  try let _ = find_variant_candidate i cls ft in true
  with Not_found -> false


let split_equality (t:term) (nbenv:int) (ft:t): int * int * term * term =
  (* Return [nargs, eq_id, left, right] if the term is an equality. *)
  let nargs, t =
    try
      let n,nms,t0 = Term.all_quantifier_split t in
      n, t0
    with Not_found ->
      0, t
  in
  let nbenv = nbenv + nargs in
  let i,a,b = Term.binary_split_0 t in
  let i = i - nbenv in
  assert (i < count ft);
  if (base_descriptor i ft).is_eq then begin
    nargs, i, a, b
  end else
    raise Not_found


let is_equality (t:term) (nbenv:int) (ft:t): bool =
  try
    let _ = split_equality t nbenv ft in true
  with Not_found -> false



let update_equality (seed:int) (bdesc:base_descriptor) (ft:t): unit =
  (* If the feature [seed] is the equality feature of ANY then mark the base
     descriptor [bdesc] as equality. *)
  if seed = eq_index then begin
    bdesc.is_eq <- true;
  end



let inherit_feature (i0:int) (i1:int) (cls:int) (export:bool) (ft:t): unit =
  (* Inherit the feature [i0] as the feature [i1] in the class [cls], i.e. add
     [i1] as a variant to all seeds of [i0] and add all seeds of [i0] as seeds
     of [i1]. Furthermore [i1] is no longer its own seed and cannot be found
     via the feature map *)
  assert (not export || is_interface_check ft);
  assert (i0 < count ft);
  assert (i1 < count ft);
  assert (cls = (descriptor i1 ft).cls);
  let bdesc0 = base_descriptor i0 ft
  and bdesc1 = base_descriptor i1 ft
  in
  bdesc1.seeds  <- IntSet.remove i1 bdesc1.seeds;
  bdesc1.is_inh <- true;
  IntSet.iter
    (fun i_seed -> (* add variant to seed and seed to variant*)
      let bdesc_seed = base_descriptor i_seed ft in
      assert (not (IntMap.mem cls bdesc_seed.variants) ||
              IntMap.find cls bdesc_seed.variants = i1);
      bdesc_seed.variants <- IntMap.add cls i1 bdesc_seed.variants;
      bdesc1.seeds        <- IntSet.add i_seed bdesc1.seeds;
      update_equality i_seed bdesc1 ft
    )
    bdesc0.seeds;
  if not export && is_public ft then begin (* do the same for the private view *)
    let bdesc0 = base_descriptor_priv i0 ft
    and bdesc1 = base_descriptor_priv i1 ft
    in
    bdesc1.seeds  <- IntSet.remove i1 bdesc1.seeds;
    bdesc1.is_inh <- true;
    IntSet.iter
      (fun i_seed -> (* add variant to seed and seed to variant*)
        let bdesc_seed = base_descriptor_priv i_seed ft in
        assert (not (IntMap.mem cls bdesc_seed.variants) ||
        IntMap.find cls bdesc_seed.variants = i1);
        bdesc_seed.variants <- IntMap.add cls i1 bdesc_seed.variants;
        bdesc1.seeds        <- IntSet.add i_seed bdesc1.seeds;
        update_equality i_seed bdesc1 ft
      )
      bdesc0.seeds;
  end;
  let fn  = (descriptor i1 ft).fname in
  let tab = Feature_map.find fn ft.map in
  Term_table2.remove i1 tab






let inherit_new_effective (i:int) (cls:int) (ghost:bool) (ft:t): int =
  let desc = descriptor i ft in
  let ctp,tvs = Class_table.class_type cls ft.ct
  and anchor  = anchor i ft (*desc.anchored.(0)*) in
  assert (anchor <> -1);
  let ntvs    = Tvars.count_all tvs
  and ntvs_i  = Tvars.count_all desc.tvs
  in
  let tvs1 = Tvars.insert_fgs desc.tvs anchor tvs in
  let ctp  = Term.upbound (ntvs_i-anchor) ntvs ctp in
  let ctp  = Term.up anchor ctp in
  let tvs1 = Tvars.update_fg (anchor+ntvs) ctp tvs1 in
  let f_tp(tp:type_term): type_term =
    Term.upbound ntvs anchor tp
  in
  let cnt = count ft
  and nargs = Array.length desc.argnames
  in
  let spec = variant_spec i cnt desc.cls cls ft in
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    if is_public ft then Some (standard_bdesc cnt cls spec nargs ft)
    else None
  and sign = Sign.map f_tp desc.sign
  in
  let sign = if ghost then Sign.to_ghost sign else sign in
  let anchor_fg, anchor_cls = Sign.anchor tvs1 sign in
  Seq.push
    {mdl       = Class_table.current_module ft.ct;
     fname     = desc.fname;
     cls       = cls;
     anchor_cls = anchor_cls;
     anchor_fg  = anchor_fg;
     impl      = desc.impl;
     tvs       = tvs1;
     anchored  = Array.make 1 (anchor+ntvs);
     argnames  = desc.argnames;
     sign      = sign;
     tp        = f_tp desc.tp;
     priv      = bdesc;
     pub       = bdesc_opt
   } ft.seq;
  add_class_feature cnt false false false ft;
  inherit_feature i cnt cls false ft;
  cnt





let add_function
    (fn:       feature_name withinfo)
    (tvs:      Tvars.t)
    (argnames: int array)
    (sign:     Sign.t)
    (body:     Feature.body)
    (ft:       t): unit =
  assert (not (has_with_signature fn.v tvs sign ft));
  let is_priv = is_private ft
  and cnt     = Seq.count ft.seq
  and nargs   = Array.length argnames
  and spec,impl = body
  in
  let ghost_required =
    Feature.Spec.has_postconditions spec ||
    match Feature.Spec.definition spec with
      Some t when is_ghost_term t nargs ft -> true
    | _ -> false
  in
  if ghost_required && not (Sign.is_ghost sign) then
      error_info fn.i "Must be a ghost function";
  let mdl = Class_table.current_module ft.ct in
  let cls = Class_table.owner tvs sign ft.ct
  and anchor_fg, anchor_cls = Sign.anchor tvs sign in
  let anchored = Class_table.anchored tvs cls ft.ct in
  let nanchors = Array.length anchored in
  begin match impl with
    Feature.Deferred ->
      Class_table.check_deferred cls nanchors fn.i ft.ct
  | _ -> ()
  end;
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    if is_priv then None else Some (standard_bdesc cnt cls spec nargs ft)
  and nfgs = Tvars.count_all tvs
  and base = (is_private ft || is_interface_use ft) &&
    not (Feature.Spec.has_definition spec)
  in
  let desc =
    {mdl      = mdl;
     cls      = cls;
     anchor_cls = anchor_cls;
     anchor_fg  = anchor_fg;
     fname    = fn.v;
     impl     = impl;
     tvs      = tvs;
     argnames = argnames;
     sign     = sign;
     tp       = Class_table.to_dummy nfgs sign;
     anchored = anchored;
     priv     = bdesc;
     pub      = bdesc_opt}
  in
  Seq.push desc ft.seq;
  add_key cnt ft;
  add_class_feature cnt false false base ft



let update_function
    (idx: int)
    (info:info)
    (is_ghost: bool)
    ((spec,impl):  Feature.body)
    (ft:       t): unit =
  let desc    = descriptor idx ft
  and mdl     = Class_table.current_module ft.ct
  and is_priv = is_private ft
  in
  let not_match str =
    let str = "The " ^ str ^ " of \""
      ^ (feature_name_to_string desc.fname)
      ^ "\" does not match the previous definition"
    in
    error_info info str
  in
  desc.mdl <- mdl;
  if is_priv then begin
    if impl <> desc.impl then
      not_match "implementation status";
    if not (Feature.Spec.equivalent spec desc.priv.spec) then
      not_match "private definition"
  end else begin
    let def_opt = Feature.Spec.definition spec
    and def_priv_opt = Feature.Spec.definition desc.priv.spec in
    if Option.has def_opt && def_opt <> def_priv_opt then
      not_match "public definition";
    match desc.pub with
      None ->
        if Sign.is_ghost desc.sign && not is_ghost then
          error_info info "Must be a ghost function";
        let nargs = Array.length desc.argnames in
        desc.pub <- Some (standard_bdesc idx desc.cls spec nargs ft);
        add_class_feature idx false true false ft
    | Some bdesc ->
        let def_opt = Feature.Spec.definition spec
        and def_bdesc_opt = Feature.Spec.definition bdesc.spec in
        if def_bdesc_opt <> def_opt then
          not_match "public definition"
  end








let has_current_module (ft:t): bool =
  Class_table.has_current_module ft.ct

let current_module (ft:t): int =
  Class_table.current_module ft.ct

let count_modules (ft:t): int =
  Class_table.count_modules ft.ct

let used_modules (mdl:int) (ft:t): IntSet.t =
  Class_table.used_modules mdl ft.ct

let find_module (name:int*int list)  (ft:t): int =
  Class_table.find_module name ft.ct

let module_name (mdl:int) (ft:t): string = Class_table.module_name mdl ft.ct


let add_base_features (mdl_name:int) (ft:t): unit =
  try
    let lst = IntMap.find mdl_name ft.base in
    let curr_mdl = current_module ft in
    List.iter
      (fun idx ->
        let desc = descriptor idx ft in
        let base = not (Feature.Spec.has_definition desc.priv.spec) in
        assert (desc.mdl = -1);
        desc.mdl <- curr_mdl;
        add_key idx ft;
        add_class_feature idx true false base ft)
      !lst
  with Not_found ->
    ()




let add_used_module (name:int*int list) (used:IntSet.t) (ft:t): unit =
  Class_table.add_used_module name used ft.ct;
  add_base_features (fst name) ft




let add_current_module (name:int) (used:IntSet.t) (ft:t): unit =
  Class_table.add_current_module name used ft.ct;
  add_base_features name ft;
  if name <> ST.symbol "boolean" then begin
    let or_desc  = descriptor or_index ft
    and and_desc = descriptor and_index ft in
    or_desc.priv.spec   <- Feature.Spec.make_func_def or_desc.argnames  None [];
    and_desc.priv.spec  <- Feature.Spec.make_func_def and_desc.argnames None []
  end



let set_interface_check (used:IntSet.t) (ft:t): unit =
  Class_table.set_interface_check used ft.ct;
  ft.map <- Feature_map.empty;
  let mdl = current_module ft in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if desc.mdl = mdl || IntSet.mem desc.mdl used then
      match desc.pub with
        Some bdesc ->
          assert (not (IntSet.is_empty bdesc.seeds));
          if not bdesc.is_inh then
            add_key i ft
      | None ->
          if desc.mdl = mdl then add_key i ft
  done

let check_interface (ft:t): unit =
  assert (is_interface_check ft);
  let mt = module_table ft in
  let curr = Module_table.current mt in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if curr = desc.mdl
        && is_desc_deferred desc
        && not (Option.has desc.pub)
        && Class_table.is_class_public desc.cls ft.ct then
      error_info (FINFO (1,0))
        ("deferred feature `" ^ (string_of_signature i ft) ^
         "' is not public")
  done
