(* Copyright (C) 2015 Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Signature
open Printf

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


let false_constant (nb:int): term =
  let id = nb+false_index in
  VAppl (id,[||],[||])

let true_constant (nb:int): term =
  let id = nb+true_index in
  VAppl (id,[||],[||])


type definition = term

type formal     = int * term


class bdesc (idx:int) (nfgs:int) (cls:int) (spec:Feature.Spec.t) =
  object (self:'self)
    val mutable is_inh = false
    val mutable is_exp = false
    val mutable spec = spec
    val mutable sd = idx                    (* each new feature is its own seed *)
    val mutable subst = standard_substitution nfgs
    val mutable vars = IntMap.singleton cls idx  (* and own variant *)
    val mutable is_eq = (idx = eq_index)
    val mutable inv_ass = IntSet.empty

    method is_inherited:bool = is_inh
    method is_exported:bool = is_exp
    method seed:int = sd
    method ags:agens = subst
    method specification:Feature.Spec.t = spec
    method variant (cls:int): int = IntMap.find cls vars
    method has_variant (cls:int): bool =
      IntMap.mem cls vars
    method variants: int IntMap.t = vars
    method is_equality: bool = is_eq
    method involved_assertions: IntSet.t = inv_ass
    method set_specification (sp:Feature.Spec.t): unit =
      spec <- sp
    method set_seed (s:int) (ags:agens):unit =
      sd <- s;
      subst <- ags;
      if sd = eq_index then
        is_eq <- true
    method add_variant (cls:int) (idx:int): unit =
      assert (not (IntMap.mem cls vars));
      vars <- IntMap.add cls idx vars
    method set_inherited: unit =
      is_inh <- true
    method set_exported: unit =
      is_exp <- true
    method add_assertion (i:int): unit =
      inv_ass <- IntSet.add i inv_ass
  end

type descriptor = {
    mutable mdl: int;             (* -1: base feature, module not yet assigned*)
    mutable cls: int;             (* owner class *)
    anchor_cls:  int;
    anchor_fg:   int;
    fname:       feature_name;
    impl:        Feature.implementation;
    tvs:         Tvars.t;         (* only formal generics *)
    mutable anchored: int array;  (* formal generics anchored to the owner class *)
    argnames:    names;
    sign:        Sign.t;
    mutable tp:  type_term;
    bdesc:       bdesc;
  }

type t = {
    mutable map: Term_table.t ref Feature_map.t; (* search table *)
    seq:         descriptor seq;
    mutable base:int list ref IntMap.t; (* module name -> list of features *)
    ct:          Class_table.t;
    verbosity:   int
  }



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


let count (ft:t): int =
  Seq.count ft.seq


let verbosity (ft:t): int = ft.verbosity

let descriptor (i:int) (ft:t): descriptor =
  assert (i < count ft);
  Seq.elem i ft.seq


let tvars (i:int) (ft:t): Tvars.t =
  (descriptor i ft).tvs

let signature0 (i:int) (ft:t): Tvars.t * Sign.t =
  let desc = descriptor i ft in
  desc.tvs, desc.sign


let argument_types (i:int) (ags:agens) (ntvs:int) (ft:t): types =
  let tvs,s = signature0 i ft in
  let tps = Sign.arguments s in
  Term.subst_array tps ntvs ags


let result_type (i:int) (ags:agens) (ntvs:int) (ft:t): type_term =
  let tvs,s = signature0 i ft in
  assert (Sign.has_result s);
  let rt = Sign.result s in
  Term.subst rt ntvs ags


let signature (i:int) (ags:agens) (ntvs:int) (ft:t): Sign.t =
  (* The signature of the feature [i] where the formal generics are substituted
     by the actual generics [ags] coming from a type environment with [ntvs]
     type variables. *)
  let argtps = argument_types i ags ntvs ft
  and rtp    = result_type i ags ntvs ft in
  Sign.make_func argtps rtp


let argument_names (i:int) (ft:t): int array =
  (descriptor i ft).argnames

let class_of_feature (i:int) (ft:t): int =
  (descriptor i ft).cls


let arity (i:int) (ft:t): int =
  Sign.arity (descriptor i ft).sign


let is_higher_order (i:int) (ft:t): bool =
  let desc = descriptor i ft in
  assert (Sign.has_result desc.sign);
  let ntvs = Tvars.count_all desc.tvs in
  let cls,_ = Class_table.split_type_term (Sign.result desc.sign) in
  assert (ntvs <= cls);
  let cls = cls - ntvs in
  cls = Class_table.predicate_index || cls = Class_table.function_index


let tuple_arity (i:int) (ft:t): int =
  assert (is_higher_order i ft);
  let desc = descriptor i ft in
  assert (Sign.has_result desc.sign);
  let ntvs = Tvars.count_all desc.tvs in
  let _,args = Class_table.split_type_term (Sign.result desc.sign) in
  assert (Array.length args = 1);
  let args = Class_table.extract_from_tuple_max ntvs args.(0) in
  Array.length args



let string_of_signature (i:int) (ft:t): string =
  let desc = descriptor i ft in
  (feature_name_to_string desc.fname) ^ " " ^
  (Class_table.string_of_complete_signature desc.sign desc.tvs ft.ct)


let is_feature_public (i:int) (ft:t): bool =
  assert (i < count ft);
  is_private ft ||
  let desc = descriptor i ft in
  (desc.mdl = current_module ft && desc.bdesc#is_exported) ||
  (desc.mdl <> current_module ft &&
   Module_table.is_visible desc.mdl (module_table ft))


let feature_name (i:int) (ft:t): string =
  let desc = descriptor i ft in
  feature_name_to_string desc.fname


let base_descriptor (i:int) (ft:t): bdesc =
  assert (i < count ft);
  (descriptor i ft).bdesc




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


let prepend_names (nms:int array) (names:int array): int array =
  let nms = adapt_names nms names in
  Array.append nms names



let is_constructor (i:int) (ft:t): bool =
  assert (i < count ft);
  let desc = descriptor i ft in
  assert (desc.cls <> -1);
  IntSet.mem i (Class_table.constructors desc.cls ft.ct)



let inductive_arguments (i:int) (ft:t): int list =
  (* Reversed list of inductive arguments *)
  assert (is_constructor i ft);
  let desc = descriptor i ft in
  let ntvs = Tvars.count_all desc.tvs in
  let lst = interval_fold
      (fun lst i ->
        match Sign.arg_type i desc.sign with
          Variable cls when cls = desc.cls + ntvs ->
            i :: lst
        | VAppl(cls,_,_) when cls = desc.cls + ntvs ->
            i :: lst
        | _ ->
            lst)
      []
      0 (Sign.arity desc.sign) in
  List.rev lst



let feature_call(i:int) (nb:int) (args:arguments) (ags:agens) (ft:t): term =
  (* Construct the term [f(a,b,...)] for the feature [i] for an environment
     with [nb] variables.*)
  let len = Array.length args in
  assert (arity i ft = len);
  VAppl (i+nb, args, ags)


let constructor_rule (idx:int) (p:term) (ags:agens) (nb:int) (ft:t)
    : int * names * types * term list * term =
  (* Construct the rule for the constructor [idx] where the constructor [idx] has
     the form [c(a1,a2,...)] where [ar1,ar2,...] are recursive.

         all(args) p(ar1) ==> p(ar2) ==> ... ==> p(c(a1,a2,...))

     [p] is the predicate term which expects objects of the inductive type
     belonging to the constructor [i] and [ags] are the actual generics substituted
     for the formal generics of the inductive type.
   *)
  let desc = descriptor idx ft in
  let tps = Sign.arguments desc.sign
  in
  let n       = arity idx ft in
  let nms     = anon_argnames n in
  let p       = Term.up n p in
  let call    = VAppl (idx+n+nb, standard_substitution n, ags) in
  let tgt     = Application(p,[|call|],true) in
  let indargs = inductive_arguments idx ft in
  let ps_rev  =
    List.rev_map
      (fun iarg -> Application(p,[|Variable iarg|],true)) indargs in
  n,nms,tps,ps_rev,tgt



let induction_law (cls:int) (nb:int) (ft:t): term =
  (* Construct the induction law

     all(p,x) ind1 ==> ... ==> indn ==> p(x)
   *)
  assert (nb = 0); (* global only *)
  assert (Class_table.has_constructors cls ft.ct);
  let cons = Class_table.constructors cls ft.ct
  and tp,tvs = Class_table.class_type cls ft.ct
  and imp_id = nb + 2 + implication_index
  and p  = Variable 0
  and x  = Variable 1
  in
  let fgnms,fgcon = Tvars.fgnames tvs, Tvars.fgconcepts tvs
  and nms = [|ST.symbol "p"; ST.symbol "x"|]
  and tps = [|Class_table.predicate_type tp (Tvars.count_all tvs); tp|] in
  let lst = List.rev (IntSet.elements cons) in
  let t0 =
    List.fold_left
      (fun tgt idx ->
        let rule =
          let ags = Array.init (Array.length fgcon) (fun i -> Variable i) in
          let n,nms,tps,ps_rev,tgt = constructor_rule idx p ags (nb+2) ft in
          let chn  = Term.make_implication_chain ps_rev tgt (n+imp_id) in
          Term.all_quantified n (nms,tps) empty_formals chn in
        let rule = Term.prenex rule (2+nb) (Tvars.count_fgs tvs) imp_id in
        Term.binary imp_id rule tgt)
      (Application(p,[|x|],true))
      lst in
  Term.all_quantified 2 (nms,tps) (fgnms,fgcon) t0



let is_term_public (t:term) (nbenv:int) (ft:t): bool =
  let rec check_pub t nb =
    let check_pub_i i =
      let i = i - nb in
      assert (i < count ft);
      if not (is_feature_public i ft) then
        raise Not_found
      else
        ()
    and check_args args nb = Array.iter (fun t -> check_pub t nb) args
    and check_lst  lst nb  = List.iter  (fun t -> check_pub t nb) lst
    in
    match t with
      Variable i when i < nb ->
        ()
    | Variable i ->
        check_pub_i i
    | VAppl(i,args,_) ->
        check_pub_i i;
        check_args args nb
    | Application(f,args,_) ->
        check_pub f nb;
        check_args args nb
    | Lam(n,nms,pres0,t0,_,_) ->
        check_lst pres0 (1+nb);
        check_pub t0 (1+nb)
    | QExp(n,_,_,t0,_) ->
        check_pub t0 (n+nb)
    | Flow (ctrl,args) ->
        check_args args nb
    | Indset (nme,tp,rs) ->
        check_args rs (1+nb)
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
    and vappl i t ags  = VAppl (i+nargs-1, [|t|], ags), 0, 0
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
    | VAppl(i,args,ags) when i = first_id ->
        assert (Array.length args = 1);
        let t,outer,nsnds = untup args.(0) nb 1 0 in
        assert (outer = 0 || outer = 1);
        assert (nsnds = 0);
        if outer = 1 then
          t, 0, 0
        else
          vappl i t ags
    | VAppl(i,args,ags) when i = second_id && outer = 0 ->
        assert (Array.length args = 1);
        let t,outer,nsnds = untup args.(0) nb 2 0 in
        assert (outer = 0 || outer = 2);
        assert (nsnds = 0);
        if outer = 2 then
          t, 0, 0
        else
          vappl i t ags
    | VAppl(i,args,ags) when i = second_id->
        assert (Array.length args = 1);
        assert (outer = 1 || outer = 2);
        let t1,outer1,nsnds1 = untup args.(0) nb outer (nsnds+1) in
        if outer1 = 0 || nsnds1 = 0 then
          vappl i t1 ags
        else begin
          assert (outer1 = outer);
          t1, outer1, nsnds1-1
        end
    | VAppl(i,args,ags) ->
        let args = Array.map (fun t -> untup0 t nb) args in
        VAppl(i+nargs-1,args,ags), 0, 0
    | Application(f,args,pr) ->
        let f = untup0 f nb
        and args = Array.map (fun t -> untup0 t nb) args in
        Application(f,args,pr), 0, 0
    | Lam (n,nms,pres0,t0,pr,tp) ->
        let t0 = untup0 t0 (1+nb)
        and pres0 = untup0_lst pres0 (1+nb) in
        Lam(n,nms,pres0,t0,pr,tp), 0, 0
    | QExp (n,tps,fgs,t0,is_all) ->
        let t0 = untup0 t0 (n+nb) in
        QExp(n,tps,fgs,t0,is_all), 0, 0
    | Flow (ctrl,args) ->
        Flow (ctrl, Array.map (fun t -> untup0 t nb) args), 0, 0
    | Indset (nme,tp,rs) ->
        let rs = Array.map (fun r -> untup0 r (1+nb)) rs in
        Indset (nme,tp,rs), 0, 0
  and untup0 t nb =
    let t,_,_ = untup t nb 0 0 in t
  and untup0_lst lst nb =
    List.map (fun t -> untup0 t nb) lst
  in
  if nargs <= 1 then
      t
  else begin
    untup0 t 0
  end


(*
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
    | Flow (ctrl,args) ->
        Flow (ctrl, reduce_args args)
    | Indset (n,nms,rs) ->
        assert false (* nyi *)
  in
  reduce tlam 0
*)


let args_of_tuple (t:term) (nbenv:int) (ft:t): term array =
  (* The tuple (a,b,...) transformed into an argument array [a,b,...].
   *)
  let tuple_id  = nbenv + tuple_index in
  let rec collect t lst =
    match t with
      VAppl (i,args,_) when i = tuple_id ->
        assert (Array.length args = 2);
        let lst = args.(0) :: lst in
        collect args.(1) lst
    | _ ->
        t :: lst
  in
  let lst = collect t [] in
  Array.of_list (List.rev lst)


let ith_tuple_element
     (i:int) (n:int) (t:term) (tup_tp:type_term) (nvars:int) (ft:t)
    : term =
  (* The [i]th of [n] tuple elements of term [t] which has the tuple type
     [tup_tp] and comes from an enviroment with [nvars] variables.

     Example: Tuple elements of a 4-tuple:

          0: t.first
          1: t.second.first
          2: t.second.second.first
          3: t.second.second.second

          i + 1 < n:  i times second + first
          i + 1 = n:  i times second
   *)
  let first_id  = nvars + first_index
  and second_id = nvars + second_index
  in
  let elem (i:int) (tp:type_term): term =
    let split_tup (tp:type_term): agens =
      let _,ags = Class_table.split_type_term tp in
      assert (Array.length ags = 2);
      ags
    in
    let rec seconds (m:int) (t:term) (tp:type_term): term * type_term =
      assert (0 <= m);
      if m = 0 then
        t, tp
      else
        let ags = split_tup tp in
        let t = VAppl (second_id, [|t|], ags) in
        seconds (m - 1) t ags.(1)
    in
    if i + 1 < n then
      let t, tp = seconds i t tup_tp in
      let ags = split_tup tp in
      VAppl (first_id, [|t|], ags)
    else if i + 1 = n then
      let t,_ = seconds i t tup_tp in
      t
    else
      assert false (* cannot happen *)
  in
  elem i tup_tp


let args_of_tuple_ext
    (t:term) (tp:type_term) (nvars:int) (nargs:int) (ft:t)
    : term array =
  (* The tuple [t = (a,b,...,z)] with type [tp] transformed into an argument
     array [a,b,...].

     If the tuple [t] is only an n-tuple and [nargs]
     arguments are needed with [n < nargs] the last tuple element [z] is used
     to generated the missing elements as

         z.first,  z.second.first, z.second...first, z.second...second
   *)

  assert (0 < nargs);
  let tuple_id  = nvars + tuple_index
  in
  let rec untup
      (t:term) (tp:type_term) (n:int) (lst:term list)
      : int * term list * type_term =
    assert (n < nargs);
    if n + 1 = nargs then
      n + 1, t::lst, tp
    else
      match t with
        VAppl(i,args,ags) when i = tuple_id ->
          assert (Array.length args = 2);
          assert (Array.length ags  = 2);
          untup args.(1) ags.(1) (n+1) (args.(0)::lst)
      | _ ->
          n + 1, t::lst, tp
  in
  let n, lst_rev, tp_last = untup t tp 0 []
  in
  let lst_rev =
    if n < nargs then begin
      match lst_rev with
        [] ->
          assert false
      | last::tail ->
          let delta = nargs - n + 1 in
          let rec add_args_from i lst_rev =
            if i = delta then
              lst_rev
            else
              add_args_from
                (i + 1)
                ((ith_tuple_element i delta last tp_last nvars ft) :: lst_rev)
          in
          add_args_from 0 tail
    end else
      lst_rev
  in
  assert (List.length lst_rev = nargs);
  Array.of_list (List.rev lst_rev)



let tuple_of_args
    (args:arguments) (tup_tp:type_term) (nb:int) (ft:t)
    : term =
  (* The arguments [a,b,...] transformed to a tuple (a,b,...) or the type [tup_tp].
   *)
  let nargs = Array.length args
  and tup_id = nb + tuple_index
  in
  assert (0 < nargs);
  let rec tup_from (i:int) (tup_tp:type_term): term =
    if i = nargs - 1 then
      args.(i)
    else begin
      assert (i + 2 <= nargs);
      let _,ags = Class_table.split_type_term tup_tp in
      assert (Array.length ags = 2);
      let b = tup_from (i + 1) ags.(1) in
      VAppl (tup_id, [| args.(i); b |], ags)
    end
  in
  tup_from 0 tup_tp








let add_tuple_accessors
    (t:term) (nargs:int) (tup_tp:type_term) (nbenv:int) (ft:t)
    : term =
  (* Convert the inner term [t] which has [nargs] arguments below [nbenv] variables
     to a term with one argument expecting an [nargs] tuple.

     nargs = 4
     args: [0.first, 0.second.first, 0.second.second.first, 0.second.second.second]
   *)
  let res =
  if nargs <= 1 then
    t
  else
    let args =
      args_of_tuple_ext (Variable 0) tup_tp (nbenv+1) nargs ft in
    Term.subst t 1 args
  in
  assert (remove_tuple_accessors res nargs nbenv ft = t);
  res


let make_lambda
    (n:int) (nms:int array) (pres:term list) (t:term)
    (pr:bool) (nbenv:int) (tp:type_term) (ft:t)
    : term =
  assert (0 < n);
  assert (Array.length nms = 0 || Array.length nms = n);
  let tup_tp = Class_table.domain_type tp in
  let add_tup t = add_tuple_accessors t n tup_tp nbenv ft
  in
  let t0 = add_tup t
  and pres0 = List.map add_tup pres in
  Lam(n,nms,pres0,t0,pr,tp)



let make_application
    (f:term) (args:term array) (tup:type_term) (pred:bool) (nbenv:int) (ft:t)
    : term =
  assert (Array.length args > 0);
  let args =
    if Array.length args = 1 then
      args
    else
      [|tuple_of_args args tup nbenv ft|]
  in
  Application (f, args, pred)



let beta_reduce
    (n:int) (tlam: term) (tp:type_term) (args:term array) (nbenv:int) (ft:t)
    : term =
  (* Beta reduce the expression ((x,y,...)->tlam)(args). The expression comes from
     an environment with [nbenv] variables. The expression is normalized i.e. fully
     tupelized i.e. it has one argument which is an [n] tuple.

     [tp] is the type of the lambda term.
   *)
  assert (0 < Array.length args);
  assert (Array.length args <= n);
  assert (Array.length args = 1);
  let t0   = remove_tuple_accessors tlam n nbenv ft
  and tup_tp = Class_table.domain_type tp
  in
  let args = args_of_tuple_ext args.(0) tup_tp nbenv n ft in
  Term.apply t0 args




let fake_tuple_type (n:int): type_term =
  assert (1 <= n);
  let rec tup i tp =
    if i = 0 then
      tp
    else
      let tp = VAppl (-1, [|empty_term; tp|], [||]) in
      tup (i - 1) tp
  in
  tup (n - 1) empty_term




let term_to_string
    (t:term)
    (norm:bool)
    (long:bool)
    (nanon: int)
    (names: int array)
    (tvs: Tvars.t)
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
      (tvs:Tvars.t)
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
    let find_op_int (i:int): operator * int=
      if nnames <= i then
        let idx = i - nnames in
        match (Seq.elem idx ft.seq).fname with
          FNoperator op -> op, idx
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
    and find_op (f:term): operator * int =
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
      String.concat ";"
        (List.map (fun t -> to_string t names nanonused tvs false None) ps),
      to_string t names nanonused tvs false None
    in
    let default_fapp (f:term) (argsstr:string): operator option * string =
      None,
      (to_string f names nanonused tvs true None) ^ "(" ^ argsstr ^ ")"
    in
    let funiapp2str (i:int) (argsstr:string): operator option * string =
      if nnames <= i then
        let fn = (descriptor (i-nnames) ft).fname in
        begin match fn with
          FNname fsym ->
            if fsym = (ST.symbol "singleton") then
              None, "{" ^ argsstr ^ "}"
            else if fsym = ST.tuple then
              Some Commaop, argsstr
            else
              default_fapp (Variable i) argsstr
        | _ -> default_fapp (Variable i) argsstr
        end
      else
        default_fapp (Variable i) argsstr
    in
    let funapp2str (f:term) (argsstr:string): operator option * string =
      match f with
        Variable i ->
          funiapp2str i argsstr
      | _ -> default_fapp f argsstr
    in
    let argsstr (args: term array): string =
      String.concat
        ","
        (List.map
           (fun t -> to_string t names nanonused tvs false None)
           (Array.to_list args))
    in
    let op2str (op:operator) (fidx:int) (args: term array): string =
      match op with
        Allop | Someop | Asop -> assert false (* cannot happen *)
      | _ ->
          let nargs = Array.length args in
          if nargs = 1 && arity fidx ft = 0 then begin
            assert (is_higher_order fidx ft);
            let nargs_tup = tuple_arity fidx ft in
            assert (1 <= nargs_tup);
            if nargs_tup = 1 then
              "(" ^ (operator_to_rawstring op) ^ ")"
              ^ (to_string args.(0) names nanonused tvs false (Some (op,false)))
            else
              let tup_tp = fake_tuple_type nnames in
              let args = args_of_tuple_ext args.(0) tup_tp nnames 2 ft in
              (to_string args.(0) names nanonused tvs false (Some (op,true)))
              ^ " " ^ (operator_to_rawstring op) ^ " "
              ^ (to_string args.(1) names nanonused tvs false (Some (op,false)))
          end else if nargs = 1 then
            (operator_to_rawstring op) ^ " "
            ^ (to_string args.(0) names nanonused tvs false (Some (op,false)))
          else begin
            assert (nargs=2); (* only unary and binary operators *)
            (to_string args.(0) names nanonused tvs false (Some (op,true)))
            ^ " " ^ (operator_to_rawstring op) ^ " "
            ^ (to_string args.(1) names nanonused tvs false (Some (op,false)))
          end
    and lam2str (n:int) (nms: int array) (pres:term list) (t:term) (pr:bool)
        : string =
      let argsstr, presstr, tstr = lam_strs n nms pres t in
      if pr then
        "{" ^ argsstr ^ ": " ^ tstr ^ "}"
      else
        match pres with
          [] -> "((" ^ argsstr ^ ") -> " ^ tstr ^ ")"
        | _ -> "agent (" ^ argsstr ^ ") require " ^
            presstr ^
            " ensure -> " ^ tstr ^ " end"
    and if2str (args:term array): string =
      let len = Array.length args in
      assert(2 <= len); assert (len <= 3);
      let to_str t = to_string t names nanonused tvs false None in
      let cond_exp (c:term) (e:term) (isif:bool): string =
        (if isif then "if " else " elseif ") ^ (to_str c) ^ " then " ^ (to_str e)
      in
      let rec ifrest (t:term): string =
        match t with
          Flow (Ifexp,args) -> ifargs args false
        | _                 -> " else " ^ (to_str t)
      and ifargs (args: term array) (is_outer:bool): string =
        let len = Array.length args in
        assert(2 <= len); assert (len <= 3);
        (cond_exp args.(0) args.(1) true) ^
        (if len = 2 then "" else ifrest args.(2)) ^
        (if is_outer then " end" else "")
      in
      ifargs args true
    and insp2str (args:term array): string =
      let len = Array.length args in
      assert (len mod 2 = 1);
      assert (3 <= len);
      let ncases = len / 2 in
      let case (i:int): string =
        let n, (nms,_), mtch, res = Term.case_split args.(2*i+1) args.(2*i+2) in
        let names1 = Array.append nms names in
        let to_str t = to_string t names1 nanonused tvs false None in
        " case " ^ (to_str mtch) ^ " then " ^ (to_str res)
      in
      let rec cases_from (i:int) (str:string): string =
        if i = ncases then
          str
        else
          (cases_from (1+i) (str ^ (case i))) in
      let to_str t = to_string t names nanonused tvs false None in
      "inspect "  ^  (to_str args.(0)) ^ (cases_from 0 "") ^ " end"
    and as2str (args:term array): string =
      let len = Array.length args in
      assert (len = 2);
      let str1 = to_string args.(0) names nanonused tvs false (Some (Asop,true)) in
      let str2 =
        let n,(nms,_),mtch = Term.pattern_split args.(1) in
        let names1 = Array.append nms names in
        to_string mtch names1 nanonused tvs false (Some (Asop,false)) in
      str1 ^ " as " ^ str2
    in
    let inop, str =
      match t with
        Variable i ->
          None, var2str i
      | VAppl (i,args,_) ->
          if Array.length args = 0 then
            None, var2str i
          else
            begin try
              let op,fidx = find_op_int i in
              Some op, op2str op fidx args
            with Not_found ->
              funiapp2str i (argsstr args)
            end
      | Application (f,args,pr) ->
          begin
            try
              let op,fidx = find_op f in
              Some op, op2str op fidx args
            with Not_found ->
              funapp2str f (argsstr args)
          end
      | Lam (n,nms,pres,t,pr,_) ->
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
      | QExp (n,(nms,tps),(fgnms,fgcon),t,is_all) ->
          let nms = adapt_names nms names in
          let op, opstr  = if is_all then Allop, "all"  else Someop, "some"
          in
          if not long && nanonused + Array.length names <> 0 then
            let argsstr, _, tstr = lam_strs n nms [] t in
            Some op, opstr ^ "(" ^ argsstr ^ ") " ^ tstr
          else begin
            let names = Array.append nms names in
            let tvs1 = Tvars.make_fgs fgnms fgcon in
            if not (Tvars.is_empty tvs || Tvars.is_empty tvs1) then begin
              printf "tvs1  %s\n" (Class_table.string_of_tvs tvs1 ft.ct);
              printf "tvs   %s\n" (Class_table.string_of_tvs tvs  ft.ct);
            end;
            assert (Tvars.is_empty tvs || Tvars.is_empty tvs1);
            let tvs = if Tvars.is_empty tvs then tvs1 else tvs in
            let argsstr = Class_table.arguments_string2 tvs nms tps ft.ct
            and tvsstr  = Class_table.string_of_tvs tvs1 ft.ct
            and tstr = to_string t names nanonused tvs false None in
            Some op, opstr ^ tvsstr ^ argsstr ^ " " ^ tstr
          end
      | Flow (ctrl,args) ->
          begin
            match ctrl with
              Ifexp   -> None, if2str args
            | Inspect -> None, insp2str args
            | Asexp   -> Some(Asop), as2str args
          end
      | Indset (nme,tp,rs) ->
          let n,nms = 1, [|nme|] in
          let nms = adapt_names nms names in
          let argsstr = args2str n nms in
          let nanonused, nms = local_names n nms in
          let names = Array.append nms names in
          let rsstrs =
            List.map (fun t -> to_string t names nanonused tvs false None)
              (Array.to_list rs) in
          let rsstr = String.concat "," rsstrs in
          let str = "{(" ^ argsstr ^ "):"
            ^  rsstr ^ "}" in
          None, str
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
  to_string t names nanon tvs false None


let string_of_term_anon (t:term) (nb:int) (ft:t): string =
  term_to_string t true false nb [||] (Tvars.empty) ft

let string_long_of_term_anon (t:term) (nb:int) (tvs:Tvars.t) (ft:t): string =
  term_to_string t true true nb [||] tvs ft




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


let seed (i:int) (ft:t): int =
  assert (i < count ft);
  (base_descriptor i ft)#seed






let variant (i:int) (cls:int) (ft:t): int =
  (* The variant of the feature [i] in the class [cls] *)
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  let seed_bdesc = base_descriptor bdesc#seed ft
  in
  seed_bdesc#variant cls



let has_variant (i:int) (cls:int) (ft:t): bool =
  try
    ignore(variant i cls ft);
    true
  with
    Not_found -> false



let unify_types
    (tp1:type_term) (nfgs:int) (tp2:type_term) (nall:int) (ags:agens): unit =
  (* unify the type [tp1] which has [nfgs] formal generics with the
     corresponding type [tp2] coming from an environment with [nall] type
     variables and accumulate the substitutions into [ags].  *)
  assert (nfgs = Array.length ags);
  let rec uni tp1 tp2 =
    match tp1, tp2 with
      Variable i, _ when i < nfgs ->
        if ags.(i) = empty_term then
          ags.(i) <- tp2
        else
          assert (ags.(i) = tp2)
    | Variable i, Variable j ->
        assert (nall <= j);
        assert (i-nfgs = j-nall)
    | VAppl(i1,args1,_), VAppl(i2,args2,_) ->
        let len = Array.length args1 in
        if len <> Array.length args2 then
          raise Not_found;
        if i1-nfgs <> i2-nall then
          raise Not_found;
        assert (len = Array.length args2);
        assert (i1-nfgs = i2-nall);
        interval_iter (fun k -> uni args1.(k) args2.(k)) 0 len
    | _ ->
        raise Not_found
  in
  uni tp1 tp2


let unify_signatures
    (s1:Sign.t) (nfgs:int) (s2:Sign.t) (ags:agens) (nall:int): agens =
  (* Needed ???? *)
  let res_ags  = Array.make nfgs empty_term
  and len      = Sign.arity s1
  and subst tp = Term.subst tp nall ags in
  let uni tp1 tp2 = unify_types tp1 nfgs (subst tp2) nall res_ags in
  assert (len = Sign.arity s2);
  assert (Sign.has_result s1 = Sign.has_result s2);
  for k = 0 to len-1 do
    uni (Sign.arg_type k s1) (Sign.arg_type k s2)
  done;
  if Sign.has_result s1 then
    uni (Sign.result s1) (Sign.result s2);
  res_ags


let variant_generics
    (idx_var:int) (idx:int) (ags:agens) (ntvs:int) (ft:t): agens =
  (* [idx_var] is a variant of the feature [idx]. We consider a feature call
     of the form [VAppl(idx,_,ags)] where [ags] come from a type environment
     with [ntvs] type variables. The routine calculates the actual generics of
     the call of the variant feature [VAppl(idx_var,_,ags_var)].  *)
  let tvs_var,s_var = signature0 idx_var ft in
  let nfgs_var      = Tvars.count_fgs tvs_var in
  if nfgs_var = 0 then
    [||]
  else
    let subst tp    = Term.subst tp ntvs ags in
    let tvs0,s0     = signature0 idx ft in
    let len         = Sign.arity s0 in
    assert (len = Sign.arity s_var);
    let ags         = Array.make nfgs_var empty_term in
    let uni tp1 tp2 = unify_types tp1 nfgs_var (subst tp2) ntvs ags in
    for k = 0 to len-1 do
      uni (Sign.arg_type k s_var) (Sign.arg_type k s0)
    done;
    assert (Sign.has_result s_var = Sign.has_result s0);
    if Sign.has_result s0 then
      uni (Sign.result s_var) (Sign.result s0);
    ags



let variant_feature
    (i:int) (nb:int) (ags:type_term array) (tvs:Tvars.t) (ft:t): int*agens =
  (* The variant of the feature [i] in a context with [nb] variables where the
     formal generics are substituted by the actual generics [ags] which come from
     the type environment [tvs].
   *)
  assert (i < nb + count ft);
  let idx = i - nb in
  if Array.length ags <> count_fgs idx ft then begin
    printf "variant_feature %d %s\n" idx (string_of_signature idx ft);
    printf "#ags %d, count_fgs %d\n" (Array.length ags) (count_fgs idx ft);
  end;
  assert (Array.length ags = count_fgs idx ft);
  let nfgs = Array.length ags in
  if nfgs = 0 || nfgs > 1 then
    i,ags
  else begin
    let bdesc = base_descriptor idx ft in
    let sd,ags_sd = bdesc#seed, bdesc#ags
    and nall = Tvars.count_all tvs in
    assert (Array.length ags_sd = 1); (* nyi: inheritance with more than one
                                         formal generic *)
    let ags1 =
      if sd = i then
        ags
      else
        Term.subst_array ags_sd nall ags
    in
    let cls = Tvars.principal_class ags1.(0) tvs in
    try
      let idx_var = variant idx cls ft in
      let ags_var = variant_generics idx_var idx ags nall ft in
      nb + idx_var, ags_var
    with Not_found ->
      i,ags
  end


let substituted
    (t:term) (nargs:int) (nbenv:int) (ntvs:int)
    (args:arguments) (d:int)
    (ags:agens) (tvs:Tvars.t)
    (ft:t)
    : term =
  (* The term [t] has [nargs] arguments below [nbenv] variables. Furthermore
     there are formal generics or [ntvs] type variables (locals+generics!).

     The first arguments will be substituted by [args] coming from an
     enviroment with [d] variables more than [t].

     The formal generics will be substituted by [ags] coming from the type
     environment [tvs]. All feature calls will be specialized according to the
     actual generics.

     Note: All formal generics will be substituted.

     Note: The presence of type variables and formal generics is mutually
           exclusive.
   *)
  let len    = Array.length args
  and is_gen = (0 < Array.length ags)
  and nall   = Tvars.count_all tvs in
  assert (not is_gen || ntvs = 0);       (* mutually exclusive *)
  let subtp tp = Term.subst tp (nall-ntvs) ags in
  assert (len <= nargs);
  let rec spec nb t =
    let spec_args nb args = Array.map (fun t -> spec nb t) args
    and spec_lst  nb lst  = List.map  (fun t -> spec nb t) lst
    in
    match t with
      Variable i when i < nb ->
        t
    | Variable i when i < nb + len ->
        Term.up (nb+nargs-len) args.(i-nb)
    | Variable i when i < nb + nargs ->
        Variable (i - len)
    | Variable i ->
        Variable (i - len + d)
    | VAppl(i0,args,ags0) ->
        let ags0 = Array.map subtp ags0
        and args   = spec_args nb args in
        let i,ags0 =
          if is_gen then
            variant_feature i0 (nb+nargs+nbenv) ags0 tvs ft
          else
            i0,ags0
        in
        let i = i - len + d in
        VAppl (i,args,ags0)
    | Application (f,args,pr) ->
        let f = spec nb f
        and args = spec_args nb args in
        Application (f,args,pr)
    | Lam (n,nms,ps,t0,pr,tp) ->
        let nb = 1 + nb in
        let ps = spec_lst nb ps
        and t0 = spec nb t0
        and tp = subtp tp in
        Lam (n,nms,ps,t0,pr,tp)
    | QExp (n,(nms,tps),fgs,t0,is_all) ->
        assert (fgs = empty_formals);
        let nb = n + nb in
        let t0 = spec nb t0
        and tps = Array.map subtp tps in
        QExp (n,(nms,tps),fgs,t0,is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, spec_args nb args)
    | Indset (nme,tp,rs) ->
        let nb = 1 + nb in
        let rs = spec_args nb rs
        and tp = subtp tp in
        Indset (nme,tp,rs)
  in
  spec 0 t



let specialized (t:term) (nb:int) (tvs:Tvars.t) (ft:t)
    : term =
  let rec spec nb t =
    let spec_args nb args = Array.map (fun t -> spec nb t) args
    and spec_lst  nb lst  = List.map  (fun t -> spec nb t) lst
    in
    match t with
      Variable _ -> t
    | VAppl(i0,args,ags) ->
        let args  = spec_args nb args
        and i,ags = variant_feature i0 nb ags tvs ft in
        VAppl (i,args,ags)
    | Application (f,args,pr) ->
        let f = spec nb f
        and args = spec_args nb args in
        Application (f,args,pr)
    | Lam (n,nms,ps,t0,pr,tp) ->
        let nb = 1 + nb in
        let ps = spec_lst nb ps
        and t0 = spec nb t0 in
        Lam (n,nms,ps,t0,pr,tp)
    | QExp (n,tps,fgs,t0,is_all) ->
        assert (fgs = empty_formals);
        let nb = n + nb in
        let t0 = spec nb t0 in
        QExp (n,tps,fgs,t0,is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, spec_args nb args)
    | Indset (nme,tp,rs) ->
        let nb = 1 + nb in
        let rs = spec_args nb rs in
        Indset (nme,tp,rs)
  in
  spec nb t


let equality_term
    (a:term) (b:term) (nb:int) (tp:type_term) (tvs:Tvars.t) (ft:t)
    : term =
  (* The term [a = b] where [a] and [b] have the type [tp] in the type environment
     [tvs] and are valid in an environment with [nb] variables.

     Note: '=' in the class ANY has the signature [A:ANY](x,y:A):BOOLEAN
   *)
  let args0 = standard_substitution 2
  and ags0  = standard_substitution 1 in
  let eq0 = VAppl(2+eq_index, args0, ags0) in
  substituted eq0 2 0 0 [|a;b|] nb [|tp|] tvs ft



let implication (a:term) (b:term) (nb:int): term =
  (* The implication [a ==> b] where [a] and [b] are valid in an environment
     with [nb] variables.
   *)
  VAppl(nb+implication_index, [|a;b|], [||])



let definition_term (i:int) (ft:t): term =
  assert (i < count ft);
  Feature.Spec.definition_term (base_descriptor i ft)#specification


let definition (i:int) (nb:int) (ags:agens) (tvs:Tvars.t) (ft:t)
    : int * int array * term =
  (* The definition term of the feature [i-nb] transformed into an environment with
     [nb] variables, the formal generics substituted by [ags] which come from the
     type context [tvs] and the inner functions properly specialized *)
  assert (nb <= i);
  assert (i  <= nb + count ft);
  let idx = i - nb in
  let t0 = definition_term idx ft in
  let desc = descriptor idx ft in
  let nargs = arity idx ft in
  let t = substituted t0 nargs 0 0 [||] nb ags tvs ft in
  nargs, desc.argnames, t


(* Really necessary?? *)
let expanded_definition
    (i:int) (nb:int) (args:arguments) (ags:agens) (tvs:Tvars.t) (ft:t)
    : term =
  (* The definition of the feature [i-nb] expanded with the arguments [args]
     and the actual generics [ags] which come from the type context [tvs].

     The term to be expanded is [VAppl(i, args, ags)].
   *)
  assert (nb <= i);
  assert (i  <= nb + count ft);
  let idx = i - nb in
  let t0 = definition_term idx ft in
  let nargs = Array.length args in
  assert (nargs = arity idx ft);
  substituted t0 nargs 0 0 args nb ags tvs ft



let has_definition (i:int) (ft:t): bool =
  try ignore (definition_term i ft); true
  with Not_found -> false



let is_inductive_set (i:int) (nb:int) (ft:t): bool =
  (* Does the feature [i] in an environment with [nb] bound variables represent
     an inductively defined set`*)
  assert (nb <= i);
  try
    let t = definition_term (i-nb) ft in
    (*let n,nms,t = definition i nb ft in*)
    begin
      match t with
        Indset _ -> true
      | _        -> false
    end
  with Not_found ->
    false


let inductive_set (i:int) (args:term array) (ags:agens) (nb:int) (tvs:Tvars.t) (ft:t)
    : term =
  if is_inductive_set i nb ft then
    expanded_definition i nb args ags tvs ft
  else
    raise Not_found
  (*let n,nms,t = definition i nb ft in
  match t with
    Indset _ ->
      assert (n = Array.length args);
      Term.apply t args
  | _ ->
      raise Not_found*)


let preconditions (i:int) (nb:int) (ft:t): int * int array * term list =
  (* The preconditions (if there are some) of the feature [i] as optional number of
     arguments and a list of expressions transformed into an environment with [nb]
     bound variables.*)
  assert (nb <= i);
  let i = i - nb in
  let desc = descriptor i ft in
  let spec = (base_descriptor i ft)#specification in
  let n = arity i ft in
  if Feature.Spec.has_preconditions spec then
    let lst = Feature.Spec.preconditions spec in
    let lst = List.map (fun t -> Term.up_from nb n t) lst in
    n, desc.argnames, lst
  else
    n, desc.argnames, []



let postconditions (i:int) (nb:int) (ft:t): int * int array * term list =
  assert (nb <= i);
  let i = i - nb in
  let desc = descriptor i ft in
  let spec = (base_descriptor i ft)#specification in
  let n = arity i ft in
  let lst = Feature.Spec.postconditions spec in
  let lst = List.map (fun t -> Term.up_from nb n t) lst in
  n, desc.argnames, lst



let count_postconditions (i:int) (ft:t): int =
  let bdesc = base_descriptor i ft in
  Feature.Spec.count_postconditions bdesc#specification

let function_property_assertions (idx:int) (ft:t): term list =
  (* Get the list of assertions

        all[fgs](tps) r1 ==> r2 ==> ... ==> ei

     of a function with the specification

        f (a:A,b:B,...): RT
            require
                r1; r2; ...
            ensure
                e1(Result)
                e2(Result)
                ...
            end

     where [Result] has been replaced by [f(a,b,...)].
   *)
  let desc  = descriptor idx ft in
  let spec  = desc.bdesc#specification in
  let pres  = List.rev (Feature.Spec.preconditions spec)
  and posts = Feature.Spec.postconditions spec
  and nargs = Sign.arity desc.sign
  and tps   = Sign.arguments desc.sign
  and fgnms = Tvars.fgnames desc.tvs
  and fgcon = Tvars.fgconcepts desc.tvs
  in
  List.map
    (fun e ->
      let chn =
        Term.make_implication_chain pres e (nargs + implication_index)
      in
      let t =
        Term.all_quantified nargs (desc.argnames,tps) (fgnms,fgcon) chn
      in
      Term.prenex t 0 0 implication_index
    )
    posts



let function_property
    (i:int) (fidx:int) (nb:int) (args:term array) (ft:t): term =
  assert (nb <= fidx);
  assert false (* nyi *)
  (*let fidx = fidx - nb in
  let spec = (base_descriptor fidx ft).spec in
  let n = arity fidx ft in
  if n <> Array.length args then invalid_arg "wrong size of arguments";
  if i < 0 || count_postconditions fidx ft <= i then
    invalid_arg "postcondition does not exist";
  let pres  = Feature.Spec.preconditions spec
  and post  = Feature.Spec.postcondition i spec in
  let chn =
    Term.make_implication_chain (List.rev pres) post (implication_index + n) in
  Term.sub chn args nb*)




let domain_of_feature (i:int) (nb:int) (ags:agens) (tvs:Tvars.t) (ft:t): term =
  (* The domain of the feature [i] in a context with [nb] variables and the
     formal generics of the feature [i] substituted by the actual generics [ags]
     coming from the type environment [tvs].
   *)
  assert (nb <= i);
  assert (arity (i-nb) ft > 0);
  let n,nms,pres = preconditions i nb ft
  and nall = Tvars.count_all tvs
  in
  let subst t =
    substituted t 0 (n+nb) 0 [||] 0 ags tvs ft
  in
  let s = signature (i-nb) ags nall ft in
  let tp = Class_table.upgrade_signature nall true s in
  let t =
    match pres with
      [] ->
        true_constant (n+nb)
    | hd::tl ->
        let and_id = n + nb + and_index in
        List.fold_left
          (fun t1 t2 -> Term.binary and_id (subst t1) (subst t2))
          hd
          tl
  in
  make_lambda n nms [] t true nb tp ft




let body (i:int) (ft:t): Feature.body =
  assert (i < count ft);
  let desc = descriptor i ft
  and bdesc = base_descriptor i ft in
  bdesc#specification, desc.impl


let owner (i:int) (ft:t): int =
  assert (i < count ft);
  (descriptor i ft).cls


let is_ghost_function (i:int) (ft:t): bool =
  assert (i < count ft);
  let desc = descriptor i ft in
  Sign.is_ghost desc.sign


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
    | Lam (n,_,_,t,_,_) ->
        is_ghost t (1+nb)
    | QExp _ ->
        true
    | Flow (ctrl, args) ->
        let len = Array.length args in
        begin match ctrl with
          Ifexp ->
            ghost_args args 0 len
        | Asexp ->
            assert (len = 2);
            is_ghost args.(0) nb
        | Inspect ->
            assert (3 <= len);
            assert (len mod 2 = 1);
            let ncases = len / 2 in
            let rec cases_from i ghost =
              if ghost || i = ncases then
                ghost
              else
                let n,_,t   = Term.pattern_split args.(2*i+2) in
                let ghost = is_ghost t (n+nb) in
                cases_from (1+i) ghost
            in
            let ghost = is_ghost args.(0) nb in
            cases_from 0 ghost
        end
    | Indset _ ->
        true
    | VAppl (i,args,_) ->
        let ghost = is_ghost_function (i-nb-nargs) ft in
        ghost || ghost_args args 0 (Array.length args)
    | Application (f,args,_) ->
        let fghost = is_ghost f nb in
        fghost || ghost_args args 0 (Array.length args)
  in
  is_ghost t 0


let is_ghost_specification (spec:Feature.Spec.t) (ft:t): bool =
  Feature.Spec.has_postconditions spec ||
  (Feature.Spec.has_definition spec &&
   let nargs = Feature.Spec.count_arguments spec in
   is_ghost_term (Feature.Spec.definition_term spec) nargs ft)


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



let seed_function (ft:t): int -> int =
  fun i -> seed i ft


let seeded_term (t:term) (nb:int) (ft:t): term =
  assert false
  (*let rec seeded t nb =
    let seeded_args args nb = Array.map (fun t -> seeded t nb) args in
    match t with
      Variable i when i < nb -> t
    | Variable i ->
        Variable (nb + seed (i-nb) ft)
    | VAppl(i,args) ->
        assert (nb <= i);
        let i = nb + seed (i-nb) ft
        and args = seeded_args args nb in
        VAppl(i,args)
    | Application(f,args,pr) ->
        let f = seeded f nb
        and args = seeded_args args nb in
        Application(f,args,pr)
    | Lam(n,nms,pres,t0,pr) ->
        let t0 = seeded t0 (1+nb)
        and pres = List.map (fun t -> seeded t (1+nb)) pres in
        Lam(n,nms,pres,t0,pr)
    | QExp(n,nms,t0,is_all) ->
        let t0 = seeded t0 (n+nb) in
        QExp(n,nms,t0,is_all)
    | Flow(ctrl,args) ->
        let args = seeded_args args nb in
        Flow(ctrl,args)
    | Indset (n,nms,rs) ->
        let rs = seeded_args rs (n+nb) in
        Indset (n,nms,rs)
  in
  seeded t nb*)






(* Function expansion
   ==================

   A called function f(x,y,...) has the form

       VAppl(i,args,ags)

   The actual arguments replace the formal arguments, the actual generics replace
   the formal generics. If the function has a definition it has a definition term
   't0' which has the formal arguments i.e. 't0(x,y,...)'.

   The definition term 't0' might have other function calls of the form
   'VAppl(i,args,ags)'. However the actual generics in the inner function calls
   are expressed in terms of the formal generics of the outer function which have to
   be replaced by the actual generics of the outer function call. This replacement
   might lead to a more specialized inner function call.

   We need a function which replaces in a definition term all formal generics by
   actual generics an specializes the function calls appropriately.

*)


let rec fully_expanded (t:term) (nb:int) (tvs:Tvars.t) (ft:t)
    : term =
  (* Expand the functions in the term [t] which comes from an environment with
     [nb] variables and whose types are valid in the type environment [tvs].
   *)
  let expand t nb = fully_expanded t nb tvs ft in
  let expargs args nb = Array.map (fun t -> expand t nb) args
  and explst  lst  nb = List.map  (fun t -> expand t nb) lst
  in
  match t with
    Variable i ->
      assert (i < nb); t
  | VAppl(i,args,ags) ->
      assert (nb <= i);
      let args = expargs args nb in
      expanded_feature i args ags nb tvs ft
  | Application (f,args,pr) ->
      let f = expand f nb in
      Application(f,args,pr)
  | Lam (n,nms,ps,t0,pr,tp) ->
      let ps = explst ps (1+nb)
      and t0 = expand t0 (1+nb) in
      Lam(n,nms,ps,t0,pr,tp)
  | QExp (n,tps,fgs,t0,is_all) ->
      assert (fgs = empty_formals);
      let t0  = expand t0 (n+nb) in
      QExp(n,tps,fgs,t0,is_all)
  | Flow _ | Indset _ ->
      t

and expanded_feature
    (i:int) (args:arguments) (ags:agens) (nb:int) (tvs:Tvars.t) (ft:t): term =
  (* Expand the feature [i] (coming from an environment with [nb] bound variables)
     with the arguments [args] and the actual generics [ags] from the type
     environment [tvs] *)
  assert (nb <= i);
  let bdesc = base_descriptor (i-nb) ft in
  try
    let t0 = Feature.Spec.definition_term bdesc#specification in
    assert (Array.length args = arity (i-nb) ft);
    let nargs = Array.length args in
    let t = substituted t0 nargs 0 0 args nb ags tvs ft in
    fully_expanded t nb tvs ft
  with Not_found ->
    VAppl(i,args,ags)




let complexity (t:term) (nb:int) (tvs:Tvars.t) (ft:t): int =
  (* The complexity of the term [t] coming from and environment with [nvars]
     variables and the type context [tvs].

     The complexity of a term is the node count of the fully expanded term.
   *)
  let t = fully_expanded t nb tvs ft in
  Term.nodes t



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
        j
        (*printf "there is no variant of \"%s\" in class %s\n"
          (string_of_signature j ft)
          (Class_table.class_name cls ft.ct);
          assert false (* If [cls] inherits [base_cls] then there has to be a variant
                          in the descendant *)*)
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
  (* The variant of the specification of the feature [i] of the base class
     [base_cls] in the class [cls]. The feature in the descendant class [cls]
     has the index [inew].
   *)
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  let nargs,nms   = Feature.Spec.names bdesc#specification in
  let pres = List.map
      (fun t -> variant_term t nargs base_cls cls ft)
      (Feature.Spec.preconditions bdesc#specification)
  in
  if Feature.Spec.has_postconditions bdesc#specification then
    let posts =
      List.map
        (fun t -> variant_postcondition t i inew nargs base_cls cls ft)
        (Feature.Spec.postconditions bdesc#specification) in
    Feature.Spec.make_func_spec nms pres posts
  else
    let def = Feature.Spec.definition bdesc#specification in
    match def with
      None -> Feature.Spec.make_func_def nms None pres
    | Some defterm ->
        Feature.Spec.make_func_def
          nms (Some (variant_term defterm nargs base_cls cls ft)) pres


let equality_index (cls:int) (ft:t): int =
  variant eq_index cls ft


let equality_index_of_type (tp:term) (tvs:Tvars.t) (ft:t): int =
  let cls = Tvars.principal_class tp tvs in
  equality_index cls ft



let definition_equality (i:int) (ft:t): term =
  assert (i < count ft);
  assert (has_definition i ft);
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  assert (Sign.has_result desc.sign);
  let nargs = Sign.arity desc.sign
  and nfgs  = Tvars.count_all desc.tvs
  and r_tp  = Sign.result desc.sign
  in
  assert (desc.cls <> -1);
  let f_id  = nargs + i
  in
  let t = Option.value (Feature.Spec.definition bdesc#specification) in
  let f =
    if nargs = 0 then
      Variable f_id
    else
      let args = standard_substitution nargs
      and ags  = standard_substitution nfgs in
      VAppl (f_id, args, ags)
  in
  let eq_id = nargs + eq_index in
  VAppl (eq_id, [|f;t|], [|r_tp|])




let transformed_specifications (i:int) (ivar:int) (ags:agens) (ft:t): term list =
  (* The specification assertions of the feature [i] in the environment of the
     variant feature [ivar] with the actual generics valid in the variant. *)
  let posts =
    if has_definition i ft then
      [definition_equality i ft]
    else
      let _,_,posts = postconditions i 0 ft in
      posts
  and n,nms,pres  = preconditions  i 0 ft in
  let pres_rev = List.rev pres in
  let imp_id = n + implication_index
  and desc_var = descriptor ivar ft in
  let tps = Sign.arguments desc_var.sign
  and fgnms = Tvars.fgnames desc_var.tvs
  and fgcon = Tvars.fgconcepts desc_var.tvs
  in
  List.map
    (fun t ->
      let t1 = Term.make_implication_chain pres_rev t imp_id
      and args = standard_substitution n in
      let t2 = substituted t1 n 0 0 args n ags desc_var.tvs ft in
      QExp(n,(nms,tps),(fgnms,fgcon),t2,true)
    )
    posts





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



let find_with_signature
    (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t)
    : int =
  (* Find the feature with the name [fn] and the signature [tvs/sign].  *)
  let ntvs = Tvars.count_all tvs in
  let tp   = Class_table.to_dummy ntvs sign in
  let ntvs = Tvars.count_all tvs
  and tab = Feature_map.find fn ft.map in
  let lst  = Term_table.unify0 tp ntvs !tab in
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
            let ags = Term_sub.arguments (Term_sub.count sub) sub in
            assert (Array.length ags = 1); (* nyi: Inheritance with more than one
                                              formal generic.*)
            let cls = Tvars.principal_class ags.(0) tvs in
            try
              let ivar = variant i cls ft in
              ivar :: lst
            with Not_found ->
              lst
          end else
            lst)
      []
      lst
  in
  match idx_lst with
    [] -> raise Not_found
  | idx::rest ->
      if not (List.for_all (fun i -> i=idx) rest) then begin
        List.iteri
          (fun i idx ->
            printf "%d %d %s\n" i idx (string_of_signature idx ft))
          idx_lst
      end;
      assert (List.for_all (fun i -> i=idx) rest);
      idx




let has_with_signature (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t): bool =
  try
    let _ = find_with_signature fn tvs sign ft in true
  with Not_found -> false





let add_class_feature (i:int) (ft:t)
    : unit =
  (* Add the feature [i] as a class feature to the corresponding owner
     class and to the anchor class. *)
  assert (i < count ft);
  let desc  = descriptor i ft in
  Class_table.add_generics i false desc.tvs ft.ct


let add_key (i:int) (ft:t): unit =
  (** Add the key of the feature [i] to the key table. *)
  assert (i < count ft);
  let desc  = descriptor i ft in
  let ntvs  = Tvars.count_all desc.tvs
  in
  desc.tp <- Class_table.to_dummy ntvs desc.sign;
  let tab =
    try Feature_map.find desc.fname ft.map
    with Not_found ->
      let tab = ref Term_table.empty in
      ft.map <- Feature_map.add desc.fname tab ft.map;
      tab
  in
  tab := Term_table.add0 desc.tp ntvs 0 i !tab



let remove_key (i:int) (ft:t): unit =
  (* Remove the key of the feature [i] from the key table. *)
  let tab =
    try
      Feature_map.find (descriptor i ft).fname ft.map
    with Not_found ->
      assert false (* cannot happen *)
  in
  tab := Term_table.remove i !tab




let add_keys (ft:t): unit =
  for i = 0 to (count ft)-1 do
    add_key i ft
  done


let add_feature
    (fn:       feature_name withinfo)
    (tvs:      Tvars.t)
    (argnames: int array)
    (sign:     Sign.t)
    (impl:     Feature.implementation)
    (ft:       t): unit =
  (* Add a new feature to the feature table with an empty specification *)
  assert (not (has_with_signature fn.v tvs sign ft));
  let cnt     = Seq.count ft.seq
  and spec    = Feature.Spec.make_empty argnames
  and nfgs    = Tvars.count_all tvs
  in
  assert (not (Feature.Spec.has_definition spec));
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
  let bdesc = new bdesc cnt nfgs cls spec
  and nfgs = Tvars.count_all tvs
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
     bdesc    = bdesc}
  in
  Seq.push desc ft.seq;
  add_key cnt ft;
  add_class_feature cnt ft;
  if ft.verbosity > 1 then
    printf "  new feature %d %s\n" cnt (string_of_signature cnt ft)





let update_specification (i:int) (spec:Feature.Spec.t) (ft:t): unit =
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  assert (Feature.Spec.is_empty bdesc#specification);
  assert begin
    not (is_interface_check ft) ||
    Feature.Spec.private_public_consistent
      (base_descriptor i ft)#specification
      spec
  end;
  bdesc#set_specification spec




let set_owner_class (idx:int) (cls:int) (ft:t): unit =
  assert (idx < count ft);
  (descriptor idx ft).cls <- cls



let export_feature (i:int) (withspec:bool) (ft:t): unit =
  (* Export the feature [i] unless it is already publicly available. *)
  assert (i < count ft);
  if ft.verbosity > 1 then
    printf "  export feature %d %s\n" i (string_of_signature i ft);
  (descriptor i ft).bdesc#set_exported


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
  let bdesc = new bdesc cnt ntvs cls spec
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
    bdesc    = bdesc
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
  let p_tp1 = make_type (Class_table.predicate_index+1) [|g_tp|]
  and p_tp2 = make_type (Class_table.predicate_index+2) [|a_tp|]
  and f_tp  = make_type (Class_table.function_index+2)  [|a_tp;b_tp|]
  and tup_tp= make_type (Class_table.tuple_index+2) [|a_tp;b_tp|]
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
  and imp_id2   = 2 + implication_index
  and not_id2   = 2 + not_index
  in
  let not_term = Term.binary imp_id1 (Variable 0) (false_constant 1)
  and or_term  =  Term.binary imp_id2 (Term.unary not_id2 (Variable 0)) (Variable 1)
  and and_term =
    Term.unary  not_id2
      (Term.binary imp_id2
         (Variable 0)
         (Term.binary imp_id2 (Variable 1) (false_constant 2)))
  and true_term =
    Term.binary implication_index (false_constant 0) (false_constant 0)
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


let has_visible_variant (i:int) (ft:t): bool =
  (* Does the feature [i] has a visible variant in the current module?
   *)
  assert (is_interface_use ft);
  let bdesc = base_descriptor i ft
  and mt    = module_table ft in
  let used  = Module_table.current_used mt in
  IntMap.exists
    (fun cls ivar ->
      let desc  = descriptor ivar ft in
      IntSet.mem desc.mdl used)
    bdesc#variants



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
        if arity <= nargs then
          (i,tvs,sign) :: lst
        else if nargs = 0 then begin (* upgrade *)
          assert (0 < arity);
          let is_pred = is_predicate i ft in
          let tp = Class_table.upgrade_signature nfgs is_pred sign in
          let s  = Sign.make_const tp in
          (i,tvs,s) :: lst
        end else (* nargs <> 0  && nargs < arity *)
          lst
      )
      []
      (Term_table.terms !tab)
  in
  if lst = [] then raise Not_found
  else lst


let variant_data (i:int) (k:int) (ft:t): agens =
  (* Tell if [i] is a base feature of [k] i.e. [k] is a variant of [i].
     If no then raise [Not_found].
     If yes then return the actual generics to substitute the formal generics of [i]
     to make the signatures identical.
   *)
  let desc_i = descriptor i ft
  and desc_k = descriptor k ft
  in
  let nfgs_i = Tvars.count_fgs desc_i.tvs
  and nfgs_k = Tvars.count_fgs desc_k.tvs
  in
  let ags = Array.make nfgs_i empty_term
  in
  unify_types desc_i.tp nfgs_i desc_k.tp nfgs_k ags;
  let ok =
    interval_for_all
      (fun j ->
        Class_table.satisfies
          ags.(j) desc_k.tvs
          (Tvars.concept j desc_i.tvs) desc_i.tvs
          ft.ct
      )
      0 nfgs_i in
  if ok then
    ags
  else
    raise Not_found




let find_minimal_variants (i:int) (cls:int) (ft:t): (int*agens) list =
  (* Find the minimal variants of the feature [i] in the variant table of
     [i] or the seed of [i] with at least one class above [cls].

     Return a list [ivar,ags] of the minimal variants so that the signature of
     [i] substituted by the actual generics [ags] yields the signature of
     [ivar]
   *)
  let desc_i = descriptor i ft in
  let sd     = desc_i.bdesc#seed in
  let desc_sd = descriptor sd ft in
  IntMap.fold
    (fun _ ivar lst ->
      if i = ivar then
        lst
      else
        try
          let ags = variant_data i ivar ft in
          let desc_ivar = descriptor ivar ft in
          let above =
            interval_exist
              (fun k ->
                let pcls = Tvars.principal_class ags.(k) desc_ivar.tvs in
                Class_table.has_ancestor pcls cls ft.ct
              )
              0 (Array.length ags) in
          if not above then
            raise Not_found;
          (* [ivar] is a variant of [i], but is it minimal? *)
          let lst,is_min =
            List.fold_left
              (fun (lst,is_min) (ivar0,ags0) ->
                if not is_min then
                  (ivar0,ags0) :: lst, false
                else
                  try
                    ignore(variant_data ivar ivar0 ft);
                    lst, true
                  with Not_found ->
                    (ivar0,ags0) :: lst, false
              )
              ([],true)
              lst
          in
          if is_min then
            (ivar,ags) :: lst
          else
            lst
        with Not_found ->
          lst
    )
    desc_sd.bdesc#variants
    []




let find_unifiables (fn:feature_name) (tp:type_term) (ntvs:int) (ft:t)
    : (int*Term_sub.t) list =
  try
    let tab = Feature_map.find fn ft.map in
    Term_table.unify0_with tp ntvs 0 !tab
  with Not_found ->
    []



let find_new_variants (i:int) (ft:t): (int*agens) list =
  (* Find new variants of the feature [i] in the search tables.

     A new variant has the same name and there is a valid substitution of
     the formal generics of [i] so that the signature of [i] becomes equal to
     the signature of the variant candidate.

     Return a list [ivar,ags] of the new variants so that the signature of [i]
     substituted by the actual generics [ags] yields the signature of [ivar]
   *)
  let desc = descriptor i ft in
  let nfgs = Tvars.count_all desc.tvs in
  List.fold_left
    (fun lst (idx,sub) ->
      assert (nfgs = Term_sub.count sub);
      if i = idx then
        lst
      else
        let desc_idx = descriptor idx ft in
        let valid =
          Term_sub.for_all
            (fun k tp ->
              Class_table.satisfies tp desc_idx.tvs (Variable k) desc.tvs ft.ct
            )
            sub in
        if valid then
          (idx,Term_sub.arguments nfgs sub)::lst
        else
          lst
    )
    []
    (find_unifiables desc.fname desc.tp nfgs ft)


let get_variant_seed (i:int) (ivar:int) (ags:agens) (ft:t): int*agens =
  (* Get the seed of the feature [i] which has variant [ivar] and the actual
     generics [ags] which transform the signature of [i] into the signature of
     [ivar] ([ags] are valid in the environment of [ivar].

     Return the seed of [i] together with the actual generics which transform the
     signature of the seed into the signature of [ivar] *)
  let desc_i = descriptor i ft
  and desc_ivar = descriptor ivar ft in
  let sd, ags0 = desc_i.bdesc#seed, desc_i.bdesc#ags in
  let d = Tvars.count_all desc_ivar.tvs in
  let agssd = Term.subst_array ags0 d ags in
  sd,agssd



let add_variant (sd:int) (ivar:int) (ags:agens) (ft:t): unit =
  (* Add to the seed [sd] the variant [ivar] where [ags] are the actual generics
     which substitute the formal generics of [sd] the get the same signature.

     Furthermore remove the variant [ivar] from the key table! Reason: A variant
     shall be found only via its seed.
   *)
  assert (Array.length ags = 1); (* nyi: variants of seeds with more than one
                                    formal generic *)
  let desc_ivar = descriptor ivar ft in
  let cls = Tvars.principal_class ags.(0) desc_ivar.tvs in
  (base_descriptor sd ft)#add_variant cls ivar;
  remove_key ivar ft



let set_seed (sd:int) (ivar:int) (ags:agens) (ft:t): unit =
  (* Add the seed [sd] to the variant [ivar] where [ags] are the actual generics
     which substitute the formal generics of [sd] the get the same signature.
   *)
  (base_descriptor ivar ft)#set_seed sd ags





let is_equality_index (idx:int) (ft:t): bool =
  (base_descriptor idx ft)#is_equality



let split_equality (t:term) (nbenv:int) (ft:t): int * int * term * term =
  (* Return [nargs, eq_id, left, right] if the term is an equality. *)
  let nargs, t =
    try
      let n,(nms,_),_,t0 = Term.all_quantifier_split t in
      n, t0
    with Not_found ->
      0, t
  in
  let nbenv = nbenv + nargs in
  let i,a,b = Term.binary_split_0 t in
  let i = i - nbenv in
  assert (i < count ft);
  if (base_descriptor i ft)#is_equality then begin
    nargs, i, a, b
  end else
    raise Not_found


let is_equality (t:term) (nbenv:int) (ft:t): bool =
  try
    let _ = split_equality t nbenv ft in true
  with Not_found -> false



let add_base_features (mdl_name:int) (ft:t): unit =
  try
    let lst = IntMap.find mdl_name ft.base in
    let curr_mdl = current_module ft in
    List.iter
      (fun idx ->
        let desc = descriptor idx ft in
        assert (desc.mdl = -1);
        desc.mdl <- curr_mdl;
        add_key idx ft;
        add_class_feature idx ft)
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
    or_desc.bdesc#set_specification
      (Feature.Spec.make_func_def or_desc.argnames  None []);
    and_desc.bdesc#set_specification
      (Feature.Spec.make_func_def and_desc.argnames None [])
  end



let set_interface_check (used:IntSet.t) (ft:t): unit =
  Class_table.set_interface_check used ft.ct(*;
  ft.map <- Feature_map.empty;
  let mdl = current_module ft in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if desc.mdl = mdl || IntSet.mem desc.mdl used then
      match desc.pub with
        Some bdesc ->
          if not bdesc#is_inherited then
            add_key i ft
      | None ->
          add_key i ft;
          if desc.mdl <> mdl then
            desc.pub <- Some (desc.priv)
  done*)



let check_interface (ft:t): unit =
  assert (is_interface_check ft);
  let mt = module_table ft in
  let curr = Module_table.current mt in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if curr = desc.mdl
        && is_desc_deferred desc
        && not desc.bdesc#is_exported
        && Class_table.is_class_public desc.cls ft.ct then
      error_info (FINFO (1,0))
        ("deferred feature `" ^ (string_of_signature i ft) ^
         "' is not public")
  done




let pattern_subterms (n:int) (pat:term) (nb:int) (ft:t): (int*term*int) list =
  (* Return a list of all subterms of the pattern [n,pat] with their level.
   *)
  let rec subterms t level lst =
    match t with
      Variable i ->
        assert (i < n || n + nb <= i);
        assert (i < n || is_constructor (i-n-nb) ft);
        (n+nb,t,level)::lst
    | VAppl(i,args,ags) ->
        assert (n + nb <= i);
        assert (is_constructor (i-n-nb) ft);
        let lst = (n+nb,t,level)::lst
        and level = level + 1 in
        Array.fold_left
          (fun lst arg -> subterms arg level lst)
          lst
          args
    | _ ->
        assert false (* cannot happen in pattern *)
  in
  subterms pat 0 []




let peer_constructors (i:int) (ft:t): IntSet.t =
  assert (i < count ft);
  assert (is_constructor i ft);
  let cls = class_of_feature i ft in
  assert (cls <> -1);
  let set = Class_table.constructors cls ft.ct in
  assert (IntSet.mem i set);
  IntSet.remove i set



type tplst = type_term list

let peer_matches
    (i:int) (ags:agens) (nb:int) (ntvs:int) (ft:t): (int*tplst*term) list =
  (* Match expressions for the peer constructors on the constructor [i] with
     actual generics [ags] coming from an environment with [nb] variables and
     ntvs type variables. *)
  assert (i < count ft);
  assert (is_constructor i ft);
  let set = peer_constructors i ft in
  IntSet.fold
    (fun i lst ->
      assert (is_constructor i ft);
      let tvs,s = signature0 i ft in
      assert (Tvars.count_all tvs = Array.length ags);
      let n = Sign.arity s
      and tps = Array.to_list (Sign.arguments s) in
      let tps = List.map (fun tp -> Term.subst tp ntvs ags) tps in
      let t =
        let args = Array.init n (fun i -> Variable i) in
        VAppl (i+nb+n,args,ags) in
      (n,tps,t)::lst)
    set
    []





(*  Complementary Pattern
    =====================

    We have a pattern [pat] and want to find the minimal set of complementary
    pattern so that one pattern of the complete set always matches.

    (a) The pattern is a variable: The complementary set is empty (catch all)

    (b) The pattern has the form [f(a,b,...)] (Note: [f] has to be a constructor).

        The first part of the complementary set consists of all trivial
        pattern of the peer constructors of [f].

        Each argument has a complementary set. We have to make a combination
        of the complementary sets of the arguments. We compute a list of
        argument pattern lists and start with the list of arguments and an
        empty list of argument pattern lists:

        (a1) The argument list is empty: No pattern is added to the list of
             argument pattern lists.

        (a2) The argument list is 'rest+a':

             cset: The complementary pattern set of 'a'
             lst:  The list of argument pattern lists of the rest

             for each pattern in {a}+cset
                 for each argument pattern list in 'lst':
                     append a to the argument pattern list
             concatenate all list of argument pattern lists

             for each pattern p in cset
                     add [v0,v1,...,p] to the resulting argument pattern list ????

        (a3) At the end we have a complete list of argument pattern list

             The complementary set of 'f(a,b,...)' is

                   fcset + {f(a0,b0,...), f(a1,b1,...), ... }

             where [ai,bi,...] is an entry in the list of argument pattern lists.

    Boundary cases:

        f(a,b,...) is f(v0,v1,...) where vi is a variable:

        The complementary set of each vi is empty. The list of argument
        pattern lists before is empty before and remains empty during
        (a2). Therefore the complementary pattern set of f(v) consist of all
        primitive pattern of the peer constructors of f.

    Implementation hints:

        (a) A pattern set has the form

                 {(p0,n0), (p1,n1), ... }

            where p is the pattern term and n is the number of variables in
            the pattern.

        (b) A list of argument pattern lists has the form

                 [ ([p0a,p0b,...],n0), ([p1a,p1b,...],n1), ... ]

            where [pia,pib,...] is the ith argument pattern sequence and [ni]
            is the number of used variables in the pattern sequence.

            Appending an argument pattern (p,n) to the sequence ([pia,pib,...],ni)
            results in ([pia,pib,...p'],n+ni) where p' is p shifted up by n.


 *)

let complementary_pattern
    (n:int) (tps:types) (p:term) (nb:int) (ntvs:int) (ft:t)
    : (int*tplst*term) list =
  let rec compl_pat (p:term): (int*tplst*term) list =
    let rec args_pat_lst (argsrev:term list) (nargs:int)
        (aplst:(term list*int*tplst) list)
        : (term list*int*tplst) * (term list*int*tplst) list =
      assert (List.length argsrev = nargs);
      match argsrev with
        [] ->
          ([],0,[]), aplst
      | a::tl ->
          let cset  = compl_pat a
          and (argsrevtl,nargsrevtl,tpsrevtl), aplst =
            args_pat_lst tl (nargs-1) aplst in
          let a,na,tpsa =
            let abnd  = Term.bound_variables a n
            and perm  = Array.make n (Variable (-1)) in
            let na,tpsa = IntSet.fold
                (fun i (na,tpsa) ->
                  perm.(i) <- Variable na; na+1, tps.(i)::tpsa)
                abnd (0,[]) in
            let a = Term.subst a na perm in
            a,na,tpsa
          in
          let push_arg n tps p nargsrev argsrev tpsrev =
            let argsrev =
              List.map (fun t -> Term.up_from n nargsrev t) argsrev in
            let argsrev = (Term.up nargsrev p)::argsrev
            and tps = List.rev_append tps tpsrev in
            argsrev,(n+nargsrev),tps in
          let prepend_pattern np tps p aplst =
            List.rev_map
              (fun (argsrev,n,tpsrev) -> push_arg np tps p n argsrev tpsrev)
              aplst in
          let aplst =
            let cset = (na,tpsa,a)::cset in
            let lstlst =
              List.rev_map (fun (n,tps,p) -> prepend_pattern n tps p aplst) cset in
            List.concat lstlst in
          let push_arg0 n tps p = push_arg n tps p nargsrevtl argsrevtl tpsrevtl in
          let aplst =
            List.fold_left
              (fun aplst (n,tps,p) ->
                (push_arg0 n tps p)::aplst)
              aplst
              cset in
          push_arg0 na tpsa a, aplst
    in
    match p with
      Variable i when i < n ->
        []
    | Variable i ->
        assert (n + nb <= i);
        assert false (* there are no global variables *)
    | VAppl (i,args,ags) ->
        assert (n + nb <= i);
        let idx = i-n-nb in
        let fcset = peer_matches idx ags nb ntvs ft in
        let nargs    = Array.length args
        and args_rev = List.rev (Array.to_list args) in
        let _,apl = args_pat_lst args_rev nargs [] in
        List.fold_left
          (fun cset (args_rev,n,tps) ->
            let args = Array.of_list (List.rev args_rev)
            and tps  = List.rev tps in
            assert (Array.length args = nargs);
            let p  = VAppl (idx+n+nb,args,ags) in
            (n,tps,p) :: cset)
          fcset
          apl
    | _ ->
        assert false (* cannot happen in pattern *)
  in
  compl_pat p




let is_pattern (n:int) (t:term) (nb:int) (ft:t): bool =
  (* Is the term [t] with [n] variables a pattern i.e. does it contain only variables
     or constructors?

     All variables below [n] must occur only once in a pattern.
   *)
  let is_constr i = (n+nb) <= i && is_constructor (i-n-nb) ft
  in
  let free = Term.free_variables     t n
  and bnd  = Term.bound_variables    t n
  and bnd_lst = Term.used_variables t n in
  let nbnd = IntSet.cardinal bnd
  in
  IntSet.for_all is_constr free &&
  n = nbnd &&
  nbnd = List.length bnd_lst




let case_substitution
    (t:term) (npat:int) (pat:term) (nb:int) (ft:t): (term array) option =
  (* The substitutions for the pattern [pat] which make the pattern equivalent
     to the term [t] (with [nt] variables) or [None] if the match definitely
     fails. The function raises [Not_found] if neither a positive or a
     negative match is possible i.e. if matching cannot be decided because
     the term does not provide enough information.

     Positive match: The term is more special than the pattern and substitutions
                     can be found.

     Negative match: The term has a different constructor than the pattern at a
                     corresponding position.

     Undecidable:    The term is more general than the pattern or the term has a
                     non constructor at some position where a constructor would be
                     needed to compare it with the corresponding constructor of the
                     pattern. The latter case cannot occur if the term is a pattern.

                     I.e. if the term is a pattern then Undecidable means that the
                     term is more general.

     Note: [pat] must be a pattern i.e. it contains only constructors and variables!
   *)
  let subargs = Array.make npat (Variable (-1))
  and subflgs = Array.make npat false
  and decid   = ref true
  and hassub  = ref true in
  let is_constr idx =
    nb <= idx && is_constructor (idx-nb) ft
  in
  let rec do_match t pat =
    let match_args args1 args2 =
      assert (Array.length args1 = Array.length args2);
      Array.iteri
        (fun i arg ->
          do_match arg args2.(i))
        args1
    in
    match t, pat with
      _, Variable i ->
        assert(i < npat);  (* otherwise it would not be a pattern *)
        assert (not subflgs.(i));
        subflgs.(i) <- true;
        subargs.(i) <- t
    | VAppl(idx1,args1,ags1), VAppl(idx2,args2,ags2) when  is_constr idx1 ->
        assert (nb <= idx1);
        assert (npat + nb <= idx2);
        hassub :=  !hassub &&  idx1 = idx2 - npat;
        if !hassub then
          match_args args1 args2;
    | _ ->
        decid := false
  in
  do_match t pat;
  assert (not !hassub || not !decid || interval_for_all (fun i -> subflgs.(i)) 0 npat);
  if not !hassub then
    None
  else if !decid then
    Some subargs
  else
    raise Not_found




let is_case_matching (t:term) (npat:int) (pat:term) (nb:int) (ft:t): bool =
  (* Is the term [t] matching the pattern [pat] with [npat] variables?
     Raise [Not_found] if the match is undecidable.
   *)
  match case_substitution t npat pat nb ft with
    None   -> false
  | Some _ -> true





(*  Unmatched cases
    ===============


    Example:

        is_prefix (a,b:[G]): BOOLEAN
            -> inspect a, b
               case nil, _   then true
               case _  , nil then false
               case x^a, y^b then x = y and a.is_prefix(b)
               end

    The first case leaves us the unmatched cases:

         (0^1, 2)

    The second case has the pattern (0, nil) and should leave us with

         (0^1, 2^3)

    which is matched by the third case.

    The peer pattern of the second case:

        (0, 1^2)

    Check the second case:
        compare unmatched    (0^1,   2)
        with pattern         (0  , nil)

    An unmatched pattern has to be either
        removed                           the pattern is more general
        left in unchanged                 unmatched and pattern do not match
        modified and/or splitted up       the pattern matches partially

    Partial match: There is a substitution for the unmatched and for the pattern.
                   When both substitutions are applied the terms are equal

       (0^1,2)   sub [0~>0,1~>1,2~>nil]    res (0^1,nil)
       (0,nil)   sub [0~>0^1]              res (0^1,nil)

    The pattern is more general: Special case of a partial match where the
                                 substitution of the unmatched is empty

    No match: There is no substitution pair.


    Unification of two pattern:
    ===========================

    Example 1:
    (0^1,2) and (0,nil)

    With unique variables (0^1,2) and (3,nil)

    General substitution: [0~>0,1~>1,2~>nil,  3~>0^1]
    makes both to (0^1,nil)

    Example 2:
    (0^1,2) and (0,1)

    With unique variables (0^1,2) and (3,4)

    General substitution: [0~>0,1~>1,2~>2,  3~>0^1,4~>2]
    makes both to (0^1,2)

    If one pattern is more special than the other it gets the identity substitution.
    I.e. substitution happens only on the more general pattern.

    Computing unmatched pattern
    ===========================

    For each case clause we have a set of unmatched pattern of the previous clauses.

    For each pattern in the set of unmatched pattern the current pattern is either

    - unrelated:     The unmatched pattern remains
    - more general:  The unmatched pattern is resolved
    - partial match: The unmatched pattern has to be splitted into unmatched and
                     resolved subpattern. Only the unmatched subpattern remain.

    Splitting partially resolved pattern
    ====================================

    We have an unmatched pattern upat and a pattern pat. We unify the two pattern
    and get a substitution which is not the identity in the part of the variables
    of upat. The variables with a nontrivial substitution are only partially
    resolved.

    1. Do the substitution on upat to get upatsub
         The partially resolved variables disappear and some variables of pat
         might be introduced

    2. Treat upatsub as a pattern and calculate all peer pattern

    3. Filter the peer pattern so that only pattern more special than upat remain

    The unmatched pattern upat has to be splitted up into the filtered set of peer
    pattern of upatsub.

 *)
let unmatched_and_splitted
    (n:int) (tps:tplst) (pat:term) (unmatched:(int*tplst*term)list)
    (nb:int) (ntvs:int) (ft:t)
    : (int*tplst*term) list * (int * tplst * term * term array option) list =
  (* Calculate the remaining unmatched pattern and a split list. The unmatched
     pattern are all the pattern which are left over with the pattern [n,pat]
     working of the unmatched cases in [unmatched]. The split list consist of one
     ore more pattern into which [n,pat] has to be splitted. The pattern has to be
     splitted if it is more general than some pattern in [unmatched].
   *)
  let is_trivial arr n =
    assert (n <= Array.length arr);
    interval_for_all
      (fun i ->
        match arr.(i) with
          Variable k -> k < n
        | _ -> false)
      0 n
  and unmatched_partial
      (n:int) (tps:tplst) (pat:term)
      (arr: term array) (tps2:tplst)
      : int * tplst * term =
    assert (n <= Array.length arr);
    let len = Array.length arr in
    let n2  = len - n in
    let tps = Array.append (Array.of_list tps) (Array.of_list tps2) in
    assert (len = Array.length tps);
    let upat  = Term.up_from n2 n pat in
    let upat  = Term.subst upat len arr in
    let used  = List.rev (Term.used_variables upat len) in
    let n_new = List.length used in
    let arr2  = Array.make len empty_term
    and tps_new = Array.make n_new empty_term in
    List.iteri (fun pos i ->
      arr2.(i) <- Variable pos;
      tps_new.(pos) <- tps.(i)) used;
    let upat  = Term.subst upat n_new arr2
    and tps_new = Array.to_list tps_new in
    n_new, tps_new, upat in
  let add_filtered_peers
      (peers:(int*tplst*term) list)
      (npat:int) (tps:tplst) (pat:term)
      (lst:(int*tplst*term) list)
      : (int*tplst*term) list =
    List.fold_left
      (fun lst (n,tps,t) ->
        try
          let subarr = Term_algo.unify_pattern n t npat pat in
          if is_trivial subarr n then (n,tps,t) :: lst else lst
        with Not_found ->
          lst)
      lst
      peers
  in
  let unmatched,splitted = List.fold_left
      (fun (unmatched,splitted) (npat0,tps0,pat0) ->
        try
          let subarr = Term_algo.unify_pattern npat0 pat0 n pat in
          assert (Array.length subarr = npat0 + n);
          if is_trivial subarr npat0 then begin
            (* pat is more general, i.e. pat0 no longer needed as unmatched *)
            let newsplit =
              if npat0 = n && pat = pat0 then (n,tps,pat,None)
              else (npat0,tps0,pat0,Some subarr) in
            unmatched,
            newsplit::splitted
          end else begin
            (* pat resolves pat0 only partial, splitting of pat necessary *)
            let n2, tps2, upat2 = unmatched_partial npat0 tps0 pat0 subarr tps in
            assert (n2 = List.length tps2);
            let tps2arr = Array.of_list tps2 in
            let peers = complementary_pattern n2 tps2arr upat2 nb ntvs ft
            and subarr =
              try Term_algo.unify_pattern n2 upat2 n pat
              with Not_found -> assert false
            in
            add_filtered_peers peers npat0 tps0 pat0 unmatched,
            (n2,tps2,upat2,Some subarr)::splitted
          end
        with Not_found -> (* pat and pat_i cannot be unified *)
          (npat0,tps0,pat0) :: unmatched, splitted)
      ([],[])
      unmatched in
  unmatched, splitted



let unmatched_inspect_cases (args:term array) (nb:int) (ntvs:int) (ft:t)
    : (int * tplst* term) list =
  (* The unmatched cases of the inspect expression [Flow(Inspect,args)]
   *)
  let len = Array.length args in
  assert (3 <= len);
  assert (len mod 2 = 1);
  let ncases = len / 2 in
  let rec unmatched_from (i:int) (lst:(int*tplst*term) list)
      : (int*tplst*term) list =
    assert (i <= ncases);
    if i = ncases then
      lst
    else begin
      let npat_i,(_,tps_i),pat_i = Term.pattern_split args.(2*i+1) in
      let tps_i = Array.to_list tps_i in
      let unmatched,_ = unmatched_and_splitted npat_i tps_i pat_i lst nb ntvs ft in
      unmatched_from (i+1) unmatched
    end
  in
  unmatched_from 0 [1, [empty_term], Variable 0] (* empty_term shall not be used!! *)




(* "Catch all" cases:

        (<=) (a,b:NATURAL): BOOLEAN
            -> inspect a,b
               case 0,            _            then true        -- critical!!
               case _,            0            then false
               case successor(n), successor(m) then n <= m
               end

   The first case is implicitly two cases. The inspect has to be unfolded

        (<=) (a,b:NATURAL): BOOLEAN
            -> inspect a,b
               case 0,            0            then true
               case 0,            successor(_) then true
               case successor(_), 0            then false
               case successor(n), successor(m) then n <= m
               end

   It might be possible that one inspect variable has only catchall cases.

        plus (t:(NATURAL,NATURAL): NATURAL
            -> inspect t
               case (a,0)            then a                   -- uncritical
               case (a,successor(b)) then successor(a + b)
               end

   In the first example the catchall case is critical in the third example it
   is uncritical and does not require unfolding. What's the difference? In the
   first example there are other cases where a constructor appears at the same
   position, i.e. the inspect expression actually distinguishes cases at this
   position.

   For each case we have to calculate the unmatched pattern of all previous
   cases. With the current pattern and the unmatched set we can calculate the
   new set of cases which will substitute the current case.

       Walk through all unmatched:

          a) unmatched pattern is more general: split up the unmatched
             pattern. The current case is not modified.

          b) current pattern is more general or equal: Add a case clause with
             the unmatched (there might be more unmatched pattern which are
             more special than the current pattern.

   If the set of unmatched pattern is empty then the case clause is not needed.
   This condition might be flagged as an error. *)


let inspect_unfolded (info:info) (args:term array) (nb:int) (ntvs:int)(ft:t)
    : term array =
  (* Unfold case clauses in the inspect expression [Flow(Inspect,args)].

     A case clause has to be unfolded to a set of clauses if it is more general
     than some of the unmatched clauses.
   *)
  let len = Array.length args in
  assert (3 <= len);
  assert (len mod 2 = 1);
  let ncases = len / 2 in
  let rec unfolded_from
      (i:int) (unmatched: (int*tplst*term)list) (lst: term list): term list =
    if i = ncases then
      lst
    else
      let n,(nms,tps),pat,res = Term.case_split args.(2*i+1) args.(2*i+2) in
      let tps = Array.to_list tps in
      let unmatched,splitted =
        unmatched_and_splitted n tps pat unmatched nb ntvs ft in
      if splitted = [] then
        error_info info ("Unneeded case " ^ (string_of_term_anon pat (n+nb) ft));
      let lst =
        List.fold_left
          (fun lst (n0,tps0,pat0,sub_opt) ->
            assert (n0 = List.length tps0);
            let n1,nms1,tps1,pat1,res1 =
              match sub_opt with
                None ->
                  assert (n = n0);
                  n,nms,tps,pat,res
              | Some arr ->
                  assert (Array.length arr = n0 + n);
                  let res0 = Term.up n0 res in
                  let res0 = Term.subst res0 (n0+n) arr in
                  let res0 =
                    try Term.down_from n n0 res0
                    with Term_capture -> assert false in
                  n0, (standard_argnames n0), tps0, pat0, res0
            in
            let tps1 = Array.of_list tps1 in
            (Term.pattern n1 (nms1,tps1) res1) ::
            (Term.pattern n1 (nms1,tps1) pat1) :: lst)
          lst
          splitted
      in
      unfolded_from (i+1) unmatched lst
  in
  let lst = unfolded_from 0 [1, [empty_term], Variable 0] [] in
  let lst = args.(0) :: (List.rev lst) in
  let args = Array.of_list lst in
  args




let downgrade_term (t:term) (nb:int) (ntvs:int) (ft:t): term =
  (* Downgrade all calls of the form
 
         [ Application (VAppl (i, [||], ags), args, pr)]
     to

         [VAppl(i,args')] if [i] is not a constant.
   *)
  let rec down t nb =
    let down_args args nb = Array.map (fun t -> down t nb) args
    and down_list lst nb  = List.map  (fun t -> down t nb) lst in
    match t with
      Variable _ ->
        t
    | VAppl (i,args,ags) ->
        VAppl(i, down_args args nb,ags)
    | Application(VAppl (i,[||],ags),args,pr) when nb <= i ->
        assert (Array.length args = 1);
        let nargs = arity (i - nb) ft in
        let args = down_args args nb in
        if nargs = 0 then
          t
        else
          let s = signature i ags ntvs ft in
          let tup_tp = Class_table.to_tuple ntvs 0 (Sign.arguments s) in
          let args = args_of_tuple_ext args.(0) tup_tp nb nargs ft in
          VAppl(i,args,ags)
    | Application(f,args,pr) ->
        Application (down f nb, down_args args nb, pr)
    | Lam(n,nms,pres,t0,pr,tp) ->
        Lam (n,nms, down_list pres (1+nb), down t0 (1+nb), pr, tp)
    | QExp (n,tps,fgs,t0,is_all) ->
        QExp (n,tps,fgs, down t0 (n+nb), is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, down_args args nb)
    | Indset (nme,tp,rs) ->
        Indset (nme, tp, down_args rs (1+nb))
  in
  down t nb


let collect_called (t:term) (nb:int) (ft:t): IntSet.t =
  let rec collect (t:term) (nb:int) (set:IntSet.t): IntSet.t =
    let collect_args args nb set =
      Array.fold_left
        (fun set arg -> collect arg nb set)
        set
        args
    in
    match t with
      Variable _ ->
        set
    | VAppl(i,args,ags) ->
        assert (nb <= i);
        let set = IntSet.add (i-nb) set in
        collect_args args nb set
    | Application (f,args,is_pred) ->
        let set = collect f nb set in
        collect_args args nb set
    | Lam (n, nms, pres, t0, is_pred, tp) ->
        collect t0 (1+nb) set
    | QExp (n, args, fgs, t0, is_all) ->
        collect t0 (n+nb) set
    | Flow (flow, args) ->
        collect_args args nb set
    | Indset (nme,tp,rs) ->
        collect_args rs (1+nb) set
  in
  collect t nb IntSet.empty



let validate_visibility (t:term) (nb:int) (info:info) (ft:t): unit =
  if not (is_interface_check ft) then
    ()
  else
    let set = collect_called t nb ft in
    let set = IntSet.filter (fun idx -> not (is_feature_public idx ft)) set in
    if not (IntSet.is_empty set) then
      let strlst =
        List.map
          (fun idx -> "    " ^ (string_of_signature idx ft))
          (IntSet.elements set) in
      let str = String.concat "\n" strlst in
      error_info info ("The following functions are not visible:\n" ^ str)



let involved_assertions (fidx:int) (ft:t): IntSet.t =
  (base_descriptor fidx ft)#involved_assertions


let add_involved_assertion (ia:int) (t:term) (ft:t): unit =
  (* Add [ia] as an involved assertion to all global functions of the term [t].
   *)
  IntSet.iter
    (fun fidx -> (base_descriptor fidx ft)#add_assertion ia)
    (collect_called t 0 ft)
