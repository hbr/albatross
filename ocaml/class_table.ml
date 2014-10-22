(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term
open Signature
open Container
open Printf

type formal = int * type_term


type base_descriptor = { hmark:    header_mark;
                         tvs:      Tvars.t;
                         mutable fmap:  int Term_table2.t Feature_map.t;
                         mutable fset:  IntSet.t;
                         mutable def_features: int list;
                         mutable eff_features: int list;
                         mutable def_asserts:  int list;
                         mutable eff_asserts:  int list;
                         mutable descendants:  IntSet.t;
                         mutable ancestors: type_term array IntMap.t}


type descriptor      = { mutable mdl:  int;
                         name: int;
                         priv: base_descriptor;
                         mutable publ: base_descriptor option}

type t = {mutable map:   int IntMap.t;
          seq:           descriptor seq;
          mutable base:  int IntMap.t; (* module name -> class index *)
          mt:            Module_table.t}




let dummy_index     = 0
let boolean_index   = 1
let any_index       = 2
let predicate_index = 3
let function_index  = 4
let tuple_index     = 5


let module_table (ct:t): Module_table.t = ct.mt

let has_current_module (ct:t): bool = Module_table.has_current ct.mt

let current_module (ct:t): int =
  assert (has_current_module ct);
  Module_table.current ct.mt

let count_modules (ct:t): int = Module_table.count ct.mt

let find_module (name:int*int list) (ct:t): int =
  Module_table.find name ct.mt

let used_modules (mdl:int) (ct:t): IntSet.t =
  Module_table.used mdl ct.mt

let module_name (mdl:int) (ct:t): string = Module_table.name mdl ct.mt

let is_private (ct:t): bool = Module_table.is_private ct.mt
let is_public (ct:t):  bool = Module_table.is_public ct.mt
let is_interface_check  (ct:t): bool = Module_table.is_interface_check ct.mt
let is_interface_use (ct:t): bool = Module_table.is_interface_use ct.mt


let count (ct:t):int =
  Seq.count ct.seq

let class_symbol (i:int) (ct:t): int =
  assert (i<count ct);
  (Seq.elem i ct.seq).name

let class_name (i:int) (ct:t): string =
  ST.string (class_symbol i ct)


let standard_bdesc (hm:header_mark) (nfgs:int) (tvs:Tvars.t) (idx:int)
    : base_descriptor =
  let args = Array.init nfgs (fun i -> Variable i) in
  let anc  = IntMap.singleton idx args in
  {hmark = hm;
   tvs   = tvs;
   fmap  = Feature_map.empty;
   fset  = IntSet.empty;
   def_features = [];
   eff_features = [];
   def_asserts  = [];
   eff_asserts  = [];
   descendants  = IntSet.empty;
   ancestors=anc}


let descriptor (idx:int) (ct:t): descriptor =
  assert (idx < count ct);
  Seq.elem idx ct.seq

let base_descriptor (idx:int) (ct:t): base_descriptor =
  assert (0 <= idx);
  assert (idx < count ct);
  let desc = descriptor idx ct in
  if is_private ct then
    desc.priv
  else
    match desc.publ with
      None ->
        printf "class %s is not public\n" (class_name idx ct);
        assert false (* cannot happen in public view *)
    | Some bdesc ->
        bdesc



let add_base_classes (mdl_nme:int) (ct:t): unit =
  try
    let idx = IntMap.find mdl_nme ct.base in
    let desc = Seq.elem idx ct.seq in
    assert (desc.mdl = -1);
    desc.mdl <- current_module ct;
    (*if is_public ct then (
      printf "make base class of module %s public\n" (ST.string mdl_nme);
      desc.publ <- Some desc.priv);*)
    ct.map <- IntMap.add desc.name idx ct.map
  with Not_found ->
    ()

let add_used_module (name:int*int list) (used:IntSet.t) (ct:t): unit =
  Module_table.add_used name used ct.mt;
  add_base_classes (fst name) ct


let add_current_module (name:int) (used:IntSet.t) (ct:t): unit =
  Module_table.add_current name used ct.mt;
  add_base_classes name ct

let set_interface_check (used:IntSet.t) (ct:t): unit =
  Module_table.set_interface_check used ct.mt;
  ct.map <- IntMap.empty;
  let mdl = current_module ct in
  for i = 0 to count ct - 1 do
    let desc = descriptor i ct in
    if desc.mdl = mdl || IntSet.mem desc.mdl used then
      ct.map <- IntMap.add desc.name i ct.map
  done

let descendants (i:int) (ct:t): IntSet.t =
  assert (i < count ct);
  (base_descriptor i ct).descendants

let class_type (i:int) (ct:t): type_term * Tvars.t =
  assert (i < count ct);
  let bdesc = base_descriptor i ct in
  let nfgs  = Tvars.count_fgs bdesc.tvs in
  let tp =
    if nfgs = 0 then
      Variable i
    else
      Application(Variable (i+nfgs), Array.init nfgs (fun i -> Variable i))
  in
  tp, bdesc.tvs


let split_type_term (tp:type_term): int * type_term array =
  match tp with
    Variable i -> i, [||]
  | Application (Variable i,args) -> i, args
  | _ -> assert false


let combine_type_term (cls_idx:int) (args: type_term array): type_term =
  if 0 < Array.length args then
    Application (Variable cls_idx, args)
  else
    Variable cls_idx


let to_tuple (ntvs:int) (args:type_term array): type_term =
  let n = Array.length args in
  assert (n > 0);
  let rec tuple (i:int) (tp:type_term): type_term =
    assert (0 <= i);
    if i = 0 then
      tp
    else
      let i = i - 1 in
      let tp = Application(Variable (ntvs+tuple_index),[|args.(i);tp|]) in
      tuple i tp
  in
  tuple (n-1) args.(n-1)



let to_dummy (ntvs:int) (s:Sign.t): type_term =
  assert (Sign.has_result s);
  if Sign.arity s = 0 then
    let res = Sign.result s in
    let cls,args = split_type_term res in
    if cls = ntvs+predicate_index || cls = ntvs+function_index then
      Application(Variable (ntvs+dummy_index), args)
    else
      res
  else
    let tup = to_tuple ntvs (Sign.arguments s) in
    Application(Variable (ntvs+dummy_index), [|tup;Sign.result s|])


let boolean_type (ntvs:int)  = Variable (boolean_index+ntvs)
let any (ntvs:int)           = Variable (any_index+ntvs)
let func nb dom ran = Application(Variable(nb+function_index),[|dom;ran|])


let result_type_of_compound (tp:type_term) (ntvs:int): type_term =
  let cls_idx,args = split_type_term tp in
  if cls_idx = ntvs + predicate_index then begin
    assert (Array.length args = 1);
    boolean_type ntvs
  end else if cls_idx = ntvs + function_index ||
              cls_idx = ntvs + dummy_index
  then begin
    assert (Array.length args = 2);
    args.(1)
  end else
    raise Not_found



let is_boolean_binary (s:Sign.t) (ntvs:int): bool =
  (Sign.is_binary s) &&
  (Sign.arg_type 0 s) = (boolean_type ntvs) &&
  (Sign.arg_type 1 s) = (boolean_type ntvs) &&
  (Sign.result s)     = (boolean_type ntvs)

let is_boolean_unary (s:Sign.t) (ntvs:int): bool =
  (Sign.is_unary s) &&
  (Sign.arg_type 0 s) = (boolean_type ntvs) &&
  (Sign.result s)     = (boolean_type ntvs)



let type2string (t:term) (nb:int) (fgnames: int array) (ct:t): string =
  (** Convert the type term [t] in an environment with [nb] type variables
      and the formal generics [fgnames] to a string.
   *)
  let nfgs = Array.length fgnames
  in
  let rec to_string(t:term) (nb:int) (prec:int): string =
    let args_to_string (tarr:term array) (nb:int): string =
      "["
      ^ (String.concat ","
           (Array.to_list (Array.map (fun t -> to_string t nb 1) tarr)))
      ^ "]"
    in
    let inner_prec, str =
      match t with
        Variable j ->
          1,
          if j<nb then
            string_of_int j
          else if j < nb+nfgs then
            ST.string fgnames.(j-nb)
          else class_name (j-nb-nfgs) ct
      | Application (Variable j,tarr) ->
          let j1 = j-nb-nfgs
          and tarrlen = Array.length tarr in
          if j1 = predicate_index then begin
            assert (tarrlen=1);
            1, ((to_string tarr.(0) nb 1) ^ "?")
          end else if j1 = function_index then begin
            assert (tarrlen=2);
            1, ((to_string tarr.(0) nb 2) ^ "->" ^ (to_string tarr.(1) nb 1))
          end else if j1 = tuple_index then begin
            assert (tarrlen=2);
            0, ((to_string tarr.(0) nb 1) ^ "," ^ (to_string tarr.(1) nb 0))
          end else begin
            1,
            (to_string (Variable j) nb 1) ^ (args_to_string tarr nb)
          end
      | Application (class_exp,args) -> assert false (*not yet implemented*)
      | Lam (len,names,t) ->
          assert false (*nyi*)
          (*let len = Array.length arr in
          1,
          (args_to_string arr nb) ^ (to_string t (nb+len) 1)*)
    in
    if inner_prec < prec then "(" ^ str ^ ")" else str
  in
  to_string t nb 0


let string_of_type (tp:type_term) (tvs:Tvars.t) (ct:t): string =
  type2string tp (Tvars.count tvs) (Tvars.fgnames tvs) ct


let string_of_concepts (tvs:Tvars.t) (ct:t): string =
  let cpt_lst = Array.to_list (Tvars.concepts tvs) in
  String.concat
     ","
     (List.map (fun tp -> string_of_type tp tvs ct) cpt_lst)


let string_of_fgconcepts (tvs:Tvars.t) (ct:t): string =
  let cptsarr = Myarray.combine (Tvars.fgnames tvs) (Tvars.fgconcepts tvs) in
  let lst = Array.to_list cptsarr in
  String.concat
    ","
    (List.map (fun (n,tp) ->
      (ST.string n) ^ ":" ^ (string_of_type tp tvs ct)) lst)


let string_of_tvs (tvs:Tvars.t) (ct:t): string =
  let str1 =
    if Tvars.count_local tvs = 0 then
      ""
    else
      string_of_int (Tvars.count_local tvs)
  and str2 = string_of_concepts tvs ct
  and str3 = string_of_fgconcepts tvs ct in
  let strcpts =
    if str2="" && str3="" then
      ""
    else if str3="" then
      "[" ^ str2 ^ "]"
    else if str2="" then
      "[" ^ str3 ^ "]"
    else
      "[" ^ str2 ^ "," ^ str3 ^ "]"
  in
  str1 ^ strcpts


let string_of_sub (sub:Term_sub.t) (tvs:Tvars.t) (ct:t): string =
  let lst = Term_sub.to_list sub in
  let str =
    String.concat ","
      (List.map
         (fun (i,t) ->
           (string_of_int i) ^ ":=" ^ (string_of_type t tvs ct))
         lst)
  in
  "[" ^ str ^ "]"



let string_of_tvs_sub (tvs:TVars_sub.t) (ct:t): string =
  let subs = TVars_sub.subs tvs
  and tvs  = TVars_sub.tvars tvs in
  let subsstr =
    String.concat ","
      (List.map
         (fun (i,t1,t2) ->
           (string_of_int i) ^ ":=" ^
           (string_of_type t1 tvs ct) ^
           "(" ^ (string_of_type t2 tvs ct) ^ ")"
         ) subs)
  in
  let subsstr = if subsstr = "" then "" else "[" ^ subsstr ^ "]" in
  (string_of_tvs tvs ct) ^ subsstr



let find_base (cn:int) (findall:bool) (ct:t): int =
  let idx = IntMap.find cn ct.map in
  if findall || is_private ct then
    idx
  else
    match (descriptor idx ct).publ with
      None -> printf "\tnot found\n"; raise Not_found
    | Some _ -> idx


let find_2 (cn:int) (ct:t): int = find_base cn true ct

let find (cn: int) (ct:t): int = find_base cn false ct


let extract_from_tuple
    (nargs:int) (ntvs:int) (tp:type_term): type_term array =
  assert (0 < nargs);
  let tup_idx = ntvs + tuple_index in
  let rec extract
      (n:int) (tp:type_term) (lst:type_term list): type_term list =
    let cls_idx, args = split_type_term tp in
    if 2 <= n && cls_idx = tup_idx then
      extract (n-1) args.(1) (args.(0)::lst)
    else
      raise Not_found
  in
  if nargs = 1 then
    [|tp|]
  else
    let lst = extract nargs tp [] in
    Array.of_list (List.rev lst)





let downgrade_signature
    (ntvs:int) (sign:Sign.t) (nargs:int): Sign.t =
  assert (Sign.arity sign < nargs);
  if not (Sign.is_constant sign || Sign.arity sign = 1) then
    raise Not_found;
  let pred_idx = predicate_index + ntvs
  and func_idx = function_index  + ntvs
  and dum_idx  = dummy_index     + ntvs
  in
  if Sign.is_constant sign then
    let tp = Sign.result sign in
    let cls_idx,args = split_type_term tp in
    if cls_idx < ntvs then
      raise Not_found
    else if cls_idx = pred_idx then begin
      assert (Array.length args = 1);
      Sign.make_func
        (extract_from_tuple nargs ntvs args.(0))
        (boolean_type ntvs)
    end else if cls_idx = func_idx || cls_idx = dum_idx then begin
      assert (Array.length args = 2);
      Sign.make_func
        (extract_from_tuple nargs ntvs args.(0))
        args.(1)
    end else
      raise Not_found
  else begin
    let args, rt = Sign.arguments sign, Sign.result_type sign in
    assert (Array.length args = 1);
    let args = extract_from_tuple nargs ntvs args.(0) in
    Sign.make args rt
  end






let check_class_formal_generic
    (i:info) (nme:int) (tp1:term) (tp2:term)
    (ct:t)
    : unit =
  (** Check if the constraint [tp1] of the formal generic [nme] is equal to
      [tp2] *)
    if tp1 <> tp2 then
      error_info
        i
        ("Formal generic " ^ (ST.string nme) ^
         " must satisfy " ^ (type2string tp2 0 [||] ct))



let update_base_descriptor
    (hm:    header_mark withinfo)
    (fgens: formal_generics)
    (desc:  base_descriptor)
    (ct:    t)
    : unit =
  if hm.v <> desc.hmark then
    (let str =
      "Header mark should be \""
      ^ (hmark2string desc.hmark)
      ^ "\"\n"
    in
    error_info hm.i str);
  let fgs = Module_table.class_formal_generics fgens ct.mt in
  let fgnames    = Tvars.fgnames desc.tvs
  in
  let nfgs = Array.length fgnames in
  if nfgs <> Array.length fgs then
    (let str = "Class must have " ^ (string_of_int nfgs) ^ " formal generics" in
    error_info fgens.i str);
  for i = 0 to nfgs-1 do
    let nme,tp1 = fgs.(i)
    and tp2     = Tvars.concept i desc.tvs in
    let tp1 = Term.up nfgs tp1 in
    check_class_formal_generic fgens.i nme tp1 tp2 ct;
    fgnames.(i) <- nme
  done




let export
    (idx:   int)
    (hm:    header_mark withinfo)
    (fgens: formal_generics)
    (ct:    t)
    : unit =
  let desc = Seq.elem idx ct.seq in
  let hm1, hm2 = desc.priv.hmark, hm.v in
  begin
    match hm1, hm2 with
      Case_hmark, Immutable_hmark -> ()
    | _, _ when hm1=hm2 -> ()
    | _, _ ->
        error_info
          hm.i
          ("Header mark is not consistent with private header mark \"" ^
           (hmark2string hm1))
  end;
  let fgs  = Module_table.class_formal_generics fgens ct.mt in
  let nfgs = Array.length fgs in
  let fgconcepts = Tvars.fgconcepts desc.priv.tvs in
  if nfgs > Array.length fgconcepts then
    error_info fgens.i "More formal generics than in private definition";
  for i = 0 to nfgs-1 do
    let tp1     = fgconcepts.(i)
    and nme,tp2 = fgs.(i) in
    let tp2 = Term.up nfgs tp2 in
    if tp1 <> tp2 then
      error_info
        fgens.i
        ("The constraint of " ^ (ST.string nme) ^
         " is not consistent with private definition");
  done;
  desc.publ <-
    let fgnames,concepts = Myarray.split fgs in
    let concepts = Array.map (fun tp -> Term.up nfgs tp) concepts in
    let tvs = Tvars.make_fgs fgnames concepts in
    let bdesc = standard_bdesc hm2 nfgs tvs idx in
    Some bdesc





let update
    (idx:   int)
    (hm:    header_mark withinfo)
    (fgens: formal_generics)
    (ct:    t)
    : unit =
  assert (has_current_module ct);
  let desc = Seq.elem idx ct.seq
  and mdl  = Module_table.current ct.mt
  in
  if desc.mdl = -1 || desc.mdl = mdl then begin
    if desc.mdl = -1 then
      desc.mdl <- mdl;
    if is_private ct then
      update_base_descriptor hm fgens desc.priv ct
    else
      match desc.publ with
        None ->       export idx hm fgens ct
      | Some bdesc -> update_base_descriptor hm fgens bdesc ct
  end
  else
    () (* cannot update a class from a different module *)



let find_features
    (f:(feature_name*type_term*int))
    (cls:int)
    (ct:t)
    : (int*Term_sub.t) list =
  assert (cls < count ct);
  let fn,tp,ntvs = f in
  let bdesc = base_descriptor cls ct in
  try
    let tab = Feature_map.find fn bdesc.fmap in
    Term_table2.unify_with tp ntvs 0 tab
  with Not_found ->
    []


let add_feature_bdesc
    (f:(int*feature_name*type_term*int))
    (is_deferred:bool)
    (bdesc:base_descriptor)
    :unit =
  let fidx,fn,tp,nfgs = f in
  let tab =
    try Feature_map.find fn bdesc.fmap
    with Not_found ->
      let tab = Term_table2.make () in
      bdesc.fmap <- Feature_map.add fn tab bdesc.fmap;
      tab
  in
  assert (Feature_map.mem fn bdesc.fmap);
  if IntSet.mem fidx bdesc.fset then
    ()
  else begin
    if is_deferred then
      bdesc.def_features <- fidx :: bdesc.def_features
    else
      bdesc.eff_features <- fidx :: bdesc.eff_features;
    Term_table2.add tp nfgs 0 fidx tab;
    bdesc.fset <- IntSet.add fidx bdesc.fset
  end




let add_feature
    (f:(int*feature_name*type_term*int))
    (cidx:int)
    (is_deferred:bool)
    (priv_only: bool)
    (ct:t)
    : unit =
  assert (cidx < count ct);
  if priv_only || is_private ct then
    add_feature_bdesc f is_deferred (descriptor cidx ct).priv
  else begin
    add_feature_bdesc f is_deferred (descriptor cidx ct).priv;
    add_feature_bdesc f is_deferred (base_descriptor cidx ct)
  end


let add_assertion_bdesc (aidx:int) (is_deferred:bool) (bdesc:base_descriptor)
    : unit =
  if is_deferred then
    bdesc.def_asserts <- aidx :: bdesc.def_asserts
  else
    bdesc.eff_asserts <- aidx :: bdesc.eff_asserts


let add_assertion (aidx:int) (cidx:int) (is_deferred:bool) (ct:t)
    : unit =
  (** Add the assertion [aidx] to the class [cidx] as deferred or effecitive
      assertion depending on [is_deferred].  *)
  assert (cidx < count ct);
  let bdesc = base_descriptor cidx ct in
  if is_private ct then
    add_assertion_bdesc aidx is_deferred bdesc
  else begin
    add_assertion_bdesc aidx is_deferred bdesc;
    add_assertion_bdesc aidx is_deferred (descriptor cidx ct).priv
  end



let deferred_features (cidx:int) (ct:t): int list =
  assert (cidx < count ct);
  (base_descriptor cidx ct).def_features


let effective_features (cidx:int) (ct:t): int list =
  assert (cidx < count ct);
  (base_descriptor cidx ct).eff_features


let deferred_assertions (cidx:int) (ct:t): int list =
  assert (cidx < count ct);
  (base_descriptor cidx ct).def_asserts


let effective_assertions (cidx:int) (ct:t): int list =
  assert (cidx < count ct);
  (base_descriptor cidx ct).eff_asserts


let add
    (hm:    header_mark withinfo)
    (cn:    classname)
    (fgens: formal_generics)
    (ct:    t)
    : unit =
  let fgs = Module_table.class_formal_generics fgens ct.mt in
  let idx  = count ct
  and nfgs = Array.length fgs
  and fgnames,concepts = Myarray.split fgs
  in
  let concepts = Array.map (fun tp -> Term.up nfgs tp) concepts in
  let tvs  = Tvars.make_fgs fgnames concepts in
  let bdesc = standard_bdesc hm.v nfgs tvs idx
  and bdesc_opt =
    if is_public ct then Some (standard_bdesc hm.v nfgs tvs idx) else None
  in
  Seq.push
    {mdl  = current_module ct;
     name = snd cn.v;
     priv = bdesc;
     publ = bdesc_opt}
    ct.seq;
    ct.map <- IntMap.add (snd cn.v) idx ct.map



let owner (tvs:Tvars.t) (s:Sign.t) (ct:t): int =
  let max (cidx1:int) (cidx2:int): int =
    if cidx1 = cidx2 then
      cidx1
    else
      let mdl1 = (descriptor cidx1 ct).mdl
      and mdl2 = (descriptor cidx2 ct).mdl in
      if mdl1 = mdl2 then
        assert false (* nyi: multiple classes in the same module *)
      else
        if mdl1 < mdl2 then cidx2 else cidx1
  in
  let set = Sign.involved_classes tvs s in
  IntSet.fold
    (fun i idx_max -> if idx_max = -1 then i else max i idx_max)
    set
    (-1)


let anchored (tvs:Tvars.t) (cls:int) (ct:t): int array =
  let nfgs = Tvars.count_all tvs
  in
  let anch = ref [] in
  for i = 0 to nfgs - 1 do
    let pcls = Tvars.principal_class (Variable i) tvs in
    if pcls = cls then
        anch := i :: !anch;
  done;
  Array.of_list (List.rev !anch)


let check_deferred  (owner:int) (nanchors:int) (info:info) (ct:t): unit =
  let desc  = descriptor owner ct
  and bdesc = base_descriptor owner ct in
  let mdl = current_module ct in
  (match bdesc.hmark with
    Deferred_hmark -> ()
  | _ ->
      error_info info
        ("The owner class " ^ (class_name owner ct) ^ " is not deferred")
  );
  if mdl <> desc.mdl then
    error_info info
      ("Can be defined only in the module \"" ^
       (Module_table.name desc.mdl ct.mt) ^
       "\" of the owner class " ^
       (class_name owner ct))
  else if not (IntSet.is_empty bdesc.descendants) then
    error_info info
      ("Owner class " ^ (class_name owner ct) ^" has already descendants")
  else if nanchors <> 1 then
    error_info info
      ("There must be a unique formal generic anchored to the owner class " ^
       (class_name owner ct))




let rec satisfies
    (tp1:type_term) (tvs1:Tvars.t) (tp2:type_term) (tvs2:Tvars.t) (ct:t)
    : bool =
  let ntvs1 = Tvars.count_local tvs1
  and nall1 = Tvars.count_all   tvs1
  and ntvs2 = Tvars.count_local tvs2
  and nall2 = Tvars.count_all   tvs2
  in
  match tp1, tp2 with
    Variable i, Variable j when i < ntvs1 ->
      assert false (* shall never happen *)
  | Variable i, Variable j when j < ntvs2 ->
      true
  | Variable i, Variable j when i < nall1 ->
      let tp1 = Tvars.concept i tvs1 in
      satisfies tp1 tvs1 tp2 tvs2 ct
  | Variable i, Variable j when j < nall2 ->
      let tp2 = Tvars.concept j tvs2 in
      satisfies tp1 tvs1 tp2 tvs2 ct
  | _ ->
      let idx1,args1 = split_type_term tp1
      and idx2,args2 = split_type_term tp2 in
      let bdesc1 = base_descriptor (idx1-nall1) ct in
      try
        let anc_args = IntMap.find (idx2-nall2)  bdesc1.ancestors in
        let nargs    = Array.length anc_args in
        assert (nargs = Array.length args2);
        let anc_args = Array.map (fun t -> Term.sub t args1 nall1) anc_args
        in
        for i = 0 to nargs-1 do
          if satisfies anc_args.(i) tvs1 args2.(i) tvs2 ct then
            ()
          else
            raise Not_found
        done;
        true
      with Not_found ->
        false




let valid_type
    (cls_idx:int)
    (args: type_term array)
    (info: info)
    (tvs:  Tvars.t)
    (ct:t): type_term =
  (* The valid type term [cls_idx[args.(0),args.(1),...] in a type environment
     [tvs].

     If the type term is not valid then [Not_found] is raised.

     To check: Do all actual generics [args] satisfy their corresponding
     concepts? *)
  let ntvs  = Tvars.count tvs
  and nall  = Tvars.count_all tvs
  and nargs = Array.length args in
  if cls_idx < ntvs then begin
    assert false (* shall never happen *)
  end else if cls_idx < nall then begin
    if nargs <> 0 then
      error_info info "Generics cannot have actual generics"
    else
      Variable cls_idx
  end else begin
    let cls_idx_0 = cls_idx - nall in
    let bdesc = base_descriptor cls_idx_0 ct in
    let fgconcepts = Tvars.fgconcepts bdesc.tvs in
    if nargs <> Array.length fgconcepts then
      error_info info "number of actual generics wrong";
    for i = 0 to nargs-1 do
      if satisfies args.(i) tvs fgconcepts.(i) bdesc.tvs ct then
        ()
      else
        error_info info ("actual generic #" ^ (string_of_int i) ^
                         " does not satisfy the required concept")
    done;
    if nargs = 0 then
      Variable cls_idx
    else
      Application (Variable cls_idx, args)
  end



let class_index (name:int) (tvs:Tvars.t) (info:info) (ct:t): int =
  let ntvs    = Tvars.count tvs
  and fgnames = Tvars.fgnames tvs
  and nall    = Tvars.count_all tvs
  in
  try
      ntvs + Search.array_find_min (fun n -> n=name) fgnames
  with Not_found ->
    try
      nall + (find name ct)
    with Not_found ->
        error_info info ("Class " ^ (ST.string name)
                         ^ " does not exist")


let get_type
    (tp:type_t withinfo)
    (tvs: Tvars.t)
    (ct:t)
    : term =
  (* Convert the syntactic type [tp] in an environment with the [tvs] type
     variables and the formal generics [fgnames,concepts] into a type term *)
  let n = Tvars.count_all tvs
  in
  let class_index0 (name:int): int = class_index name tvs tp.i ct
  in
  let info = tp.i in
  let rec get_tp (tp:type_t): type_term =
    let valid_tp (idx:int) (args:type_term array): type_term =
        valid_type idx args info tvs ct
    in
    let rec tuple (tp_list: type_t list): type_term =
      let ta, tb =
        match tp_list with
          [tpa;tpb] ->
            get_tp tpa, get_tp tpb
        | tpa::tail ->
            get_tp tpa, tuple tail
        | _ ->
            assert false (* tuple type must have at least two types *)
      in
      valid_tp (n+tuple_index) [|ta;tb|]
    in
    match tp with
      Normal_type (path,name,actuals) ->
        let args = List.map (fun tp -> get_tp tp) actuals in
        let args = Array.of_list args in
        valid_tp (class_index0 name) args
    | Paren_type tp ->
        get_tp tp
    | QMark_type tp ->
        let t = get_tp tp in
        valid_tp (n+predicate_index) [|t|]
    | Arrow_type (tpa,tpb) ->
        let ta = get_tp tpa
        and tb = get_tp tpb in
        valid_tp (n+function_index) [|ta;tb|]
    | Tuple_type tp_lst ->
        tuple tp_lst
  in
  get_tp tp.v






let has_ancestor (cls:int) (anc:int) (ct:t): bool =
  (** Does the class [cls] have [anc] as an ancestor ? *)
  cls = anc ||
  let bdesc = base_descriptor cls ct in
  IntMap.mem anc bdesc.ancestors






let parent_type (cls:int) (tp:type_t withinfo) (ct:t)
    : int * type_term array =
  assert (cls < count ct);
  let tvs = (base_descriptor cls ct).tvs
  in
  let tp_term = get_type tp tvs ct
  and n = Tvars.count_all tvs
  in
  let i, args = split_type_term tp_term
  in
  begin
    if i < n then
      error_info tp.i "Formal generic not allowed as parent class"
    else
      if is_private ct && (descriptor cls ct).mdl <> current_module ct then
        let str =
          "Cannot inherit to " ^ (class_name cls ct) ^
          " in the implementation file of module \"" ^
          (module_name (current_module ct) ct) ^
          "\"" in
        error_info tp.i str
  end;
  i-n, args





let inherited_ancestors
    (cls_idx:int)
    (par_idx:int)
    (par_args:type_term array)
    (info:info)
    (ct:t)
    : (int * type_term array) list * (int * type_term array) list =
  let par_bdesc = base_descriptor par_idx ct
  and cls_bdesc = base_descriptor cls_idx ct in
  let cls_nfgs  = Tvars.count_fgs cls_bdesc.tvs in
  assert (IntSet.is_empty cls_bdesc.descendants); (* nyi: inheritance to
                                                     descendants*)
  let res = IntMap.fold
    (fun anc_idx anc_args lst->
      let anc_args: type_term array =
        Array.map (fun t -> Term.sub t par_args cls_nfgs) anc_args in
      try
        let anc_args_0 = IntMap.find anc_idx cls_bdesc.ancestors in
        if anc_args <> anc_args_0 then
          error_info info
            ("Cannot inherit "  ^
             (class_name anc_idx ct) ^
             " with different actual generics")
        else
          lst
      with Not_found ->
        (anc_idx,anc_args) :: lst)
    par_bdesc.ancestors
    []
  in
  if is_interface_check ct then
    let cls_bdesc_priv = (descriptor cls_idx ct).priv in
    List.partition
        (fun (anc_idx,anc_args) ->
          try
            let anc_args_0 = IntMap.find anc_idx cls_bdesc_priv.ancestors in
            if anc_args <> anc_args_0 then
              error_info info
                ("Cannot inherit "  ^
                 (class_name anc_idx ct) ^
                 " with different actual generics than inherited privately")
            else
              false
          with Not_found ->
            true)
        res
  else
    res, []




let one_inherit
    (cls_idx: int)
    (cls_bdesc:base_descriptor)
    (anc_idx: int)
    (anc_args: type_term array)
    (anc_bdesc:base_descriptor)
    : unit =
  cls_bdesc.ancestors <-
    IntMap.add anc_idx anc_args cls_bdesc.ancestors;
  assert (not (IntSet.mem cls_idx anc_bdesc.descendants));
  anc_bdesc.descendants <- IntSet.add cls_idx anc_bdesc.descendants



let do_inherit
    (cls_idx:int)
    (anc_lst: (int*type_term array) list)
    (ct:t)
    : unit =
  if is_public ct then begin
    let cls_bdesc = (descriptor cls_idx ct).priv in
    List.iter
      (fun (anc_idx,anc_args) ->
        let anc_bdesc = (descriptor anc_idx ct).priv in
        one_inherit cls_idx cls_bdesc anc_idx anc_args anc_bdesc)
      anc_lst
  end;
  let cls_bdesc = base_descriptor cls_idx ct in
  List.iter
    (fun (anc_idx,anc_args) ->
      let anc_bdesc = base_descriptor anc_idx ct in
      one_inherit cls_idx cls_bdesc anc_idx anc_args anc_bdesc)
    anc_lst


let export_inherited
    (cls_idx:int)
    (anc_lst: (int*type_term array) list)
    (ct:t)
    : unit =
  assert (anc_lst <> [] );
  assert (is_interface_check ct);
  let cls_bdesc = base_descriptor cls_idx ct in
  List.iter
    (fun (anc_idx,anc_args) ->
      let anc_bdesc = base_descriptor anc_idx ct in
      one_inherit cls_idx cls_bdesc anc_idx anc_args anc_bdesc)
    anc_lst



let put_formal (name: int withinfo) (concept: type_t withinfo) (ct:t): unit =
  (** Add the formal generic with [name] and [concept] to the formal generics
      of the class table [ct] *)
  let cpt = get_type concept Tvars.empty ct in
  Module_table.put_formal name cpt ct.mt






let formal_arguments
    (entlst: entities list withinfo)
    (tvs:Tvars.t)
    (ct:t)
    : formal array =
  (** The formal arguments of the entity list [entlst] in an environment with
      the formal generics [fgnames,concepts] and [ntvs] type variables *)
  let fargs (es: entities): formal list =
    match es with
      Untyped_entities lst ->
        assert (List.length lst <= Tvars.count_local tvs);
        List.mapi (fun i name -> name, Variable i) lst
    | Typed_entities (lst,tp) ->
        let t =
          get_type
            (withinfo entlst.i tp)
            tvs
            ct in
        List.map (fun name -> name,t) lst
  in
  let arglst = List.concat (List.map fargs entlst.v) in
  Array.of_list arglst



let result_type
    (rt:return_type)
    (tvs:Tvars.t)
    (ct:t)
    : Result_type.t =
  (** The result type which corresponds to the return type [rt] in an
      environment with the formal generics [fgnames,concepts] and [ntvs] type
      variables *)
  match rt with
    None -> Result_type.empty
  | Some tpinf ->
      let tp,proc,ghost = tpinf.v in
      let t =
        get_type (withinfo tpinf.i tp) tvs ct
      in
      Result_type.make t proc ghost



let empty_table (): t =
  let cc = Seq.empty ()
  in
  {map   = IntMap.empty;
   seq   = cc;
   base  = IntMap.empty;
   mt=Module_table.make ()}





let add_base_class
    (name:string)
    (hm:  header_mark)
    (fgs: formal array)
    (ct:t)
    : unit =
  let idx  = count ct
  and nfgs = Array.length fgs
  and nme  = ST.symbol name
  and fgnames,concepts = Myarray.split fgs
  in
  let concepts = Array.map (fun tp -> Term.up nfgs tp) concepts in
  let tvs  = Tvars.make_fgs fgnames concepts in
  let bdesc = standard_bdesc hm nfgs tvs idx
  and bdesc_opt =
    if is_public ct then Some (standard_bdesc hm nfgs tvs idx) else None
  in
  Seq.push
    {mdl=(-1);
     name = nme;
     priv = bdesc;
     publ = bdesc_opt}
    ct.seq;
  let mdl_nme = ST.symbol (String.lowercase name) in
  assert (not (IntMap.mem mdl_nme ct.base));
  ct.base <- IntMap.add mdl_nme idx ct.base




let check_base_classes (ct:t): unit =
  assert (tuple_index < (count ct));
  assert ((class_name boolean_index   ct) = "BOOLEAN");
  assert ((class_name any_index       ct) = "ANY");
  assert ((class_name predicate_index ct) = "PREDICATE");
  assert ((class_name function_index  ct) = "FUNCTION");
  assert ((class_name tuple_index     ct) = "TUPLE");
  ()




let base_table (): t =
  let fgg = ST.symbol "G"
  and fga = ST.symbol "A"
  and fgb = ST.symbol "B"
  and anycon = Variable any_index
  and ct = empty_table ()   in
  add_base_class "@DUMMY"    Immutable_hmark [||] ct;
  add_base_class "BOOLEAN"   Immutable_hmark [||] ct;
  add_base_class "ANY"       Deferred_hmark  [||] ct;
  add_base_class "PREDICATE" Immutable_hmark [|fgg,anycon|] ct;
  add_base_class "FUNCTION"  Immutable_hmark [|(fga,anycon);(fgb,anycon)|] ct;
  add_base_class "TUPLE"     Immutable_hmark [|(fga,anycon);(fgb,anycon)|] ct;
  check_base_classes ct;
  ct





let string_of_signature
    (s:Sign.t)
    (tvs:Tvars.t)
    (ct:t)
    : string =
  let has_args = (Sign.arity s) <> 0
  and has_res  = Sign.has_result s
  in
  let argsstr =
    if not has_args then ""
    else
      "("
      ^ (String.concat
           ","
           (List.map
              (fun tp -> string_of_type tp tvs ct)
              (Array.to_list (Sign.arguments s))))
      ^ ")"
  and retstr =
    if has_res then
      string_of_type (Sign.result s) tvs ct
    else ""
  and colon = if has_args && has_res then ":" else ""
  in
  argsstr ^ colon ^ retstr


let string_of_complete_signature
    (s:Sign.t)
    (tvs:Tvars.t)
    (ct:t)
    : string =
  (string_of_tvs tvs ct) ^ (string_of_signature s tvs ct)
