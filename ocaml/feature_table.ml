(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Signature
open Printf

module FDef = Feature.Spec

type implementation_status = No_implementation | Builtin | Deferred


type definition = term

type formal     = int * term

type base_descriptor = {
    mutable spec:       Feature.Spec.t;
    mutable level:      int;
    mutable is_inh:     bool;
    mutable seeds:      IntSet.t;
    mutable variants:   int IntMap.t;  (* cls -> fidx *)
    mutable is_eq:      bool (* is equality inherited from ANY *)
  }

type descriptor = {
    mutable mdl: int;             (* -1: base feature, module not yet assigned*)
    cls:         int;             (* owner class *)
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
let not_index:         int =  2
let or_index:          int =  3
let all_index:         int =  4
let some_index:        int =  5
let eq_index:          int =  6
let pparen_index:      int =  7
let domain_index:      int =  8
let fparen_index:      int =  9
let tuple_index:       int = 10
let first_index:       int = 11
let second_index:      int = 12


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



let definition (i:int) (nb:int) (ft:t): term =
  (* The definition of the feature [i] as a lambda term (if there are arguments)
     transformed into an environment with [nb] bound variables. Raises [Not_found]
     in case that there is no definition *)
  assert (nb <= i);
  let i = i - nb in
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  let nargs = Sign.arity desc.sign in
  let t = Feature.Spec.definition_term bdesc.spec in
  let t = Term.upbound nb nargs t in
  if nargs = 0 then t else Lam (nargs,[||],t)
  (*match bdesc.definition with
    None -> raise Not_found
  | Some t ->
      let t = Term.upbound nb nargs t in
      if nargs = 0 then t else Lam (nargs,[||],t)*)




let has_definition (i:int) (ft:t): bool =
  try let _ = definition i 0 ft in true
  with Not_found -> false



let owner (i:int) (ft:t): int =
  assert (i < count ft);
  (descriptor i ft).cls


let function_level (i:int) (ft:t): int =
  assert (i < count ft);
  (base_descriptor i ft).level




let term_level (t:term) (nb:int) (ft:t): int =
  Term.fold
    (fun level i ->
      if nb <= i then
        let ilev = function_level (i-nb) ft in
        if level < ilev then ilev else level
      else level
    )
    0
    t


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
    | Lam (n,_,t) ->
        is_ghost t (nb+n)
    | Application (f,args) ->
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
  let level =
    try let t = Feature.Spec.definition_term spec in 1 + term_level t nb ft
    with Not_found -> 0
  in
  {is_inh     = false;
   seeds      = IntSet.singleton i;     (* each feature is its own seed *)
   variants   = IntMap.singleton cls i; (* and own variant in its owner class *)
   level      = level;
   spec       = spec;
   is_eq      = false}


let count_fgs (i:int) (ft:t): int =
  assert (i < count ft);
  Tvars.count_fgs (descriptor i ft).tvs


let anchor (i:int) (ft:t): int =
  let desc = descriptor i ft in
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




let variant_term (t:term) (nb:int) (base_cls:int) (cls:int) (ft:t): term =
  assert (Class_table.has_ancestor cls base_cls ft.ct);
  let f (j:int): term =
    let var_j =
      if class_of_feature j ft = base_cls && has_anchor j ft then
        try variant j cls ft
        with Not_found ->
          assert false (* If [cls] inherits [base_cls] then there has to be a variant
                          in the descendant *)
      else
        j
    in
    Variable var_j
  in
  Term.map_free f t nb



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
    else Application (Variable f_id, Array.init nargs (fun i -> Variable i))
  in
  let eq_term = Term.binary eq_id f t in
  if nargs = 0 then
    eq_term
  else
    Term.quantified all_index nargs desc.argnames eq_term



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



let export_feature (i:int) (ft:t): unit =
  (* Export the feature [i] unless it is already publicly available. *)
  assert (i < count ft);
  let desc = descriptor i ft in
  match desc.pub with
    None ->
      let nargs = Array.length desc.argnames in
      desc.pub <- Some (standard_bdesc i desc.cls desc.priv.spec nargs ft)
  | Some _ ->
      ()



let add_class_feature (i:int) (priv_only:bool) (base:bool) (ft:t): unit =
  (* Add the feature [i] as a class feature to the corresponding owner
     class. *)
  assert (i < count ft);
  let desc  = Seq.elem i ft.seq in
  Class_table.add_feature
    (i, desc.fname, desc.tp, Tvars.count_all desc.tvs)
    desc.cls
    (is_desc_deferred desc)
    priv_only
    base
    ft.ct



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
  let p_tp  = Application (Variable (Class_table.predicate_index+1),
                           [|g_tp|])
  and p_tp2 = Application (Variable (Class_table.predicate_index+2),
                           [|a_tp|])
  and f_tp  = Application (Variable (Class_table.function_index+2),
                           [|a_tp;b_tp|])
  and tup_tp= Application (Variable (Class_table.tuple_index+2),
                           [|a_tp;b_tp|])
  and spec_none = Feature.Spec.make_func None [] []
  and spec_term t = Feature.Spec.make_func (Some t) [] []
  and spec_pre t  = Feature.Spec.make_func None [t] []
  in
  add_base (* ==> *)
    "boolean" Class_table.boolean_index (FNoperator DArrowop)
    [||] [|bool;bool|] bool false false spec_none ft;

  add_base (* false *)
    "boolean" Class_table.boolean_index FNfalse
    [||] [||] bool false false spec_none ft;

  let imp_id1   = 1 + implication_index
  and false_id1 = 1 + false_index
  and imp_id2   = 2 + implication_index
  and not_id2   = 2 + not_index
  in
  let not_term = Term.binary imp_id1 (Variable 0) (Variable false_id1)
  and or_term =  Term.binary imp_id2 (Term.unary not_id2 (Variable 0)) (Variable 1)
  in
  add_base (* not *)
    "boolean" Class_table.boolean_index (FNoperator Notop)
    [||] [|bool|] bool false false (spec_term not_term) ft;

  add_base (* or *)
    "boolean" Class_table.boolean_index (FNoperator Orop)
    [||] [|bool;bool|] bool false false (spec_term or_term) ft;

  add_base (* all *)
    "boolean" Class_table.predicate_index (FNoperator Allop)
    [|any1|] [|p_tp|] bool1 false true spec_none ft;

  add_base (* some *)
    "boolean" Class_table.predicate_index (FNoperator Someop)
    [|any1|] [|p_tp|] bool1 false true spec_none ft;

  add_base (* equality *)
    "any" Class_table.any_index (FNoperator Eqop)
    [|any1|] [|g_tp;g_tp|] bool1 true false spec_none ft;

  add_base (* predicate application *)
    "predicate" Class_table.predicate_index (FNoperator Parenop)
    [|any1|] [|p_tp;g_tp|] bool1 false false spec_none ft;

  add_base (* domain *)
    "function" Class_table.function_index (FNname ST.domain)
  [|any2;any2|] [|f_tp|] p_tp2 false true spec_none ft;

  let dom2 = domain_index + 2 in
  let fpre = Application (Term.unary dom2 (Variable 0), [|Variable 1|])
  in
  add_base (* function application *)
    "function" Class_table.function_index (FNoperator Parenop)
    [|any2;any2|] [|f_tp;a_tp|] b_tp false false (spec_pre fpre) ft;

  add_base (* tuple *)
    "tuple" Class_table.tuple_index (FNname ST.tuple)
    [|any2;any2|] [|a_tp;b_tp|] tup_tp false false spec_none ft;

  add_base (* first *)
    "tuple" Class_table.tuple_index (FNname ST.first)
    [|any2;any2|] [|tup_tp|] a_tp false false spec_none ft;

  add_base (* second *)
    "tuple" Class_table.tuple_index (FNname ST.second)
    [|any2;any2|] [|tup_tp|] b_tp false false spec_none ft;

  assert ((descriptor implication_index ft).fname = FNoperator DArrowop);
  assert ((descriptor false_index ft).fname       = FNfalse);
  assert ((descriptor not_index ft).fname         = FNoperator Notop);
  assert ((descriptor or_index ft).fname          = FNoperator Orop);
  assert ((descriptor all_index ft).fname         = FNoperator Allop);
  assert ((descriptor some_index ft).fname        = FNoperator Someop );
  assert ((descriptor eq_index ft).fname          = FNoperator Eqop);
  assert ((descriptor pparen_index ft).fname      = FNoperator Parenop);
  assert ((descriptor domain_index ft).fname      = FNname ST.domain);
  assert ((descriptor fparen_index ft).fname      = FNoperator Parenop);
  assert ((descriptor tuple_index ft).fname       = FNname ST.tuple);
  assert ((descriptor first_index ft).fname       = FNname ST.first);
  assert ((descriptor second_index ft).fname      = FNname ST.second);
  ft




let implication_term (a:term) (b:term) (nbound:int) (ft:t)
    : term =
  (* The implication term a=>b in an environment with 'nbound' bound variables
   *)
  let args = [|a;b|] in
  Application (Variable (implication_index+nbound), args)


let preconditions (i:int) (ft:t): term list =
  assert false

let find
    (fn:feature_name)
    (tvs: Tvars.t)
    (tp:type_term)
    (ft:t)
    : int =
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
          if ok then (
            printf "find fn %s\n" (feature_name_to_string fn);
            assert false)
          else
            lst)
      []
      lst
  in
  match idx_lst with
    [] -> raise Not_found
  | idx::rest ->
      assert (List.for_all (fun i -> i=idx) rest);
      idx




let find_with_signature (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t): int =
  (* Find the feature with the characteristics.  *)
  let ntvs = Tvars.count_all tvs in
  let tp   = Class_table.to_dummy ntvs sign in
  find fn tvs tp ft


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
        else if arity = nargs then
          (i,tvs,sign) :: lst
        else if arity < nargs then (* downgrade *)
          try
            let s = Class_table.downgrade_signature nfgs sign nargs in
            (i,tvs,s) :: lst
          with Not_found ->
            lst
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






exception Expand_found

let expand_focus_term_new (t:term) (nb:int) (ft:t): term =
  (* Expand the variable in the focus of [t] within an environment with [nb] bound
     variables (i.e. a variable [i] with [nb<=i] refers to the global feature
     [i-nb])

     A variable is in the focus of [t]:

     - It is the toplevel variable of [t]

     - The toplevel is an application and it is the variable of the function term

     - The toplevel is an application and the function term is not an expandable
       variable and it is the first argument which allows a focussed expansion

     Note: The function doesn't do any beta reductions in the term [t] which
     would have been possible before the expansion. *)
  let apply (f:term) (args:term array): term =
    match f with
      Lam (n,_,t) ->
        assert (n = Array.length args);
        Term.apply t args
    | _ ->
        Application (f,args)
  and def (i:int) = definition (i-nb) nb ft
  in
  let rec expand (t:term) (level:int) (is_arg:bool): term =
    if level > 2 then raise Not_found;
    match t with
      Variable i when nb <= i -> def i
    | Application (f,args) ->
        begin
          try
            let fexp = expand f (level+1) is_arg in
            apply fexp args
          with Not_found ->
            let args = Array.copy args in
            if is_arg then raise Not_found
            else
              try
                Array.iteri
                  (fun i arg ->
                    try
                      let arg_exp = expand arg level true in
                      args.(i) <- arg_exp;
                      raise Expand_found
                    with Not_found -> ())
                  args;
                raise Not_found
              with Expand_found ->
                Application (f,args)
        end
    | _ ->
        raise Not_found
  in
  expand t 0 false



let expand_focus_term_old (t:term) (nb:int) (ft:t): term =
  (* Expand the variable in the focus of [t] within an environment with [nb] bound
     variables (i.e. a variable [i] with [nb<=i] refers to the global feature
     [i-nb])

     A variable is in the focus of [t] if it is the toplevel variable of [t] or
     it is the function term of [t]

     Note: The function doesn't do any beta reductions in the term [t] which
     would have been possible before the expansion. *)
  let apply (f:term) (args:term array): term =
    match f with
      Lam (n,_,t) ->
        assert (n = Array.length args);
        Term.apply t args
    | _ ->
        Application (f,args)
  and def (i:int) = definition (i-nb) nb ft
  in
  let expand (t:term): term =
    match t with
      Variable i when nb <= i -> def i
    | Application (Variable i ,args) when nb <= i->
        apply (def i) args
    | Application (Application (Variable i,args0), args1) ->
        let f = apply (def i) args0 in
        apply f args1
    | _ ->
        raise Not_found
  in
  expand t


let expand_focus_term (t:term) (nb:int) (ft:t): term =
  expand_focus_term_old t nb ft


let term_to_string
    (t:term)
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
      (nanon: int)
      (is_fun: bool)
      (outop: (operator*bool) option)
      : string =
    (* nanon: number of already used anonymous variables
       is_fun: the term is used in a function position
       outop: the optional outer operator and a flag if the current term
              is the left operand of the outer operator
     *)
    let nnames = Array.length names
    and anon2sym (i:int): int = anon_symbol i nanon
    in
    let var2str (i:int): string =
      if i < nnames then
        ST.string names.(i)
      else
        feature_name_to_string
          (Seq.elem (i-nnames) ft.seq).fname
    and find_op (f:term): operator  =
      match f with
        Variable i when nnames <= i ->
          begin
            match (Seq.elem (i-nnames) ft.seq).fname with
              FNoperator op -> op
            | _ -> raise Not_found
          end
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
        nanon, nms
      else
        nanon+n, Array.init n anon2sym
    in
    let lam_strs (n:int) (nms:int array) (t:term): string * string =
      let nanon, nms = local_names n nms in
      let names = Array.append nms names in
      args2str n nms,
      to_string t names nanon false None
    in
    let q2str (qstr:string) (args:term array): string =
      let nargs = Array.length args in
      assert (nargs = 1);
      match args.(0) with
        Lam (n,nms,t) ->
          let argsstr, tstr = lam_strs n nms t in
          qstr ^ "(" ^ argsstr ^ ") " ^ tstr
      | _ ->
          (* very rare case that a quantor is applied directly to a predicate *)
          qstr ^ ".(" ^ (to_string args.(0) names nanon false None) ^ ")"
    in
    let funapp2str (f:term) (argsstr:string): string =
      let default f =
        (to_string f names nanon true None) ^ "(" ^ argsstr ^ ")" in
      match f with
        Variable i when nnames <= i ->
          let fn = (descriptor (i-nnames) ft).fname in
          begin match fn with
            FNname fsym ->
              if fsym = (ST.symbol "singleton") then
                "{" ^ argsstr ^ "}"
              else if fsym = ST.tuple then
                "(" ^ argsstr ^ ")"
              else
                default f
          | _ -> default f
          end
      | _ -> default f
    in
    let op2str (op:operator) (args: term array): string =
      match op with
        Allop  -> q2str "all"  args
      | Someop -> q2str "some" args
      | _ ->
          let nargs = Array.length args in
          if nargs = 1 then
            (operator_to_rawstring op) ^ " "
            ^ (to_string args.(0) names nanon false (Some (op,false)))
          else begin
            assert (nargs=2); (* only unary and binary operators *)
            (to_string args.(0) names nanon false (Some (op,true)))
            ^ " " ^ (operator_to_rawstring op) ^ " "
        ^ (to_string args.(1) names nanon false (Some (op,false)))
          end
    and app2str (f:term) (args: term array): string =
      let argsstr =
        String.concat
          ","
          (List.map
             (fun t -> to_string t names nanon false None)
             (Array.to_list args)) in
      funapp2str f argsstr
      (*(to_string f names nanon true None) ^ "(" ^ argsstr ^ ")"*)
      (*(to_string f names nanon true None)
      ^ "("
      ^ (String.concat
           ","
           (List.map
              (fun t -> to_string t names nanon false None)
              (Array.to_list args)))
      ^ ")"*)
    and lam2str (n:int) (nms: int array) (t:term): string =
      let argsstr, tstr = lam_strs n nms t in
      "((" ^ argsstr ^ ") -> " ^ tstr ^ ")"
    in
    let inop, str =
      match t with
        Variable i ->
          None, var2str i
      | Application (f,args) ->
          begin
            try
              let op = find_op f in
              Some op, op2str op args
            with Not_found ->
              None, app2str f args
          end
      | Lam (n,nms,t) ->
          None, lam2str n nms t
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





let expand_term (t:term) (nbound:int) (ft:t): term =
  (* Expand the definitions of the term 't' within an environment with
     'nbound' bound variables, i.e. a variable i with nbound<=i refers to the
     global feature i-nbound

     Note: [expand_term] doesn't do any beta reductions in the term [t] which
     would have been possible before the expansion. *)
  let rec expand (t:term) (nb:int): term =
    let apply (f:term) (args:term array): term =
      match f with
        Lam (n,nms,t) ->
          assert (n = Array.length args);
          Term.apply t args
      | _ -> Application (f,args)
    in
    match t with
      Variable i when i < nb ->
        t
    | Variable i ->
        assert (i-nb < count ft);
        (try expand (definition i nb ft) nb
        with Not_found -> t)
    | Application (Lam(n,nms,t),args) ->
        let t    = expand t (nb+n)
        and args = Array.map (fun t -> expand t nb) args in
        Application(Lam(n,nms,t),args)
    | Application (f,args) ->
        let f    = expand f nb
        and args = Array.map (fun t -> expand t nb) args in
        apply f args
    | Lam (n,nms,t) ->
        let t = expand t (nb+n) in
        Lam (n,nms,t)
  in
  expand t nbound





let rec normalize_term (t:term) (nbound:int) (ft:t): term =
  (* Expand the definitions of the term 't' and beta reduce it within an
     environment with 'nbound' bound variables, i.e. a variable i with
     nbound<=i refers to the global feature i-nbound *)
  Term.reduce (expand_term t nbound ft)




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
        | Some def -> term_to_string def 0 fdesc.argnames ft
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




let find_variant (i:int) (cls:int) (ft:t): int =
  (* Find the variant of the feature [i] in the class [cls] *)
  let ct = class_table ft
  and desc = descriptor i ft in
  assert (Array.length desc.anchored = 1); (* exactly one formal generic anchored
                                              to the owner class *)
  let nfgs = Tvars.count_all desc.tvs
  and fg_anchor = desc.anchored.(0) in
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



let has_variant (i:int) (cls:int) (ft:t): bool =
  (* Has the feature [i] a variant in the class [cls]? *)
  try let _ = find_variant i cls ft in true
  with Not_found -> false


let split_equality (t:term) (nbenv:int) (ft:t): int * term * term =
  let all_id = nbenv + all_index in
  let nargs, t =
    try
      let n,nms,t0 = Term.quantifier_split t all_id in
      n, t0
    with Not_found ->
      0, t
  in
  let nbenv = nbenv + nargs in
  match t with
    Application (Variable i, args) when nbenv <= i ->
      let i = i - nbenv in
      assert (i < count ft);
      if (base_descriptor i ft).is_eq then begin
        assert (Array.length args = 2);
        nargs, args.(0), args.(1)
      end else
        raise Not_found
  | _ -> raise Not_found


let is_equality (t:term) (nbenv:int) (ft:t): bool =
  try
    let _ = split_equality t nbenv ft in true
  with Not_found -> false



let update_equality (seed:int) (i:int) (ft:t): unit =
  (* If the feature [seed] is the equality feature of ANY then mark the base
     descriptor [bdesc] as equality. *)
  if seed = eq_index then begin
    let desc  = descriptor i ft
    and bdesc = base_descriptor i ft in
    bdesc.is_eq <- true;
    assert (desc.cls <> -1)
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
      update_equality i_seed i1 ft
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
        bdesc1.seeds        <- IntSet.add i_seed bdesc1.seeds
      )
      bdesc0.seeds;
  end;
  let fn  = (descriptor i1 ft).fname in
  let tab = Feature_map.find fn ft.map in
  Term_table2.remove i1 tab






let inherit_effective (i:int) (cls:int) (ft:t): unit =
  let desc = descriptor i ft in
  let ctp,tvs = Class_table.class_type cls ft.ct
  and anchor  = desc.anchored.(0) in
  let ntvs    = Tvars.count_all tvs
  and ntvs_i  = Tvars.count_all desc.tvs
  in
  let tvs1 = Tvars.insert_fgs desc.tvs anchor tvs in
  let ctp  = Term.upbound (ntvs_i-anchor) ntvs ctp in
  let ctp  = Term.up anchor ctp in
  let tvs1 = Tvars.update_fg (anchor+ntvs) ctp tvs1 in
  let f_tp(tp:type_term): type_term =
    Term.upbound ntvs anchor tp
  and def_opt =
    let bdesc = base_descriptor i ft in
    assert (not (Feature.Spec.has_preconditions bdesc.spec)); (* nyi *)
    match Feature.Spec.definition bdesc.spec with
      None -> None
    | Some t ->
        let nargs = Array.length desc.argnames in
        Some (variant_term t nargs desc.cls cls ft)
  in
  let spec = Feature.Spec.make_func def_opt [] [] in
  let cnt = count ft
  and nargs = Array.length desc.argnames
  in
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    if is_public ft then Some (standard_bdesc cnt cls spec nargs ft)
    else None
  in
  Seq.push
    {mdl       = Class_table.current_module ft.ct;
     fname     = desc.fname;
     cls       = cls;
     impl      = desc.impl;
     tvs       = tvs1;
     anchored  = Array.make 1 (anchor+ntvs);
     argnames  = desc.argnames;
     sign      = Sign.transform f_tp desc.sign;
     tp        = f_tp desc.tp;
     priv      = bdesc;
     pub       = bdesc_opt
   } ft.seq;
  inherit_feature i cnt cls false ft





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
  begin match Feature.Spec.definition spec with
    Some t when is_ghost_term t nargs ft && not (Sign.is_ghost sign) ->
      error_info fn.i "Must be a ghost function"
  | _ -> ()
  end;
  let mdl = Class_table.current_module ft.ct in
  let cls = Class_table.owner tvs sign ft.ct in
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
  add_class_feature cnt false base ft



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
    if spec <> desc.priv.spec then
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
        add_class_feature idx false false ft
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
        if idx <> all_index && idx <> some_index then
          add_class_feature idx true base ft)
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
    let or_desc = descriptor or_index ft in
    or_desc.priv.spec <- Feature.Spec.make_func None [] [];
    or_desc.priv.level <- 0
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
