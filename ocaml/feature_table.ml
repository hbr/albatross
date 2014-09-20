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
    definition:       term option;
    mutable seeds:    IntSet.t;
    mutable variants: int IntMap.t  (* cls -> fidx *)
  }

type descriptor = {
    mutable mdl: int;             (* -1: base feature, module not yet assigned*)
    cls:         int;             (* owner class *)
    fname:       feature_name;
    impstat:     implementation_status;
    tvs:         Tvars.t;         (* only formal generics *)
    mutable anchored: int array;  (* formal generics anchored to the owner class *)
    argnames:    int array;
    sign:        Sign.t;
    mutable tp:  type_term;
    priv:        base_descriptor;
    mutable pub: base_descriptor option;
  }

type t = {
    mutable map: Term_table.t ref Feature_map.t;
    seq:         descriptor seq;
    mutable base:int list ref IntMap.t; (* module name -> list of features *)
    ct:          Class_table.t
  }


let empty (): t =
  {map  = Feature_map.empty;
   seq  = Seq.empty ();
   base = IntMap.empty;
   ct   = Class_table.base_table ()}



let standard_bdesc (i:int) (cls:int) (def_opt: term option): base_descriptor =
  {seeds      = IntSet.singleton i;     (* each feature is its own seed *)
   variants   = IntMap.singleton cls i; (* and own variant in its owner class *)
   definition = def_opt}


let class_table (ft:t):  Class_table.t   = ft.ct

let is_private (ft:t): bool = Class_table.is_private ft.ct
let is_public  (ft:t): bool = Class_table.is_public  ft.ct
let is_interface_check  (ft:t): bool = Class_table.is_interface_check ft.ct
let is_interface_use (ft:t): bool = Class_table.is_interface_use ft.ct


let count (ft:t): int =
  Seq.count ft.seq


let descriptor (i:int) (ft:t): descriptor =
  assert (i < count ft);
  Seq.elem i ft.seq


let base_descriptor (i:int) (ft:t): base_descriptor =
  assert (i < count ft);
  let desc = descriptor i ft in
  if is_private ft then
    desc.priv
  else
    match desc.pub with
      None -> assert false (* cannot happen in public view *)
    | Some bdesc -> bdesc


let definition (i:int) (nb:int) (ft:t): term =
  (* The definition of the feature [i] as a lambda term (if there are arguments)
     transformed into an environment with [nb] bound variables. Raises [Not_found]
     in case that there is no definition *)
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  let nargs = Sign.arity desc.sign in
  match bdesc.definition with
    None -> raise Not_found
  | Some t ->
      let t = Term.upbound nb nargs t in
      if nargs = 0 then t else Lam (nargs,[||],t)



let count_fgs (i:int) (ft:t): int =
  assert (i < count ft);
  Tvars.count_fgs (descriptor i ft).tvs


let anchor (i:int) (ft:t): int =
  let desc = descriptor i ft in
  if Array.length desc.anchored = 1 then
    desc.anchored.(0)
  else
    raise Not_found



let variant (i:int) (cls:int) (ft:t): int =
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  try
    let seed_bdesc = base_descriptor (IntSet.min_elt bdesc.seeds) ft in
    IntMap.find cls seed_bdesc.variants
  with Not_found ->
    i


let variant_term (t:term) (nb:int) (cls:int) (ft:t): term =
  let f (j:int): term = Variable (variant j cls ft) in
  Term.map_free f t nb


let is_deferred (desc:descriptor): bool =
  match desc.impstat with
    Deferred -> true
  | _        -> false


let string_of_signature (i:int) (ft:t): string =
  let desc = descriptor i ft in
  (feature_name_to_string desc.fname) ^
  (Class_table.string_of_signature desc.sign desc.tvs ft.ct)


let names_of_formals (farr: formal array): int array =
  Array.map (fun (name,_) -> name) farr

let terms_of_formals (farr: formal array): term array =
  Array.map (fun (_,t) -> t) farr





let implication_index: int = 0
let fparen_index:      int = 1
let all_index:         int = 2
let some_index:        int = 3
let pparen_index:      int = 4



let add_class_feature (i:int) (ft:t): unit =
  (* Add the feature [i] as a class feature to the corresponding owner
     class. *)
  assert (i < count ft);
  let desc  = Seq.elem i ft.seq
  in
  Class_table.add_feature
    (i, desc.fname, desc.tp, Tvars.count_all desc.tvs)
    desc.cls
    (is_deferred desc)
    ft.ct



let add_class_features (ft:t): unit =
  for i = 0 to (count ft)-1 do
    add_class_feature i ft
  done


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
      let tab = ref Term_table.empty in
      ft.map <- Feature_map.add desc.fname tab ft.map;
      tab
  in
  if has_equivalent i ft then
    assert false  (* raise some exception *)
  else
    tab := Term_table.add desc.tp ntvs 0 i !tab




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


let add_builtin
    (mdl_nme: string)
    (cls: int)
    (fn:feature_name)
    (concepts: type_term array)
    (argtypes: type_term array)
    (res:  type_term)
    (ft:t)
    : unit =
  let mdl_nme            = ST.symbol mdl_nme
  in
  let sign = Sign.make_func argtypes res
  and ntvs = Array.length concepts
  and cnt  = count ft
  in
  let bdesc = standard_bdesc cnt cls None
  in
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
    impstat  = Builtin;
    tvs      = Tvars.make_fgs (standard_fgnames ntvs) concepts;
    anchored = [||];     (* ??? *)
    argnames = standard_argnames (Array.length argtypes);
    sign     = sign;
    tp       = Class_table.to_dummy ntvs sign;
    priv     = bdesc;
    pub      = Some bdesc
  }
  in
  Seq.push desc ft.seq;
  lst := cnt :: !lst



let base_table () : t =
  (** Construct a basic table which contains at least implication.  *)
  let bool    = Class_table.boolean_type 0 in
  let ft      = empty ()
  in
  let any1  = Variable (Class_table.any_index+1)
  and any2  = Variable (Class_table.any_index+2)
  and bool1 = Variable (Class_table.boolean_index+1)
  and g_tp  = Variable 0
  and a_tp  = Variable 0
  and b_tp  = Variable 1 in
  let p_tp  = Application (Variable (Class_table.predicate_index+1),
                           [|g_tp|])
  and f_tp  = Application (Variable (Class_table.function_index+2),
                           [|a_tp;b_tp|])
  in
  add_builtin
    "boolean" Class_table.boolean_index (FNoperator DArrowop)
    [||] [|bool;bool|] bool ft;

  add_builtin
    "function" Class_table.function_index (FNoperator Parenop)
    [|any2;any2|] [|f_tp;a_tp|] b_tp ft;

  add_builtin
    "boolean" Class_table.predicate_index (FNoperator Allop)
    [|any1|] [|p_tp|] bool1 ft;

  add_builtin
    "boolean" Class_table.predicate_index (FNoperator Someop)
    [|any1|] [|p_tp|] bool1 ft;

  assert ((descriptor implication_index ft).fname = FNoperator DArrowop);
  assert ((descriptor fparen_index ft).fname      = FNoperator Parenop);
  assert ((descriptor all_index ft).fname         = FNoperator Allop);
  assert ((descriptor some_index ft).fname        = FNoperator Someop );
  ft




let implication_term (a:term) (b:term) (nbound:int) (ft:t)
    : term =
  (* The implication term a=>b in an environment with 'nbound' bound variables
   *)
  let args = [|a;b|] in
  Application (Variable (implication_index+nbound), args)




let find
    (fn:feature_name)
    (tvs: Tvars.t)
    (tp:type_term)
    (ft:t)
    : int =
  let ntvs = Tvars.count_all tvs
  and tab = Feature_map.find fn ft.map in
  let lst  = Term_table.unify tp ntvs !tab in
  let idx_lst =
    List.fold_left
      (fun lst (i,sub) ->
        let desc = descriptor i ft in
        if tvs = desc.tvs && Term_sub.is_identity sub then
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
          if ok then
            assert false
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




let find_with_signature
    (fn:feature_name)
    (tvs: Tvars.t)
    (sign:Sign.t)
    (ft:t)
    : int =
  (* Find the feature with the characteristics.  *)
  let ntvs = Tvars.count_all tvs in
  let tp   = Class_table.to_dummy ntvs sign in
  find fn tvs tp ft



let find_funcs
    (fn:feature_name)
    (nargs:int) (ft:t)
    : (int * Tvars.t * Sign.t) list =
  let tab = Feature_map.find fn ft.map in
  List.fold_left
    (fun lst (i,_,_,_) ->
      let desc = descriptor i ft in
      let sign = desc.sign in
      let arity = Sign.arity sign
      and tvs   = Tvars.fgs_to_global desc.tvs
      in
      if arity = nargs then
        (i,tvs,sign) :: lst
      else if arity < nargs then (* downgrade *)
        let nfgs = Tvars.count_all tvs in
        try
          let s = Class_table.downgrade_signature nfgs sign nargs
          in
          (i,tvs,s) :: lst
        with Not_found ->
          lst
      else (* upgrade *)
        lst (* nyi: upgrade of signature *)
    )
    []
    (Term_table.terms !tab)


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
        let idx = i-nb in
        assert (idx < count ft);
        (try expand (definition idx nb ft) nb
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




let term_to_string
    (t:term)
    (names: int array)
    (ft:t)
    : string =
  (** Convert the term [t] in an environment with the named variables [names]
      to a string.
   *)
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
    and anon2sym (i:int): int =
      ST.symbol ("$" ^ (string_of_int (nanon+i)))
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
      | _ -> assert false  (* cannot happen *)
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
      (to_string f names nanon true None)
      ^ "("
      ^ (String.concat
           ","
           (List.map
              (fun t -> to_string t names nanon false None)
              (Array.to_list args)))
      ^ ")"
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
            Left  -> not is_left
          | Right -> is_left
          | _     -> false
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
  to_string t names 0 false None





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
      and bdyname def_opt =
        match def_opt with
          None -> "Basic"
        | Some def -> term_to_string def fdesc.argnames ft
      and clsnme =
        if fdesc.cls = -1 then ""
        else Class_table.class_name fdesc.cls ft.ct
      in
      match fdesc.pub with
        None ->
          Printf.printf "%s.%s: %s %s = (%s)\n"
            mdlnme clsnme name tname (bdyname fdesc.priv.definition)
      | Some pdef ->
          Printf.printf "%s.%s: %s %s = (%s, %s)\n"
            mdlnme clsnme name tname
            (bdyname fdesc.priv.definition) (bdyname pdef.definition))
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




let inherit_feature (i0:int) (i1:int) (ft:t): unit =
  (* Inherit the feature [i0] as the feature [i1], i.e. add [i1] as a variant
     to all seeds of [i0] and add all seeds of [i0] as seeds of
     [i1]. Furthermore [i1] is no longer its own seed and cannot be found via
     the feature map
   *)
  assert (i0 < count ft);
  assert (i1 < count ft);
  let bdesc0 = base_descriptor i0 ft
  and bdesc1 = base_descriptor i1 ft
  and desc1  = descriptor i1 ft
  in
  bdesc1.seeds <- IntSet.remove i1 bdesc1.seeds;
  IntSet.iter
    (fun i_seed -> (* add variant to seed and seed to variant*)
      let bdesc_seed = base_descriptor i_seed ft in
      assert (not (IntMap.mem desc1.cls bdesc_seed.variants) ||
              IntMap.find desc1.cls bdesc_seed.variants = i1);
      bdesc_seed.variants <- IntMap.add desc1.cls i1 bdesc_seed.variants;
      bdesc1.seeds        <- IntSet.add i_seed bdesc1.seeds
    )
    bdesc0.seeds;
  let tab = Feature_map.find desc1.fname ft.map in
  tab := Term_table.remove i1 !tab





let inherit_deferred (i:int) (cls:int) (info:info) (ft:t): unit =
  (* Inherit the deferred feature [i] in the class [cls] *)
  let desc = descriptor i ft in
  assert (cls <> desc.cls);
  let idx =
    try find_variant i cls ft
    with Not_found ->
      let ct   = class_table ft  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " does not have a feature unifyable with \"" ^
        (feature_name_to_string desc.fname) ^
        (Class_table.string_of_signature
           desc.sign desc.tvs  ct) ^
        "\" with proper substitutions of the type variables" in
      error_info info str
  in
  inherit_feature i idx ft






let inherit_effective (i:int) (cls:int) (info:info) (ft:t): unit =
  (* Inherit the effective  feature [i] in the class [cls] *)
  let desc = descriptor i ft in
  assert (cls <> desc.cls);
  if not (Array.length desc.anchored = 1) then
    ()
  else
    try
      let _ = find_variant i cls ft in
      let ct   = class_table ft  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " has already a feature unifyable with \"" ^
        (feature_name_to_string desc.fname) ^
        (Class_table.string_of_signature desc.sign desc.tvs ct) ^
        "\"" in
      error_info info str
    with Not_found ->
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
        match (base_descriptor i ft).definition with
          None -> None
        | Some t ->
          let nargs = Array.length desc.argnames in
          Some (variant_term t nargs cls ft)
      in
      let cnt = count ft in
      let bdesc = standard_bdesc cnt cls def_opt
      in
      Seq.push
        {mdl       = Class_table.current_module ft.ct;
         fname     = desc.fname;
         cls       = cls;
         impstat   = desc.impstat;
         tvs       = tvs1;
         anchored  = Array.make 1 (anchor+ntvs);
         argnames  = desc.argnames;
         sign      = Sign.transform f_tp desc.sign;
         tp        = f_tp desc.tp;
         priv      = bdesc;
         pub       = if is_public ft then Some bdesc else None
       } ft.seq;
      inherit_feature i cnt ft




let do_inherit
    (cls:int)
    (anc_lst: (int * type_term array) list)
    (info:info)
    (ft:t)
    : unit =
  (* For all ancestors in the list [anc_lst]:

     Go through all deferred features of the parent class [par_idx] and verify
     that the class [cls] has all these deferred features.

     Then inherit all effective features of the class [par_idx] into the class
     [cls_idx]
   *)
  let ct = class_table ft in
  List.iter
    (fun (par,par_args) ->
      let flst = Class_table.deferred_features par ct in
      List.iter (fun i -> inherit_deferred i cls info ft) flst;
      let flst = Class_table.effective_features par ct in
      List.iter (fun i -> inherit_effective i cls info ft) flst
    )
    anc_lst




let add_function (desc:descriptor) (info:info) (ft:t): unit =
  let cnt = count ft
  and nfgs = Tvars.count_all desc.tvs
  and nanchors = Array.length desc.anchored
  in
  desc.tp <- Class_table.to_dummy nfgs desc.sign;
  Seq.push desc ft.seq;
  add_key cnt ft;
  add_class_feature cnt ft;
  if not (is_deferred desc) && nanchors = 1 then
    let descs = Class_table.descendants desc.cls ft.ct in
    IntSet.iter
      (fun des -> inherit_effective cnt des info ft)
      descs



let put_function
    (fn:       feature_name withinfo)
    (tvs:      Tvars.t)
    (argnames: int array)
    (sign:     Sign.t)
    (impstat:  implementation_status)
    (term_opt: term option)
    (ft:       t): unit =
  assert (Tvars.count tvs = 0);  (* only formal generics, no untyped *)
  let is_priv = is_private ft in
  let cnt   = Seq.count ft.seq
  in
  let idx =
     try find_with_signature fn.v tvs sign ft
     with Not_found -> cnt
  in
  let mdl = Class_table.current_module ft.ct in
  let cls = Class_table.owner tvs sign ft.ct in
  let anchored = Class_table.anchored tvs cls ft.ct in
  let nanchors = Array.length anchored in
  if idx=cnt then begin (* new feature *)
    (match impstat with
      Deferred ->
        Class_table.check_deferred cls nanchors fn.i ft.ct
    | _ -> ());
    let bdesc = standard_bdesc cnt cls term_opt in
    let desc =
      {mdl      = mdl;
       cls      = cls;
       fname    = fn.v;
       impstat  = impstat;
       tvs      = tvs;
       argnames = argnames;
       sign     = sign;
       tp       = Variable 0;
       anchored = anchored;
       priv     = bdesc;
       pub      = if is_priv then None else Some bdesc}
    in
    add_function desc fn.i ft
  end else begin        (* feature update *)
    let desc = descriptor idx ft
    and not_match str =
      let str = "The " ^ str ^ " of \""
        ^ (feature_name_to_string fn.v)
        ^ "\" does not match the previous definition"
      in
      error_info fn.i str
    in
    desc.mdl <- mdl;
    assert (cls = desc.cls);
    if is_priv then begin
      if impstat <> desc.impstat then
        not_match "implementation status";
      if term_opt <> desc.priv.definition
      then
        not_match "private definition"
    end else
      match desc.pub with
        None ->
          desc.pub <- Some (standard_bdesc idx cls term_opt)
      | Some bdesc ->
          if bdesc.definition <> term_opt then
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

let find_module (name:int) (lib:int list) (ft:t): int =
  Class_table.find_module name lib ft.ct

let module_name (mdl:int) (ft:t): string = Class_table.module_name mdl ft.ct


let add_base_features (mdl_name:int) (ft:t): unit =
  try
    let lst = IntMap.find mdl_name ft.base in
    let curr_mdl = current_module ft in
    List.iter
      (fun idx ->
        let desc = descriptor idx ft in
        assert (desc.mdl = -1);
        desc.mdl <- curr_mdl ;
        add_key idx ft;
        add_class_feature idx ft)
      !lst
  with Not_found ->
    ()


let add_used_module (name:int) (lib:int list) (used:IntSet.t) (ft:t): unit =
  Class_table.add_used_module name lib used ft.ct;
  add_base_features name ft

let add_current_module (name:int) (used:IntSet.t) (ft:t): unit =
  Class_table.add_current_module name used ft.ct;
  add_base_features name ft

let set_interface_check (used:IntSet.t) (ft:t): unit =
  Class_table.set_interface_check used ft.ct;
  ft.map <- Feature_map.empty;
  let mdl = current_module ft in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if desc.mdl = mdl || IntSet.mem desc.mdl used then
      add_key i ft
  done
