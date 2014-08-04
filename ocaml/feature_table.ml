open Container
open Support
open Term
open Signature
open Printf

type implementation_status = No_implementation | Builtin | Deferred



module Feature_map = Map.Make(struct
  type t = feature_name
  let compare = Pervasives.compare
end)



type definition = term

type formal     = int * term

type descriptor = {
    mutable mdl: int;
    cls:         int;
    fname:       feature_name;
    impstat:     implementation_status;
    fgnames:     int array;
    concepts:    type_term array;
    mutable anchored: int array;
    argnames:    int array;
    sign:        Sign.t;
    mutable tp:  type_term;
    priv:        definition option;
    mutable pub: definition option option
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

let class_table (ft:t):  Class_table.t   = ft.ct


let count (ft:t): int =
  Seq.count ft.seq


let descriptor (i:int) (ft:t): descriptor =
  assert (i < count ft);
  Seq.elem i ft.seq


let is_deferred (desc:descriptor): bool =
  match desc.impstat with
    Deferred -> true
  | _        -> false


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
    i
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
  let ntvs  = Array.length desc.concepts
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


let names_0 (c:char) (size:int): int array =
  let code = Char.code c in
  Array.init size (fun i -> ST.symbol (String.make 1 (Char.chr (i + code))))

let fgnames_0 (size:int): int array =
  names_0 'A' size

let argnames_0 (size:int): int array =
  names_0 'a' size


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
    fgnames  = fgnames_0 ntvs;
    concepts = concepts;
    anchored = [||];     (* ??? *)
    argnames = argnames_0 (Array.length argtypes);
    sign     = sign;
    tp       = Class_table.to_dummy ntvs sign;
    priv     = None;
    pub      = None
  }
  and cnt = count ft
  in
  Seq.push desc ft.seq;
  lst := cnt :: !lst



let base_table () : t =
  (** Construct a basic table which contains at least implication.  *)
  let bool    = Class_table.boolean_type 0 in
  let ft      = empty ()
  in
  let any   = Variable Class_table.any_index
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
    [|any;any|] [|f_tp;a_tp|] b_tp ft;

  add_builtin
    "boolean" Class_table.predicate_index (FNoperator Allop)
    [|any|] [|p_tp|] bool1 ft;

  add_builtin
    "boolean" Class_table.predicate_index (FNoperator Someop)
    [|any|] [|p_tp|] bool1 ft;

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
    (nargs:int)
    (concepts:type_term array)
    (sign:Sign.t)
    (ft:t)
    : int =
  (* Find the feature with the characteristics.  *)
  let tab = Feature_map.find fn ft.map in
  let ntvs = Array.length concepts in
  let tp   = Class_table.to_dummy ntvs sign in
  let lst  = Term_table.unify tp ntvs !tab in
  let idx_lst =
    List.fold_left
      (fun lst (i,sub) ->
        (* For all type variables of i there is one subterm of tp in sub.

           Each type variable in i has a concept. The corresponding subterm of
           tp has to satisfy the concept
         *)
        let desc = descriptor i ft in
        if concepts = desc.concepts && Term_sub.is_identity sub then
          i :: lst
        else
          let ok =
            Term_sub.for_all
              (fun j t ->
                Class_table.satisfies
                  t TVars.empty concepts desc.concepts.(j) ft.ct)
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




let find_funcs
    (fn:feature_name)
    (nargs:int) (ft:t)
    : (int * TVars.t * Sign.t) list =
  let tab = Feature_map.find fn ft.map in
  List.fold_left
    (fun lst (i,_,_,_) ->
      let desc = descriptor i ft in
      let sign = desc.sign in
      let arity = Sign.arity sign
      and tvs   = TVars.make 0 desc.concepts
      in
      if arity = nargs then
        (i,tvs,sign) :: lst
      else if arity < nargs then (* downgrade *)
        let nfgs = Array.length desc.concepts in
        try
          let s = Class_table.downgrade_signature nfgs sign nargs in
          (i,tvs,s) :: lst
        with Not_found ->
          lst
      else (* upgrade *)
        lst (* nyi: upgrade of signature *)
    )
    []
    (Term_table.terms !tab)




let rec expand_term (t:term) (nbound:int) (ft:t): term =
  (* Expand the definitions of the term 't' within an environment with
     'nbound' bound variables, i.e. a variable i with nbound<=i refers to
     the global feature i-nbound *)
  Term.map
    (fun i nb ->
      let n = nb+nbound in
      if i<n then
        Variable i
      else
        let idx = i-n in
        assert (idx < (Seq.count ft.seq));
        let desc = Seq.elem idx ft.seq in
        match desc.priv with
          None -> Variable i
        | Some def ->
            let nargs = Sign.arity desc.sign in
            let t = expand_term def nargs ft in
            let tup = Term.upbound n nargs t in
            if nargs = 0 then tup
            else
              Lam (nargs, [||], tup)
    )
    t




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
      (outop: (operator*bool) option)
      : string =
    (* nanon: number of already used anonymous variables
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
      to_string t names nanon None
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
            ^ (to_string args.(0) names nanon (Some (op,false)))
          else begin
            assert (nargs=2); (* only unary and binary operators *)
            (to_string args.(0) names nanon (Some (op,true)))
            ^ " " ^ (operator_to_rawstring op) ^ " "
        ^ (to_string args.(1) names nanon (Some (op,false)))
          end
    and app2str (f:term) (args: term array): string =
      (to_string f names nanon None)
      ^ "("
      ^ (String.concat
           ","
           (List.map
              (fun t -> to_string t names nanon None)
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
    | _ -> str
  in
  to_string t names 0 None





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
        Class_table.string_of_signature fdesc.sign 0 fdesc.fgnames ft.ct
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
            mdlnme clsnme name tname (bdyname fdesc.priv)
      | Some pdef ->
          Printf.printf "%s.%s: %s %s = (%s, %s)\n"
            mdlnme clsnme name tname (bdyname fdesc.priv) (bdyname pdef))
    ft.seq



let add_function (desc:descriptor) (ft:t): unit =
  let cnt = count ft in
  desc.tp <- Class_table.to_dummy (Array.length desc.concepts) desc.sign;
  let anch = ref [] in
  for i = 0 to Array.length desc.concepts - 1 do
    match desc.concepts.(i) with
      Variable i when i = desc.cls ->
        anch := i :: !anch
    | _ -> ()
  done;
  desc.anchored <- Array.of_list (List.rev !anch);
  Seq.push desc ft.seq;
  add_key cnt ft;
  add_class_feature cnt ft



let put_function
    (fn:       feature_name withinfo)
    (fgnames:  int array)
    (concepts: type_term array)
    (argnames: int array)
    (sign:     Sign.t)
    (impstat:  implementation_status)
    (term_opt: term option)
    (ft:       t): unit =
  let is_priv = Parse_info.is_module () in
  let cnt   = Seq.count ft.seq
  and nargs = Sign.arity sign
  in
  let idx =
     try find fn.v nargs concepts sign ft
     with Not_found -> cnt
  in
  let mdl = Class_table.current_module ft.ct in
  let cls = Class_table.owner mdl concepts sign ft.ct in
  if idx=cnt then begin (* new feature *)
    let desc =
      {mdl      = mdl;
       cls      = cls;
       fname    = fn.v;
       impstat  = impstat;
       fgnames  = fgnames;
       concepts = concepts;
       argnames = argnames;
       sign     = sign;
       tp       = Variable 0;
       anchored = [||];
       priv     = term_opt;
       pub      = if is_priv then None else Some term_opt}
    in
    add_function desc ft
  end else begin        (* feature update *)
    let desc = Seq.elem idx ft.seq
    and not_match str =
      let str = "The " ^ str ^ " of \""
        ^ (feature_name_to_string fn.v)
        ^ "\" does not match the previous definition"
      in
      error_info fn.i str
    in
    desc.mdl <- mdl;
    if cls <> desc.cls then
      printf "put_function: owner cls %d, desc.cls %d\n" cls desc.cls;
    assert (cls = desc.cls);
    if is_priv then begin
      if impstat <> desc.impstat then
        not_match "implementation status";
      if term_opt <> desc.priv
      then
        not_match "private definition"
    end else
      match desc.pub with
        None ->
          desc.pub <- Some term_opt
      | Some def ->
          if def <> term_opt then
            not_match "public definition"
  end




let do_inherit
    (cls_idx:int)
    (par_idx:int)
    (par_args: type_term array)
    (info:info)
    (ft:t): unit =
  (* Go through all deferred features of the parent class [par_idx] and verify
     that the class [cls_idx] has all these deferred features.

     Then inherit all effective features of the class [par_idx] into the class
     [cls_idx]
   *)
  let ct = class_table ft in
  let flst = Class_table.deferred_features par_idx ct in
  List.iter
    (fun i ->
      ())
    flst



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


let add_module
    (name:int) (lib: int list) (pub:bool) (used:IntSet.t) (ft:t): unit =
  Class_table.add_module name lib pub used ft.ct;
  add_base_features name ft
