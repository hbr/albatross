open Support
open Term
open Signature
open Container
open Printf

type formal = int * type_term

type base_descriptor = { hmark:   header_mark;
                         fgs:     formal array;
                         mutable ancestors: type_term array IntMap.t}

type descriptor      = { mutable mdl:  int;
                         name: int;
                         mutable def_features: IntSet.t;
                         mutable eff_features: IntSet.t;
                         mutable def_asserts:  IntSet.t;
                         mutable eff_asserts:  IntSet.t;
                         priv: base_descriptor;
                         mutable publ: base_descriptor option}

type t = {mutable map:   int IntMap.t;
          seq:           descriptor seq;
          mutable fgens: type_term IntMap.t;
          mt:            Module_table.t}

let boolean_index   = 0
let any_index       = 1
let predicate_index = 2
let function_index  = 3
let tuple_index     = 4



let module_table (ct:t): Module_table.t =
  ct.mt

let count (c:t) =
  Seq.count c.seq


let class_symbol (i:int) (ct:t): int =
  assert (i<count ct);
  (Seq.elem i ct.seq).name

let class_name (i:int) (ct:t): string =
  ST.string (class_symbol i ct)


let split_type_term (tp:type_term) (nfgs:int): int * type_term array =
  let i,args =
    match tp with
      Variable i -> i, [||]
    | Application (Variable i,args) -> i, args
    | _ -> assert false
  in
  assert (nfgs <= i );
  i-nfgs, args


let combine_type_term (cls_idx:int) (args: type_term array): type_term =
  if 0 < Array.length args then
    Application (Variable cls_idx, args)
  else
    Variable cls_idx



let boolean_type (ntvs:int)  = Variable (boolean_index+ntvs)
let any (ntvs:int)           = Variable (any_index+ntvs)
let func nb dom ran = Application(Variable(nb+function_index),[|dom;ran|])



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



let find (cn: int) (ct:t): int =
  IntMap.find cn ct.map

let find_in_module (cn:int) (ct:t): int =
  assert (Module_table.has_current (module_table ct));
  let idx  = find cn ct in
  let desc = Seq.elem idx ct.seq
  and mdl  = Module_table.current ct.mt in
  if desc.mdl = (-1) || desc.mdl = mdl then
    idx
  else
    raise Not_found


let class_formal_generics (fgens: formal_generics) (ct:t): formal array =
  Array.of_list
    (List.map
       (fun nme ->
         try
           nme, IntMap.find nme ct.fgens
         with Not_found ->
           let str = "Unknown formal generic " ^ (ST.string nme) in
           error_info fgens.i str)
       fgens.v)


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
  let fgs = class_formal_generics fgens ct in
  let nfgs = Array.length desc.fgs in
  if nfgs <> Array.length fgs then
    (let str = "Class must have " ^ (string_of_int nfgs) ^ " formal generics" in
    error_info fgens.i str);
  for i = 0 to nfgs-1 do
    let nme,tp1 = fgs.(i)
    and _,  tp2 = desc.fgs.(i) in
    check_class_formal_generic fgens.i nme tp1 tp2 ct;
    desc.fgs.(i) <- nme,tp2
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
  let fgs = class_formal_generics fgens ct in
  let nfgs = Array.length fgs        in
  if nfgs > Array.length desc.priv.fgs then
    error_info fgens.i "More formal generics than in private definition";
  for i = 0 to nfgs-1 do
    let _,  tp1 = desc.priv.fgs.(i)
    and nme,tp2 = fgs.(i) in
    if tp1 <> tp2 then
      error_info
        fgens.i
        ("The constraint of " ^ (ST.string nme) ^
         " is not consistent with private definition");
    desc.publ <- Some {hmark=hm2; fgs=fgs; ancestors=IntMap.empty}
  done





let update
    (idx:   int)
    (hm:    header_mark withinfo)
    (fgens: formal_generics)
    (ct:    t)
    : unit =
  assert (Module_table.has_current (module_table ct));
  let desc = Seq.elem idx ct.seq
  and mdl  = Module_table.current ct.mt
  in
  if desc.mdl = -1 then
    desc.mdl <- mdl
  else if desc.mdl = mdl then
    ()
  else
    assert false; (* Cannot update a class from a different module *)
  if Module_table.is_private ct.mt then
    update_base_descriptor hm fgens desc.priv ct
  else
    match desc.publ with
      None ->       export idx hm fgens ct
    | Some bdesc -> update_base_descriptor hm fgens bdesc ct



let add_feature (fidx:int) (cidx:int) (is_deferred:bool) (ct:t)
    : unit =
  (** Add the feature [fidx] to the class [cidx] as deferred or effecitive
      feature depending on [is_deferred].  *)
  assert (cidx < count ct);
  let desc = Seq.elem cidx ct.seq in
  if is_deferred then
    desc.def_features <- IntSet.add fidx desc.def_features
  else
    desc.eff_features <- IntSet.add fidx desc.eff_features



let add_assertion (aidx:int) (cidx:int) (is_deferred:bool) (ct:t)
    : unit =
  (** Add the assertion [aidx] to the class [cidx] as deferred or effecitive
      assertion depending on [is_deferred].  *)
  assert (cidx < count ct);
  let desc = Seq.elem cidx ct.seq in
  if is_deferred then
    desc.def_asserts <- IntSet.add aidx desc.def_asserts
  else
    desc.eff_asserts <- IntSet.add aidx desc.eff_asserts



let add
    (hm:    header_mark withinfo)
    (cn:    int withinfo)
    (fgens: formal_generics)
    (ct:    t)
    : unit =
  assert false (* nyi: insertion of new classes *)





let owner (mdl:int) (concepts:type_term array) (sign:Sign.t) (ct:t): int =
  let max (cidx1:int) (cidx2:int): int =
    assert (0 <= cidx1 && cidx1 < count ct);
    assert (cidx2 = -1 || (0 <= cidx2 && cidx2 < count ct));
    if cidx2 = -1         then cidx1
    else if cidx1 = cidx2 then cidx1
    else begin
      let desc1 = Seq.elem cidx1 ct.seq
      and desc2 = Seq.elem cidx2 ct.seq in
      let mdl1  = desc1.mdl
      and mdl2  = desc2.mdl in
      assert (not (mdl1 = -1 && mdl2 = -1));
      if mdl1 = -1                       then cidx2
      else if mdl2 = -1                  then cidx1
      else if mdl1 < mdl2 && mdl2 <= mdl then cidx2
      else begin
        assert (mdl2 < mdl1 && mdl1 <= mdl);
        cidx1
      end
    end
  in
  let owner_tp (tp:type_term) (nb:int) (cidx_prev:int): int =
    Term.fold
      (fun cidx_prev var ->
        if var < nb then cidx_prev
        else max (var-nb) cidx_prev)
      cidx_prev
      tp
  in
  let nfgs = Array.length concepts in
  let cidx = Array.fold_left
      (fun cidx_prev tp -> owner_tp tp 0 cidx_prev)
      (-1)
      concepts
  in
  let cidx = Array.fold_left
      (fun cidx_prev tp -> owner_tp tp nfgs cidx_prev)
      cidx
      (Sign.arguments sign)
  in
  let rt = Sign.result_type sign in
  let cidx =
    if Result_type.has_result rt then
      owner_tp (Result_type.result rt) nfgs cidx
    else
      cidx
  in
  cidx



let base_descriptor (idx:int) (ct:t): base_descriptor =
  assert (0 <= idx);
  assert (idx < count ct);
  let desc = Seq.elem idx ct.seq in
  if desc.mdl = (Module_table.current (module_table ct)) then
    desc.priv
  else begin
    assert (Option.has desc.publ);
    Option.value desc.publ
  end



let rec satisfies
    (t1:type_term)
    (ntvs:int)
    (fgs: formal array)
    (cpt:type_term)
    (ct:t)
    : bool =
  (** Does the type [t] in an environment with [ntvs] type variables and the
      formal generics [fgs] satisfy the concept [cpt]?  *)
  let nfgs = Array.length fgs in
  match t1 with
    Variable i when i < nfgs ->
      let cpt_t1 = snd fgs.(i) in
      satisfies cpt_t1 0 [||] cpt ct
  | _ ->
      (Array.length fgs = 0 && t1 = cpt)





let valid_type
    (cls_idx:int)
    (args: type_term array)
    (ntvs: int)
    (fgs: formal array)
    (ct:t): type_term =
  (** The valid type term [cls_idx[args.(0),args.(1),...] in an environment
      with [ntvs] type variables and the formal generics [fgs].

      If the type term is not valid then [Not_found] is raised.

      To check: do all actual generics [args] satisfy their corresponding
      concepts *)
  let nfgs  = Array.length fgs
  and nargs = Array.length args in
  if cls_idx < ntvs then
    assert false (* shall never happen *)
  else if cls_idx < ntvs + nfgs then begin
    if nargs <> 0 then
      raise Not_found
    else
      Variable cls_idx
  end else begin
    let cls_idx_0 = cls_idx - ntvs - nfgs in
    let bdesc = base_descriptor cls_idx_0 ct in
    if nargs <> Array.length bdesc.fgs then
      raise Not_found;
    for i = 0 to nargs-1 do
      if not (satisfies args.(i) ntvs fgs (snd bdesc.fgs.(i)) ct) then
        raise Not_found
    done;
    if nargs = 0 then
      Variable cls_idx
    else
      Application (Variable cls_idx, args)
  end




let get_type
    (tp:type_t withinfo)
    (ntvs: int)
    (fgs: formal array)
    (ct:t)
    : term =
  (** Convert the syntactic type [tp] in an environment with [ntvs] type
      variables and the formal generics [fgs] into a type term *)
  let nfgs = Array.length fgs in
  let n    = ntvs + nfgs in
  let class_index (name:int): int =
    try
      ntvs + (Search.array_find_min (fun (n,_) -> n=name) fgs)
    with Not_found ->
      try
        n + (find name ct)
      with Not_found ->
        error_info tp.i ("Class " ^ (ST.string name)
                         ^ " does not exist")
  in
  let info = tp.i in
  let rec get_tp (tp:type_t): type_term =
    let valid_tp (idx:int) (args:type_term array): type_term =
      try
        valid_type idx args ntvs fgs ct
      with Not_found ->
        error_info info ((string_of_type tp) ^ " is not a valid type")
    in
    match tp with
      Normal_type (path,name,actuals) ->
        let args = List.map (fun tp -> get_tp tp) actuals in
        let args = Array.of_list args in
        valid_tp (class_index name) args
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
        tuple tp_lst
    | _ -> not_yet_implemented info "types other than normal types"
  in
  get_tp tp.v






let has_ancestor (cls:int) (anc:int) (ct:t): bool =
  (** Does the class [cls] have [anc] as an ancestor ? *)
  cls = anc ||
  let bdesc = base_descriptor cls ct in
  IntMap.mem anc bdesc.ancestors




let get_parent_type (tp: type_t withinfo) (cls_idx:int) (ct:t): type_term =
  (** Convert the syntactic type [tp] of a parent of the class [cls_idx] into
      a type term. *)
  assert (cls_idx < count ct);
  let bdesc = base_descriptor cls_idx ct
  in
  let tp_term = get_type tp 0 bdesc.fgs ct
  in
  (let fgnames,_ = Myarray.split bdesc.fgs in
  printf "parent type: %s of class %s\n"
    (type2string tp_term 0 fgnames ct)
    (class_name cls_idx ct)
  );
  let nfgs = Array.length bdesc.fgs in
  let parent_idx,parent_ags = split_type_term tp_term nfgs in
  if has_ancestor parent_idx cls_idx ct then
    error_info tp.i "Cyclic inheritance";
  let bdesc_parent = base_descriptor parent_idx ct
  in
  IntMap.iter
    (fun ancestor_cls ancestor_args ->
      let anc_args_sub =
        Array.map
          (fun tp ->
            Term.sub tp parent_ags nfgs)
          ancestor_args
      in
      try
        let anc_args = IntMap.find ancestor_cls bdesc.ancestors in
        if anc_args <> anc_args_sub then
          let fgnames,_ = Myarray.split bdesc.fgs
          and anc0 = combine_type_term ancestor_cls anc_args
          and anc1 = combine_type_term ancestor_cls anc_args_sub in
          let ancstr0 = type2string anc0 0 fgnames ct
          and ancstr1 = type2string anc1 0 fgnames ct in
          error_info tp.i
            ("Cannot inherit " ^ ancstr1 ^ " because " ^
             ancstr0 ^ " is already an ancestor")
      with Not_found ->
        bdesc.ancestors <-
          IntMap.add ancestor_cls anc_args_sub bdesc.ancestors)
    bdesc_parent.ancestors;
  tp_term



let put_formal (name: int withinfo) (concept: type_t withinfo) (ct:t): unit =
  (** Add the formal generic with [name] and [concept] to the formal generics
      of the class table [ct] *)
  if IntMap.mem name.v ct.fgens then
    error_info
      name.i
      ("formal generic " ^ (ST.string name.v) ^ " already defined")
  else
    ct.fgens <- IntMap.add
        name.v
        (get_type concept  0 [||] ct)
        ct.fgens





let collect_fgs (tp: type_t) (fgs:formal list) (ct:t): formal list =
  (** Collect the formal generics in the type [tp] in the order in
      which they appear and prepend them to [fgs] if not yet in.
   *)
  let rec collect (tp:type_t) (fgs:formal list): formal list =
    let add (path:int list) (name:int) (fgs:formal list): formal list =
      if path = [] &&
        not (List.exists (fun (nme,_) -> nme=name) fgs)
      then
        try
          let cpt = IntMap.find name ct.fgens in
          (name,cpt) :: fgs
        with Not_found ->
          fgs
      else
        fgs
    in
    match tp with
      Normal_type (path,name,args) ->
        let fgnms = List.fold_left
            (fun lst tp -> collect tp lst)
            fgs
            args
        in
        add path name fgnms
    | Current_type lst ->
        assert false (* nyi: but might be eliminated from the language *)
    | Arrow_type (tpa,tpb) ->
        collect tpb (collect tpa fgs)
    | Ghost_type tp | QMark_type tp | Paren_type tp ->
        collect tp fgs
    | Tuple_type lst ->
        List.fold_left (fun fgs tp -> collect tp fgs) fgs lst
  in
  collect tp fgs




let formal_generics
    (entlst: entities list withinfo)
    (rt:     return_type)
    (ntvs:   int)
    (fgs:    formal array)
    (ct:     t)
    : int * formal array =
  (** The cumulated number of type variables and the cumulated formal generics
      of the entity list [entlst] and the return type [rt] in an environment
      with [ntvs] type variables and the formal generics [fgs]. *)
  let fgs_rev = List.rev (Array.to_list fgs) in
  let ntvs, fgs_rev =
    List.fold_left
      (fun (ntvs,fgs_rev) ent ->
        match ent with
          Untyped_entities vars ->
            ntvs + List.length vars, fgs_rev
        | Typed_entities (_,tp) ->
            ntvs, collect_fgs tp fgs_rev ct)
      (ntvs,fgs_rev)
      entlst.v
  in
  let fgs_rev =
    match rt with
      None -> fgs_rev
    | Some tp -> collect_fgs (fst tp.v) fgs_rev ct
  in
  ntvs,
  Array.of_list (List.rev fgs_rev)





let formal_arguments
    (entlst: entities list withinfo)
    (ntvs: int)
    (fgs: formal array)
    (ct:t)
    : formal array =
  (** The formal arguments of the entity list [entlst] in an environment with
      the formal generics [fgs] and [ntvs] type variables *)
  let fargs (es: entities): formal list =
    match es with
      Untyped_entities lst ->
        assert (List.length lst <= ntvs);
        List.mapi (fun i name -> name, Variable i) lst
    | Typed_entities (lst,tp) ->
        let t = get_type (withinfo entlst.i tp) ntvs fgs ct in
        List.map (fun name -> name,t) lst
  in
  let arglst = List.concat (List.map fargs entlst.v) in
  Array.of_list arglst


let result_type
    (rt:return_type)
    (ntvs: int)
    (fgs: formal array)
    (ct:t)
    : Result_type.t =
  (** The result type which corresponds to the return type [rt] in an
      environment with the formal generics [fgs] and [ntvs] type variables *)
  match rt with
    None -> Result_type.empty
  | Some tpinf ->
      let tp,proc = tpinf.v in
      let t = get_type (withinfo tpinf.i tp) ntvs fgs ct in
      Result_type.make t proc



let empty_table (): t =
  let cc = Seq.empty ()
  in
  {map=IntMap.empty; seq=cc; fgens=IntMap.empty; mt=Module_table.make ()}



let add_base_class
    (name:int)
    (desc:base_descriptor)
    (ct:t)
    : unit =
  let priv = desc
  and publ = Some desc
  and idx  = Seq.count ct.seq
  and eset = IntSet.empty
  in
  Seq.push {mdl=(-1); name=name;
            def_features=eset; eff_features=eset;
            def_asserts=eset;  eff_asserts=eset;
            priv=priv; publ=publ} ct.seq;
  ct.map <- IntMap.add name idx ct.map



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
  and emppar = IntMap.empty
  and ct = empty_table ()   in
  add_base_class
    (ST.symbol "BOOLEAN")
    {hmark=Immutable_hmark; fgs=[||]; ancestors=emppar}
    ct;
  add_base_class
    (ST.symbol "ANY")
    {hmark=Deferred_hmark; fgs=[||]; ancestors=emppar}
    ct;
  add_base_class
    (ST.symbol "PREDICATE")
    {hmark=Deferred_hmark; fgs=[|fgg,anycon|]; ancestors=emppar}
    ct;
  add_base_class
    (ST.symbol "FUNCTION")
    {hmark=Deferred_hmark; fgs=[|(fga,anycon); (fgb,anycon)|]; ancestors=emppar}
    ct;
  add_base_class
    (ST.symbol "TUPLE")
    {hmark=Deferred_hmark; fgs=[|(fga,anycon); (fgb,anycon)|]; ancestors=emppar}
    ct;
  check_base_classes ct;
  ct





let type_of_signature
    (s:Sign.t)
    (ntvs: int)
    : type_term =
  (** The type term which corresponds to the signature [s] in an environment
      with [ntvs] type variables.  *)
  let argtypes = Sign.arguments s
  and nargs    = Sign.arity s
  and tuple_index    = tuple_index    + ntvs
  and function_index = function_index + ntvs
  in
  if Sign.has_result s && not (Sign.is_procedure s) then
    let rt = Sign.result s in
    if nargs = 0 then
      rt
    else if nargs = 1 then
      Application(Variable function_index, [|argtypes.(0);rt|])
    else
      let rec tuple (i:int) (tup:term): term =
        if i=0 then tup
        else
          let i   = i - 1 in
          let tup = Application(Variable tuple_index, [|argtypes.(i);tup|]) in
          tuple i tup
      in
      tuple
        (nargs-2)
        (Application(Variable tuple_index,
                     [|argtypes.(nargs-2); argtypes.(nargs-1)|]))
  else
    assert false (* nyi: procedures *)



let string_of_signature
    (s:Sign.t)
    (ntvs:int)
    (fgnames: int array)
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
              (fun tp -> type2string tp ntvs fgnames ct)
              (Array.to_list (Sign.arguments s))))
      ^ ")"
  and retstr =
    if has_res then
      type2string (Sign.result s) ntvs fgnames ct
    else ""
  and colon = if has_args && has_res then ": " else ""
  in
  argsstr ^ colon ^ retstr


(* needs to be adapted for private and public views !!
let class2string (i:int) (ctxt:t): string =
  assert (i < count ctxt);
  let desc = Seq.elem  i ctxt.seq in
  let ngen = Array.length desc.constraints in
  assert (ngen = Array.length desc.fgnames);
  let con2string =
    if ngen = 0 then ""
    else
      "["
      ^ (String.concat
             ","
           (Array.to_list
              (Array.mapi
                 (fun i c ->
                   (ST.string desc.fgnames.(i))
                   ^ ":"
                   ^ (type2string c 0 [||] ctxt))
                 desc.constraints) )
        )
      ^ "]"
  and par2string =
    String.concat
      ";"
      (List.rev (TypSet.fold
                   (fun el lst -> (type2string el 0 desc.fgnames ctxt)::lst)
                   desc.parents
                   []))
  in
  (hmark2string_wblank desc.hmark)
  ^ "class " ^ (class_name i ctxt)
  ^ con2string
  ^ (if TypSet.is_empty desc.parents then ""
  else" inherit " ^ par2string)
  ^ " end"
*)

let print ctxt =
  (*Seq.iteri
    (fun i c -> Printf.printf "%s\n" (class2string i ctxt))
    ctxt.seq*)
  assert false
