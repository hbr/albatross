open Support
open Term
open Signature
open Container

module TypSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = term
end)

module Int_table = Map_table.Make(struct
  let  compare = Pervasives.compare
  type t       = int
end)

type formal = int * type_term

type base_descriptor = { hmark:   header_mark;
                         fgs:     formal array;
                         mutable parents: TypSet.t}

type descriptor      = { mutable mdl:  int;
                         name: int;
                         priv: base_descriptor;
                         mutable publ: base_descriptor option}

type t = {mutable map:   int IntMap.t;
          classes:       descriptor seq;
          mutable fgens: term IntMap.t}

let boolean_index   = 0
let any_index       = 1
let predicate_index = 2
let function_index  = 3
let tuple_index     = 4



let count (c:t) =
  Seq.count c.classes


let class_symbol (i:int) (ct:t): int =
  assert (i<count ct);
  (Seq.elem i ct.classes).name

let class_name (i:int) (ct:t): string =
  ST.string (class_symbol i ct)




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

let find_in_module (cn:int) (mt:Module_table.t) (ct:t): int =
  assert (Module_table.has_current mt);
  let idx  = find cn ct in
  let desc = Seq.elem idx ct.classes
  and mdl  = Module_table.current mt in
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
  let desc = Seq.elem idx ct.classes in
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
      error_info fgens.i
        ("The");
    desc.publ <- Some {hmark=hm2; fgs=fgs; parents=TypSet.empty}
  done





let update
    (idx:   int)
    (hm:    header_mark withinfo)
    (fgens: formal_generics)
    (mt:    Module_table.t)
    (ct:    t)
    : unit =
  assert (Module_table.has_current mt);
  let desc = Seq.elem idx ct.classes
  and mdl  = Module_table.current mt
  in
  if desc.mdl = -1 then
    desc.mdl <- mdl
  else if desc.mdl = mdl then
    ()
  else
    assert false; (* Cannot update a class from a different module *)
  if Module_table.is_private mt then
    update_base_descriptor hm fgens desc.priv ct
  else
    match desc.publ with
      None ->       export idx hm fgens ct
    | Some bdesc -> update_base_descriptor hm fgens bdesc ct



let add
    (hm:    header_mark withinfo)
    (cn:    int withinfo)
    (fgens: formal_generics)
    (mt:    Module_table.t)
    (ct:    t)
    : unit =
  assert false (* nyi: insertion of new classes *)




let get_type
    (tp:type_t withinfo)
    (ntvs: int)
    (fgs: (int*type_term) array)
    (ct:t)
    : term =
  (** Convert the syntactic type [tp] in an environment with [ntvs] type
      variables and then formal generics [fgs] into a type term *)
  let nfgs = Array.length fgs in
  let n    = ntvs + nfgs in
  let cls_idx (name:int): int =
    try
      ntvs + (Search.array_find_min (fun (n,_) -> n=name) fgs)
    with Not_found ->
      try
        n + (find name ct)
      with Not_found ->
        error_info tp.i ("Class " ^ (ST.string name)
                         ^ " does not exist")
  in
  match tp.v with
    Normal_type (path,name,actuals) ->
      assert (actuals = []); (* nyi: generic types *)
      Variable (cls_idx name)
  | _ -> not_yet_implemented tp.i "types other than normal types"



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




let collect_formal_generics
    (entlst: entities list withinfo)
    (rt:return_type)
    (ct:t)
    : IntSet.t * int =
  (** Collect the names of all formal generics and the number of untyped
      entities of the entity list [entlst] and the return type [rt]
   *)
  let rec fgs (tp:type_t) (fgens: IntSet.t): IntSet.t =
    match tp with
      Normal_type (path,name,args) ->
        let fgens =
          try
            let _ = IntMap.find name ct.fgens
            in
            match args with
              [] -> IntSet.add name fgens
            | _ -> error_info entlst.i
                  ("Formal generic " ^  (ST.string name) ^
                   "cannot have actual generics")
          with Not_found -> fgens
        in
        fgs_list fgens args
    | Current_type lst ->
        assert false (* nyi: but might be eliminated from the language *)
    | Arrow_type (tpa,tpb) ->
        fgs tpb (fgs tpa fgens)
    | Ghost_type tp | QMark_type tp | Paren_type tp ->
        fgs tp fgens
    | Tuple_type lst ->
        fgs_list fgens lst
  and fgs_list (set:IntSet.t) (lst: type_t list) =
    List.fold_left (fun set tp -> fgs tp set) set lst
  in
  let l: type_t list =
    match rt with None -> []
    | Some tp ->
        let t,_ = tp.v in [t]
  in
  let l,ntvs  = List.fold_left
      (fun (lst,ntvs) ent->
        match ent with
          Untyped_entities vars -> lst, ntvs+(List.length vars)
        | Typed_entities (_,tp) -> tp::lst,ntvs)
      (l,0)
      entlst.v
  in
  fgs_list IntSet.empty l, ntvs



let formal_generics
    (entlst: entities list withinfo)
    (rt:     return_type)
    (fgs:    formal array)
    (ct:     t)
    : formal array * int =
  (** The formal generics and number of type variables of the entity list
      [entlst] and the return type [rt] in an environment with the formal
      generics [fgs]. *)
  let fgset, n = collect_formal_generics entlst rt ct in
  let fgset =
    Array.fold_left (fun set (name,_) -> IntSet.remove name set) fgset fgs
  in
  let fglst_rev = IntSet.fold
      (fun name lst -> (name, IntMap.find name ct.fgens)::lst)
      fgset
      []
  in
  Array.of_list (List.rev fglst_rev),
  n


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
  (** The result type with corresponds to the return type [rt] in an
      environment with the formal generics [fgs] and [ntvs] type variables *)
  match rt with
    None -> Result_type.empty
  | Some tpinf ->
      let tp,proc = tpinf.v in
      let t = get_type (withinfo tpinf.i tp) ntvs fgs ct in
      Result_type.make t proc


let rec satisfies (t1:type_term) (fgs: formal array) (cpt:type_term) (ct:t)
    : bool =
  (** Does the type [t] which might contain the formal generics [fgs] satisfy
      the concept [cpt]?  *)
  let nfgs = Array.length fgs in
  match t1 with
    Variable i when i < nfgs ->
      let cpt_t1 = snd fgs.(i) in
      satisfies cpt_t1 [||] cpt ct
  | _ ->
      (Array.length fgs = 0 && t1 = cpt)


let empty_table (): t =
  let cc = Seq.empty ()
  in
  {map=IntMap.empty; classes=cc; fgens=IntMap.empty}



let add_base_class
    (name:int)
    (desc:base_descriptor)
    (ct:t)
    : unit =
  let priv = desc
  and publ = Some desc
  and idx  = Seq.count ct.classes
  in
  Seq.push {mdl=(-1); name=name; priv=priv; publ=publ} ct.classes;
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
  and emppar = TypSet.empty
  and ct = empty_table ()   in
  add_base_class
    (ST.symbol "BOOLEAN")
    {hmark=Immutable_hmark; fgs=[||]; parents=emppar}
    ct;
  add_base_class
    (ST.symbol "ANY")
    {hmark=Deferred_hmark; fgs=[||]; parents=emppar}
    ct;
  add_base_class
    (ST.symbol "PREDICATE")
    {hmark=Deferred_hmark; fgs=[|fgg,anycon|]; parents=emppar}
    ct;
  add_base_class
    (ST.symbol "FUNCTION")
    {hmark=Deferred_hmark; fgs=[|(fga,anycon); (fgb,anycon)|]; parents=emppar}
    ct;
  add_base_class
    (ST.symbol "TUPLE")
    {hmark=Deferred_hmark; fgs=[|(fga,anycon); (fgb,anycon)|]; parents=emppar}
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


(*
let class2string (i:int) (ctxt:t): string =
  assert (i < count ctxt);
  let desc = Seq.elem  i ctxt.classes in
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
    ctxt.classes*)
  assert false
