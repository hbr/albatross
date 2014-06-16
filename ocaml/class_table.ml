open Support
open Term
open Signature
open Container

module TypSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = term
end)

type formal = int * type_term

type descriptor =
    {hmark:header_mark;
     fgnames: int array; constraints: term array;
     parents: TypSet.t}

type t = {names:   int Key_table.t;
          classes: descriptor seq;
          mutable fgens: term IntMap.t}

let zero_index      = 0
let boolean_index   = 1
let any_index       = 2
let predicate_index = 3
let function_index  = 4
let tuple_index     = 5

let count (c:t) =
  Seq.count c.classes

let class_name (i:int) (c:t) =
  assert (i<count c);
  Support.ST.string (Key_table.key i c.names)



let put (hm:header_mark withinfo) (cn:int withinfo) (c:t) =
  try
    let idx = Key_table.find cn.v c.names in
    let desc = Seq.elem idx c.classes in
    if hm.v <> desc.hmark then
      let str =
        "Header mark should be \""
        ^ (hmark2string desc.hmark)
        ^ "\"\n"
      in
      error_info hm.i str
    else
      ()
  with Not_found ->
    not_yet_implemented cn.i "Insertion of new classes"

let boolean_type (ntvs:int)  = Variable (boolean_index+ntvs)
let any (ntvs:int)           = Variable (any_index+ntvs)
let zero (ntvs:int)          = Variable (zero_index+ntvs)
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
        n + (Key_table.find name ct.names)
      with Not_found ->
        error_info tp.i ("Class " ^ (ST.string name)
                         ^ " does not exist")
  in
  match tp.v with
    Normal_type (path,name,actuals) ->
      assert (actuals = []); (* nyi: generic types *)
      Variable (cls_idx name)
  | _ -> not_yet_implemented tp.i "types other than normal types"



let get_type0
    (tp:type_t withinfo)
    (fgnames: int array)
    (ct:t)
    : term =
  (** Convert the syntactic type [tp] in an environment with the formal
      generic names [fgnames] into a type term
   *)
  let nfgs = Array.length fgnames in
  let cls_idx (name:int): int =
    try
      Search.array_find_min (fun n -> n=name) fgnames
    with Not_found ->
      try
        (Key_table.find name ct.names) + nfgs
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
  and kt = Key_table.empty ()
  in
  {names=kt; classes=cc; fgens=IntMap.empty}


let base_table (): t =
  let bt = empty_table () in
  let cc = bt.classes
  and kt = bt.names
  in
  let index cname = Key_table.index (Support.ST.symbol cname) kt
  in
  let zero_idx  = index "@ZERO"
  and bool_idx  = index "BOOLEAN"
  and any_idx   = index "ANY"
  and pred_idx  = index "PREDICATE"
  and func_idx  = index "FUNCTION"
  and tuple_idx = index "TUPLE"
  in
  assert (zero_idx=zero_index);
  assert (bool_idx=boolean_index);
  assert (any_idx=any_index);
  assert (pred_idx=predicate_index);
  assert (func_idx=function_index);
  assert (tuple_idx=tuple_index);
  let fgg = ST.symbol "G"
  and fga = ST.symbol "A"
  and fgb = ST.symbol "B"
  in
  Seq.push {hmark = No_hmark;
            fgnames = [||]; constraints = [||];
            parents = TypSet.empty } cc; (*@ZERO*)

  Seq.push {hmark = Immutable_hmark;
            fgnames = [||]; constraints = [||];
            parents = TypSet.empty} cc; (*BOOLEAN*)

  Seq.push {hmark = Deferred_hmark;
            fgnames = [||]; constraints = [||];
            parents = TypSet.empty } cc; (*ANY*)

  Seq.push {hmark = Immutable_hmark;
            fgnames = [|fgg|]; constraints = [|any 0|];
            parents = TypSet.empty} cc; (*PREDICATE*)

  Seq.push {hmark = Immutable_hmark;
            fgnames = [|fga;fgb|]; constraints = [|any 0; any 0|];
            parents = TypSet.empty} cc; (*FUNCTION*)

  Seq.push {hmark = Immutable_hmark;
            fgnames = [|fga;fgb|]; constraints = [|any 0; any 0|];
            parents =TypSet.empty} cc; (*TUPLE*)
  {names=kt; classes=cc; fgens=bt.fgens}




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

let print ctxt =
  Seq.iteri
    (fun i c -> Printf.printf "%s\n" (class2string i ctxt))
    ctxt.classes
