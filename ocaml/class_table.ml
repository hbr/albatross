open Support
open Term
open Signature
open Container

module TypSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = term
end)


type descriptor =
    {hmark:header_mark;
     fgnames: int array; constraints: term array;
     parents: TypSet.t}

type t = {names:   int key_table;
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
  Support.ST.string (Key_table.key c.names i)



let put (hm:header_mark withinfo) (cn:int withinfo) (c:t) =
  try
    let idx = Key_table.find c.names cn.v in
    let desc = Seq.elem c.classes idx in
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

let boolean_type  = Variable boolean_index
let any           = Variable any_index
let zero          = Variable zero_index
let func nb dom ran = Application(Variable(nb+function_index),[|dom;ran|])



let is_boolean_binary (args: term array) (ret:term): bool =
  ret=boolean_type
    && (Array.length args)=2
    && args.(0)=boolean_type
    && args.(1)=boolean_type

let is_boolean_unary (args: term array) (ret:term): bool =
  ret=boolean_type
    && (Array.length args)=1
    && args.(0)=boolean_type



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





let get_type
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
      Search.array_find_min name fgnames
    with Not_found ->
      try
        (Key_table.find ct.names name) + nfgs
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
  (* Add the formal generic with name and concept to the formal generics of
     the class table *)
  if IntMap.mem name.v ct.fgens then
    error_info
      name.i
      ("formal generic " ^ (ST.string name.v) ^ " already defined")
  else
    ct.fgens <- IntMap.add
        name.v
        (get_type concept  [||] ct)
        ct.fgens




let arguments
    (entlst: entities list withinfo)
    (fgnames: int array)
    (ct:t)
    : int array * type_term array =
  let args: (int*term) list =
    List.flatten
      (List.map
         (fun es ->
           match es with
             Untyped_entities lst ->
               List.mapi (fun i name -> name, Variable i) lst
           | Typed_entities (lst,tp) ->
               let t = get_type (withinfo entlst.i tp) fgnames ct
               in
               List.map (fun name -> name,t) lst)
         entlst.v)
  in
  let argnames = List.rev_map (fun e -> let n,_ = e in n) args (*reindex*)
  and argtypes = List.rev_map (fun e -> let _,t = e in t) args (*reindex*)
  in
  let rec check_names (namelst: int list) =
    match namelst with
      [] -> ()
    | f::t ->
        if List.mem f t then
          error_info entlst.i
            ("Duplicate argument \"" ^ (ST.string f) ^ "\"" )
        else check_names t
  in
  check_names argnames;
  (Array.of_list argnames), (Array.of_list argtypes)




let signature
    (entlst: entities list withinfo)
    (rt:return_type)
    (fgnames0:  int array)
    (concepts0: type_term array)
    (argnames0: int array)
    (ntvs0:     int)
    (ct:t)
    : int array * type_term array * int array * int * Sign.t =
  (** Analyze the syntactic signature [entlst,rt] based on an environment
      which has already the formal generics [fgnames0] with their constraints
      [concepts0] and the arguments [argnames0] and the number of type
      variables [ntvs0]
   *)
  let fgens, ntvs = (* Set of formal generics names and number of type vars *)
    collect_formal_generics entlst rt ct
  in
  let fgens =
    Array.fold_left (fun set name -> IntSet.remove name set) fgens fgnames0
  in
  let fgnames,concepts =
    let ns,cs =
      IntSet.fold
        (fun name (ns,cs) ->
          name::ns,
          (IntMap.find name ct.fgens)::cs)
        fgens
        ([], [])
    in
    Array.of_list (List.rev ns), Array.of_list (List.rev cs)
  in
  let fgnames  = Array.append fgnames  fgnames0
  and concepts = Array.append concepts concepts0
  in
  let argnames,argtypes = arguments entlst fgnames ct
  in
  let argnames = Array.append argnames argnames0
  in
  let sign =
    match rt with
      None -> Sign.make_args argtypes
    | Some tpinf ->
        let tp,proc = tpinf.v in
        let t = get_type (withinfo tpinf.i tp) fgnames ct in
        if proc then Sign.make_proc argtypes t
        else Sign.make_func argtypes t
  in
  fgnames, concepts, argnames, (ntvs0+ntvs), sign




let argument_signature
    (entlst: entities list withinfo)
    (ct:t)
    : int array * type_term array * int array * type_term array =
  let fgnames, concepts, argnames, _, sign =
    signature entlst None [||] [||] [||] 0 ct
  in
  fgnames, concepts, argnames, Sign.arguments sign








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
  let index cname = Key_table.index kt (Support.ST.symbol cname)
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
  Seq.push cc {hmark = No_hmark;
               fgnames = [||]; constraints = [||];
               parents = TypSet.empty }; (*@ZERO*)

  Seq.push cc {hmark = Immutable_hmark;
               fgnames = [||]; constraints = [|zero|];
               parents = TypSet.empty}; (*BOOLEAN*)

  Seq.push cc {hmark = Deferred_hmark;
               fgnames = [||]; constraints = [|zero|];
               parents = TypSet.empty }; (*ANY*)

  Seq.push cc {hmark = Immutable_hmark;
               fgnames = [|fgg|]; constraints = [|any|];
               parents = TypSet.empty}; (*PREDICATE*)

  Seq.push cc {hmark = Immutable_hmark;
               fgnames = [|fga;fgb|]; constraints = [|any;any|];
               parents = TypSet.empty}; (*FUNCTION*)

  Seq.push cc {hmark = Immutable_hmark;
               fgnames = [|fga;fgb|]; constraints = [|any;any|];
               parents =TypSet.empty}; (*TUPLE*)
  {names=kt; classes=cc; fgens=bt.fgens}




let type2string (t:term) (nb:int) (fgnames: int array) (ct:t): string =
  (** Convert the type term [t] in an environment with [nb] type variables
      and the formal generics [fgnames]
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
          let j1 = j-nb
          and tarrlen = Array.length tarr in
          if j1 = predicate_index then begin
            assert (tarrlen=1);
            1, ((to_string tarr.(0) nb 2) ^ "?")
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
      | Lam (len,t) ->
          assert false (*nyi*)
          (*let len = Array.length arr in
          1,
          (args_to_string arr nb) ^ (to_string t (nb+len) 1)*)
    in
    if inner_prec < prec then "(" ^ str ^ ")" else str
  in
  to_string t nb 0




let class2string (i:int) (ctxt:t): string =
  assert (i < count ctxt);
  let desc = Seq.elem  ctxt.classes i in
  let ngen = Array.length desc.constraints in
  let con2string =
    if ngen = 0 then ""
    else
      "["
      ^ (String.concat
             ","
           (Array.to_list
              (Array.mapi (fun i c ->
                (string_of_int (ngen-1-i))
                ^ ":"
                ^ (type2string c 0 [||] ctxt)) desc.constraints) )
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



let arguments_to_string
    (names: int array)
    (types: term array)
    (ct:t): string =
  let nargs = Array.length names in
  assert (nargs = (Array.length types));
  if nargs=0 then
      " "
  else
    let zipped =
      Array.to_list (Array.init nargs
                       (fun i -> let j=nargs-1-i in names.(j),types.(j)))
    in
    let llst =
      List.fold_left
        (fun ll (n,tp) ->
          match ll with
            [] -> [[n],tp]
          | (ns,tp1)::tl ->
              if tp=tp1 then
                [n::ns,tp]
              else
                ([n],tp)::ll
        )
        []
        zipped
    in
    "("
    ^  String.concat
        ","
        (List.rev_map
           (fun (ns,tp) ->
             (String.concat "," (List.rev_map (fun n -> ST.string n) ns))
             ^ ":" ^ (type2string tp 0 [||] ct))
           llst)
    ^ ")"