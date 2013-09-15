open Support
open Type
open Container

module TypSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = typ
end)


type descriptor =
    {hmark:header_mark; constraints: typ array; parents: TypSet.t}

type t = {names: int key_table; classes: descriptor seq}

let boolean_index   = 0
let any_index       = 1
let predicate_index = 2
let function_index  = 3

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

let fgen i = Simple i
let bool = Simple 0
let any  = Simple 1
let func nb dom ran = Generic(nb+3,[|dom;ran|])
let predicate nb g = Generic(nb+2,[|g|])
let tuple1 a   = Tuple [|a|]
let tuple2 a b = Tuple [|a;b|]
let pset_any nb = TypSet.singleton (Class.type_up nb any)


let boolean_type (ct:t): typ = bool

let boolean_binary (ct:t): typ =
  func 0 (tuple2 bool bool) bool

let boolean_unary (ct:t): typ =
  func 0 (tuple1 bool) bool



let get_type (tp:type_t withinfo) (ct:t) =
  match tp.v with
    Normal_type (path,name,actuals) -> begin
      assert (actuals = []);
      try
        let idx = Key_table.find ct.names name in
        Simple idx
      with Not_found ->
        error_info tp.i ("Class " ^ (ST.string name)
                         ^ " does not exist")
    end
  | _ -> not_yet_implemented tp.i "types other than normal types"



let split_function (function_type:typ) (ct:t): typ array * typ =
  match function_type with
    Generic (i,tarr) ->
      if i<>function_index then
        failwith "is not a function"
      else begin
        assert ((Array.length tarr) = 2);
        match tarr.(0) with
          Tuple args -> args,tarr.(1)
        | _ -> assert false  (* always a tuple! *)
      end
  | _ -> failwith "is not a function"




let arguments
    (entlst: entities list withinfo)
    (ct:t): int array * typ array =
  let args: (int*typ)list =
    List.flatten
      (List.map
         (fun es ->
           match es with
             Untyped_entities _ ->
               error_info entlst.i
                 ("Arguments must be fully typed "
                  ^ "in top level declarations")
           | Typed_entities (lst,tp) ->
               let t = get_type (withinfo entlst.i tp) ct
               in
               List.map (fun name -> name,t) lst)
         entlst.v)
  in
  let argnames = List.map (fun e -> let n,_ = e in n) args
  and argtypes = Array.of_list (List.map (fun e -> let _,t = e in t) args)
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
  (Array.of_list argnames), argtypes


let feature_type
    (entlst: entities list withinfo)
    (rt:return_type)
    (ct:t): typ array * typ * typ * int array =
  let argnames,argtypes = arguments entlst ct
  and ret =
    match rt with
      None -> assert false
    | Some tp ->
        let t,procedure = tp.v in
        assert (not procedure);
        get_type (withinfo tp.i t) ct
  in
  let function_type =
    if (Array.length argtypes) = 0 then
      ret
    else
      func 0 (Tuple argtypes) ret
  in
  argtypes, ret, function_type, argnames


let base_table () =
  let cc = Seq.empty ()
  and kt = Key_table.empty ()
  in
  let index cname = Key_table.index kt (Support.ST.symbol cname)
  in
  let bool_idx = index "BOOLEAN"
  and any_idx  = index "ANY"
  and pred_idx = index "PREDICATE"
  and func_idx = index "FUNCTION"
  in
  assert (bool_idx=boolean_index);   assert (any_idx=any_index);
  assert (pred_idx=predicate_index); assert (func_idx=function_index);
  Seq.push cc {hmark = Immutable_hmark; constraints = [||];
               parents = pset_any 0};
  Seq.push cc {hmark = Deferred_hmark; constraints = [||];
               parents = TypSet.empty };
  Seq.push cc {hmark = Immutable_hmark; constraints = [|any|];
               parents = pset_any 1 };
  Seq.push cc {hmark = Immutable_hmark; constraints = [|any;any|];
               parents = pset_any 2};
  {names=kt; classes=cc}


let type2string (t:typ) (nb:int) (c:t) =
  let predicate = 2
  and func      = 3
  in
  let rec t2s qmark nb t =
    let arr2s nb tarr =
      String.concat
        ","
        (Array.to_list (Array.map (fun t -> t2s false nb t) tarr))
    and j2s j nb =
      if j<nb then string_of_int j
      else
        class_name (j-nb) c
    in
    let tup2s nb tarr = "[" ^ (arr2s nb tarr) ^ "]"
    in
    match t with
      Simple j -> j2s j nb
    | Tuple tarr ->
        tup2s nb tarr
    | Generic (j,tarr) ->
        let j1 = j-nb in
        if j1 = predicate then begin
          assert ((Array.length tarr)=1);
          (t2s true nb tarr.(0)) ^ "?"
        end
        else if j1 = func then begin
          assert ((Array.length tarr)=2);
          let str0 = (t2s false nb tarr.(0)) ^ "->" ^ (t2s false nb tarr.(1))
          in
          if qmark then "(" ^ str0 ^ ")" else str0
        end
        else
          (j2s j nb) ^ (tup2s nb tarr)
      | TLam (tarr,t) ->
          let len = Array.length tarr in
          (tup2s nb tarr) ^ (t2s false (nb+len) t)
  in
  t2s false nb t


let class2string (i:int) (ctxt:t) =
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
                ^ (type2string c 0 ctxt)) desc.constraints) )
        )
      ^ "]"
  and par2string =
    String.concat
      ";"
      (List.rev (TypSet.fold
                     (fun el lst -> (type2string el ngen ctxt)::lst)
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
    (types: typ array)
    (ct:t): string =
  let nargs = Array.length names in
  assert (nargs = (Array.length types));
  let args = Array.init
      nargs
      (fun i ->
        (ST.string names.(i))
        ^ ":"
        ^ (type2string types.(i) 0 ct))
  in
   if nargs=0 then
     " "
   else 
     "(" ^ (String.concat "," (Array.to_list args)) ^ ")"
