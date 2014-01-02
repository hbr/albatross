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

let any_index       = 0
let boolean_index   = 1
let predicate_index = 2
let function_index  = 3
let tuple_index     = 4

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

let boolean = Simple boolean_index
let any     = Simple any_index
let func nb dom ran = Generic(nb+3,[|dom;ran|])


let boolean_type (ct:t): typ = boolean

let is_boolean_binary (args: typ array) (ret:typ): bool =
  ret=boolean
    && (Array.length args)=2
    && args.(0)=boolean
    && args.(1)=boolean

let is_boolean_unary (args: typ array) (ret:typ): bool =
  ret=boolean
    && (Array.length args)=1
    && args.(0)=boolean



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
      assert (i=function_index);
      assert ((Array.length tarr) = 2);
      let rec arglist (t:typ) (l:typ list): typ list =
        match t with
          Generic (i,tarr) ->
            if i = tuple_index then begin
              assert ((Array.length tarr) = 2);
              tarr.(0) :: (arglist tarr.(1) l)
            end else
              t::l
        | _ -> t::l
      in
      Array.of_list (arglist tarr.(0) []), tarr.(1)
  | _ -> assert false



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
  let argnames = List.rev_map (fun e -> let n,_ = e in n) args
  and argtypes = List.rev_map (fun e -> let _,t = e in t) args
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
    let arglen = Array.length argtypes in
    if arglen = 0 then
      ret
    else
      let rec arg_type (n:int): typ =
        assert (n>0);
        if n=1 then argtypes.(arglen-n)
        else Generic(tuple_index,
                     [| argtypes.(arglen-n); arg_type (n-1)|])
      in
      func 0 (arg_type arglen) ret
  in
  argtypes, ret, function_type, argnames




let base_table () =
  let cc = Seq.empty ()
  and kt = Key_table.empty ()
  in
  let index cname = Key_table.index kt (Support.ST.symbol cname)
  in
  let any_idx   = index "ANY"
  and bool_idx  = index "BOOLEAN"
  and pred_idx  = index "PREDICATE"
  and func_idx  = index "FUNCTION"
  and tuple_idx = index "TUPLE"
  in
  assert (bool_idx=boolean_index);   assert (any_idx=any_index);
  assert (pred_idx=predicate_index); assert (func_idx=function_index);
  assert (tuple_idx=tuple_index);
  Seq.push cc {hmark = Deferred_hmark; constraints = [||];
               parents = TypSet.empty };
  Seq.push cc {hmark = Immutable_hmark; constraints = [||];
               parents = TypSet.empty};
  Seq.push cc {hmark = Immutable_hmark; constraints = [|any|];
               parents = TypSet.empty};
  Seq.push cc {hmark = Immutable_hmark; constraints = [|any;any|];
               parents = TypSet.empty};
  Seq.push cc {hmark = Immutable_hmark; constraints = [|any;any|];
               parents =TypSet.empty};
  {names=kt; classes=cc}




let type2string (t:typ) (nb:int) (ct:t): string =
  let rec to_string(t:typ) (nb:int) (prec:int): string =
    let args_to_string (tarr:typ array) (nb:int): string =
      "["
      ^ (String.concat ","
           (Array.to_list (Array.map (fun t -> to_string t nb 1) tarr)))
      ^ "]"
    in
    let inner_prec, str =
      match t with
        Simple j ->
          1, if j<nb then string_of_int j else class_name (j-nb) ct
      | Generic (j,tarr) ->
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
            (to_string (Simple j) nb 1) ^ (args_to_string tarr nb)
          end
      | TLam (arr,t) ->
          let len = Array.length arr in
          1,
          (args_to_string arr nb) ^ (to_string t (nb+len) 1)
    in
    if inner_prec < prec then "(" ^ str ^ ")" else str
  in
  to_string t nb 0




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
             ^ ":" ^ (type2string tp 0 ct))
           llst)
    ^ ")"
