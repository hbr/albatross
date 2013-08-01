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
      
let count (c:t) =
  Seq.count c.classes
    
let class_name (i:int) (c:t) =
  assert (i<count c);
  Support.ST.string (Key_table.key c.names i)
    
let put (c:t) (hm:header_mark withinfo) (cn:int withinfo) =
  try
    let idx = Key_table.find c.names cn.v in
    let desc = Seq.elem c.classes idx in
    if hm.v <> desc.hmark then
      let str = 
        "Header mark should be \"" 
        ^ (hmark2string desc.hmark) 
        ^ "\"\n"
      in
      raise (Error_info (hm.i,str))
    else
      ()
  with Not_found ->
    assert false


let fgen i = Simple i
let bool = Simple 0
let any  = Simple 1
let func nb dom ran = Generic(nb+3,[|dom;ran|])
let predicate nb g = Generic(nb+2,[|g|])
let tuple2 a b = Tuple [|a;b|]
let pset_any nb = TypSet.singleton (Class.type_up nb any)

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
  assert (bool_idx=0); assert (any_idx=1);
  assert (pred_idx=2); assert (func_idx=3);
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
  ^ con2string ^ " inherit " ^ par2string ^ " end"
                                              
let print ctxt =
  Seq.iteri 
    (fun i c -> Printf.printf "%s\n" (class2string i ctxt))
    ctxt.classes
    
