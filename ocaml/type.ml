type typ =
    Simple of int
  | Tuple of typ array
  | Generic of int * typ array
  | TLam of typ array * typ

type term =
    Variable    of int
  | Application of term * term array
  | Lam         of typ array * term

type feature_name =
    Name of string
  | Operator of string
  | Parenthesis
  | Bracket

module Class : sig
  type context
  val base_context: unit -> context
  val print_context: context -> unit
  val type2string: typ -> int -> context -> string
  val type_up: int -> typ -> typ
  val fgen: int -> typ
  val bool: typ
  val any:  typ
  val func: int -> typ -> typ -> typ
  val predicate: int -> typ -> typ
  val tuple2: typ -> typ -> typ
end = struct
  module TypSet = Set.Make(struct
    let compare = Pervasives.compare
    type t = typ
  end)

  type descriptor =
      {cname:string; constraints: typ array; parents: TypSet.t}

  open Container
  type context = {names: int key_table; classes: descriptor seq}

  let count (c:context) =
    Seq.count c.classes

  let class_name (i:int) (c:context) =
    assert (i<count c);
    Support.ST.string (Key_table.key c.names i)

  let type_map (f:int->int->int) (t:typ) =
    let rec map nb t = 
      match t with
         Simple j -> Simple (f j nb)
      | Tuple tarr ->
          Tuple (Array.map (fun t -> map nb t) tarr)
      | Generic (j,tarr) ->
          Generic (f j nb, Array.map (fun t -> map nb t) tarr)
      | TLam (tarr,t) ->
          TLam(tarr, map (nb+Array.length tarr) t)
    in
    map 0 t

  let type_up (i:int) (t:typ) =
    (* Shift all classes up by 'i' in type 't' *)
    type_map 
      (fun j nb ->
        if j<nb then j
        else j+i)
      t

  let type_sub (t:typ) (args:typ array) =
    let len = Array.length args in
    let rec sub nb t =
      match t with
        Simple j ->
          if j<nb then Simple j
          else if j-nb<len then type_up nb args.(j-nb)
          else Simple (j-len)
      | Tuple tarr ->
          Tuple(Array.map (fun t -> sub nb t) tarr)
      | Generic (j,tarr) ->
          assert (nb+len<j);
          Generic (j-len, Array.map (fun t-> sub nb t) tarr)
      | TLam(tarr,t) ->
          TLam(tarr, sub (nb+Array.length tarr) t)
    in
    sub 0 t


  let fgen i = Simple i
  let bool = Simple 0
  let any  = Simple 1
  let func nb dom ran = Generic(nb+3,[|dom;ran|])
  let predicate nb g = Generic(nb+2,[|g|])
  let tuple2 a b = Tuple [|a;b|]
  let pset_any nb = TypSet.singleton (type_up nb any)

  let base_context () =
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
    Seq.push cc {cname = "BOOLEAN"; constraints = [||]; 
                 parents = pset_any 0};
    Seq.push cc {cname = "ANY"; constraints = [||];
                 parents = TypSet.empty };
    Seq.push cc {cname = "PREDICATE"; constraints = [|any|];
                 parents = pset_any 1 };
    Seq.push cc {cname = "FUNCTION"; constraints = [|any;any|];
                 parents = pset_any 2};
    {names=kt; classes=cc}




  let type2string (t:typ) (nb:int) (c:context) =
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


  let class2string (i:int) (ctxt:context) =
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
    "class " ^ (class_name i ctxt) 
    ^ con2string ^ " inherit " ^ par2string ^ " end"

  let print_context ctxt =
    Seq.iteri 
      (fun i c -> Printf.printf "%s\n" (class2string i ctxt))
      ctxt.classes
end










module Term: sig
end = struct
  open Container

  type type_descriptor =
      {fname:feature_name; typ:typ; definition: term option}

  type type_context = type_descriptor seq

  type context = {classes: Class.context; 
                  types: type_descriptor seq}


  let term_map (f:int->int->term) (t:term) =
    let rec map nb t =
      match t with
        Variable j -> f j nb
      | Application (a,b) ->
          Application (map nb a, Array.map (fun t -> map nb t) b)
      | Lam (tarr,t) ->
          Lam(tarr, map (nb+Array.length tarr) t)
    in
    map 0 t

  let term_up (n:int) (t:term) =
    term_map (fun j i -> if j<i then Variable(j) else Variable(j+n)) t

  (* substitute the free variables 0,1,args.len-1 in term t by the arguments
     and shift all other free variables down by args.len *)
  let term_sub (t:term) (args:term array) =
    let len = Array.length args in
    term_map
      (fun j nb ->
        if j<nb then Variable(j)
        else if j-nb < len then term_up nb args.(j-nb)
        else Variable(j-len))
      t


  let base_type_context () =
    let tc = Seq.empty ()
    and func = Class.func
    and fgen = Class.fgen
    and tuple2 = Class.tuple2
    and bool   = Class.bool
    and predicate = Class.predicate
    and any = Class.any
    in
    Seq.push tc {fname = Operator "=>";
                 typ = func 0 (tuple2 bool bool) bool;
                 definition = None};
    Seq.push tc {fname = Operator "=" ; 
                 typ = TLam([|any|],
                            func 1
                              (tuple2 (fgen 0) (fgen 0)) 
                              (Class.type_up 1 bool));
                 definition = None};
    Seq.push tc {fname = Operator "in";
                 typ = TLam ([|any|],
                             func 1
                               (tuple2 (fgen 0) (predicate 1 (fgen 0)))
                               (Class.type_up 1 bool));
                 definition = None};
    tc

  let print_type_context tc cc =
    Seq.iter
      (fun td -> Printf.printf "%s  %s\n" 
          (match td.fname with Name s -> s 
          | Operator s -> s 
          | Parenthesis -> "()" 
          | Bracket -> "[]")
          (Class.type2string td.typ 0 cc))
      tc
      

  let base_context () =
    let tc = base_type_context () 
    and cc = Class.base_context ()
    in
    {classes=cc; types=tc}

  let print_context ctxt =
    Class.print_context ctxt.classes;
    print_type_context  ctxt.types

  let print =
    let c = base_context () in
    let cc = c.classes 
    and tc = c.types in
    Class.print_context cc;
    print_type_context tc cc
end



type type_context = typ array
