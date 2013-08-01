open Support

type typ =
    Simple of int
  | Tuple of typ array
  | Generic of int * typ array
  | TLam of typ array * typ



module Class : sig
  val type_up: int -> typ -> typ
  val fgen: int -> typ
  val bool: typ
  val any:  typ
  val func: int -> typ -> typ -> typ
  val predicate: int -> typ -> typ
  val tuple2: typ -> typ -> typ
end = struct
  open Support
  module TypSet = Set.Make(struct
    let compare = Pervasives.compare
    type t = typ
  end)

  type descriptor =
      {hmark:header_mark; constraints: typ array; parents: TypSet.t}

  open Container
  type context = {names: int key_table; classes: descriptor seq}

  let count (c:context) =
    Seq.count c.classes

  let class_name (i:int) (c:context) =
    assert (i<count c);
    Support.ST.string (Key_table.key c.names i)

  let put (c:context) (hm:header_mark withinfo) (cn:int withinfo) =
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
end










