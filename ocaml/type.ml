module Type : sig
  type typ =
      Simple of int
    | Tuple of typ array
    | Generic of int * typ array
    | TLam of typ array * typ
  type term =
      Variable    of int
    | Application of term * term array
    | Lam         of typ array * term
  type context
  val base_context: unit -> context
  val type_up: int -> typ -> typ
  val fgen: int -> typ
  val bool: typ
  val any:  typ
  val func: typ -> typ -> typ
  val predicate: typ -> typ
end = struct
  type typ =
      Simple of int
    | Tuple of typ array
    | Generic of int * typ array
    | TLam of typ array * typ
  type term =
      Variable    of int
    | Application of term * term array
    | Lam         of typ array * term

  module TypSet = Set.Make(struct
    let compare = Pervasives.compare
    type t = typ
  end)

  type class_descriptor =
      {cname:string; constraints: typ array; parents: TypSet.t}

  type name =
      Name of string
    | Operator of string

  type type_descriptor =
      {fname:name; typ:typ}

  open Container
  type context = {classes: class_descriptor seq; 
                  types: type_descriptor seq}

  let type2string (t:typ) (c:context) =
    let cs = c.classes in
    let rec t2s nb t =
      let arr2s nb tarr = 
        String.concat 
          "," 
          (Array.to_list (Array.map (fun t -> t2s nb t) tarr))
      and j2s j nb =
        if j<nb then string_of_int j
        else begin
          assert (j+nb<Seq.count cs);
          (Seq.elem cs (j+nb)).cname
        end
      in
      let tup2s nb tarr = "[" ^ (arr2s nb tarr) ^ "]"
      in
      match t with
        Simple j -> j2s j nb
      | Tuple tarr ->
          tup2s nb tarr
      | Generic (j,tarr) ->
          (j2s j nb) ^ (tup2s nb tarr)
      | TLam (tarr,t) ->
          let len = Array.length tarr in
          (tup2s nb tarr) ^ (t2s (nb+len) t)
    in
    t2s 0 t

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

  let fgen i = Simple i
  let bool = Simple 0
  let any  = Simple 1
  let func dom ran = Generic(3,[|dom;ran|])
  let predicate g = Generic(2,[|g|])
  let tuple2 a b = Tuple [|a;b|]
  let pset_any = TypSet.singleton (any)


  let base_context () =
    let cc = Seq.empty ()
    and tc = Seq.empty ()
    in
    Seq.push cc {cname = "BOOLEAN"; constraints = [||]; 
                 parents = pset_any};
    Seq.push cc {cname = "ANY"; constraints = [||];
                 parents = TypSet.empty };
    Seq.push cc {cname = "PREDICATE"; constraints = [|any|];
                 parents = pset_any };
    Seq.push cc {cname = "FUNCTION"; constraints = [|any;any|];
                 parents = pset_any };
    Seq.push tc {fname = Operator "=>"; typ = func (tuple2 bool bool) bool};
    Seq.push tc {fname = Operator "=" ; 
                 typ = TLam([|any|],
                            func 
                              (tuple2 (fgen 0) (fgen 0)) 
                              (type_up 1 bool))};
    {classes=cc; types=tc}
end

type typ = Type.typ




(*
module Term: sig
end = struct
  open Container
  type name =
      Name of string
    | Operator of string
  type type_descriptor =
      {fname:name; typ:typ}
  type context =  type_descriptor seq

  let base_context () =
    let tc = Seq.empty ()
    in
    Seq.push tc {fname = Operator "=>"; 
                 typ = Type.func (Type.Tuple [|Type.bool;Type.bool|]) 
                   Type.bool};
    Seq.push tc {fname = Operator "=" ; 
                 typ = Type.TLam([|Type.any|],
                            Type.func 
                              (Type.Tuple [|Type.fgen 0;Type.fgen 0|]) 
                              (Type.up 1 Type.bool))};
    tc
end


*)
type type_context = typ array
