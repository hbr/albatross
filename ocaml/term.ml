open Support
open Type


type term =
    Variable    of int
  | Application of term * term array
  | Lam         of typ array * term

type feature_name =  (* Name clash with Support !!!*)
    Name of string
  | Operator of string
  | Parenthesis
  | Bracket


module Term: sig
end = struct
  open Container

  type type_descriptor =
      {fname:feature_name; typ:typ; definition: term option}

  type type_context = type_descriptor seq

  type context = {classes: Class_table.t; 
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
          (Class_table.type2string td.typ 0 cc))
      tc
      

  let base_context () =
    let tc = base_type_context () 
    and cc = Class_table.base_table ()
    in
    {classes=cc; types=tc}

  let print_context ctxt =
    Class_table.print ctxt.classes;
    print_type_context  ctxt.types

  let print =
    let c = base_context () in
    let cc = c.classes 
    and tc = c.types in
    Class_table.print cc;
    print_type_context tc cc
end



type type_context = typ array
