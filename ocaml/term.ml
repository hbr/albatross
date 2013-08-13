open Support
open Type
open Container


type term =
    Variable    of int
  | Application of term * term array
  | Lam         of typ array * term


module Term: sig

  val normalize: typ array -> term -> typ array * term * int array

end = struct

  let map (f:int->int->term) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'f j nb' where 'nb' is the
       number of bound variables in the context where 'j' appears
     *)
    let rec mapr nb t =
      match t with
        Variable j -> f j nb
      | Application (a,b) ->
          Application (mapr nb a, Array.map (fun t -> mapr nb t) b)
      | Lam (tarr,t) ->
          Lam(tarr, mapr (nb+Array.length tarr) t)
    in
    mapr 0 t



  let upbound (n:int) (start:int) (t:term): term =
    (* Shift all free variables up by 'n' from 'start' on in the term 't' *)
    map
      (fun j nb ->
        if j<nb+start then Variable(j)
        else Variable(j+n))
      t


  let up (n:int) (t:term): term =
    (* Shift all free variables up by 'n' in the term 't' *)
    upbound n 0 t




  let sub (t:term) (args:term array) (nbound:int): term =
    (* substitute the free variables 0,1,args.len-1 in term t by the
       arguments which are from an environment with 'nbound' bound variables,
       i.e. all free variables above 'len' are shifted up by 'nbound-args.len'
     *)
    let len = Array.length args in
    map
      (fun j nb ->
        if j<nb then
          Variable(j)
        else
          let jfree = j-nb in
          if jfree < len then
            args.(jfree)
          else
            Variable(j + nbound - len))
      t



(*
  let sub (t:term) (args:term array): term =
    (* substitute the free variables 0,1,args.len-1 in term t by the
       arguments and shift all other free variables down by args.len
     *)
    let len = Array.length args in
    map
      (fun j nb ->
        if j<nb then Variable(j)
        else if j-nb < len then up nb args.(j-nb)
        else Variable(j-len))
      t
*)


  let variables_below (n:int) (t:term): int list =
    (* The list of free variables below 'n' in the order in which they appear
       in the term 't'
     *)
    let rec vars (t:term) (nb:int): int list =
      match t with
        Variable j -> if j<nb || n+nb<=j then [] else [j-nb]
      | Application (t,args) ->
          let tl = vars t nb
          and al = List.map (fun t -> vars t nb) (Array.to_list args)
          in
          tl @ (List.flatten al)
      | Lam (tarr,t) ->
          vars t (nb+(Array.length tarr))
    in
    vars t 0



  type usage =
      Unused
    | Used of int   (* the first appearance *)



  let usage_array (n:int) (t:term): int * usage array =
    (* The number of used variables and the usage array of the
       variables below 'n' in the term 't'
     *)
    let varlst = variables_below n t
    and nused = ref 0
    and usearr = Array.make n Unused
    in
    let _ =
      Mylist.iteri
        (fun pos var ->
          assert (var < n);
          match usearr.(var) with
            Unused -> begin
              usearr.(var) <- Used pos;
              nused := !nused + 1
            end
          | Used _ -> ()
        )
        varlst
    in
    !nused,usearr




  let normalize (tarr: typ array) (t:term): typ array * term * int array =
    (* Normalize the term 't' with local variables of types 'tarr'
       and return the types of the used variables and the term
       where the variables have their occurrence according to the
       type array
     *)
    let len = Array.length tarr in
    let nused,usearr = usage_array len t in
    let tnorm = map
        (fun i nb ->
          if nb+len <= i then
            Variable (i-(len-nused))
          else if i < nb then
            Variable i
          else begin
            assert(nb<=i); assert((i-nb)<len);
            match usearr.(i-nb) with
              Used pos ->
                assert (pos < nused);
                Variable (nb + nused - 1 - pos)
            | Unused ->
                assert false  (* Variable i-nb must be used *)
          end
        )
        t
    in
    let vars_sorted = Array.init len (fun i -> i) in
    let _ =
      Array.sort 
        (fun i j ->
          match usearr.(i), usearr.(j) with
            Used p1, Used p2 -> compare p1 p2
          | Used _ , Unused  -> -1
          | Unused , Used _  ->  1
          | Unused , Unused  ->  0)
        vars_sorted
    in
    let tarrnorm = Array.init nused (fun i -> tarr.(vars_sorted.(i)))
    and varsused = (Array.sub vars_sorted 0 nused)
    in
    assert
      (t = (sub tnorm (Array.map (fun i -> Variable i) varsused) len));
    tarrnorm, tnorm, varsused



end

(*
module Term: sig
end = struct
  open Container

  type feature_name =  (* Name clash with Support !!!*)
      Name of string
    | Operator of string
    | Parenthesis
    | Bracket

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
*)
