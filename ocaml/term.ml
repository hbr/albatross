open Support
open Type
open Container


type term =
    Variable    of int
  | Application of term * term array
  | Lam         of typ array * term



module Term: sig

  val to_string: term -> string

  val nodes: term -> int

  val bound_variables: term -> int -> IntSet.t

  val map: (int->int->term) -> term -> term

  val upbound: int->int->term->term

  val up: int->term->term

  val sub:   term -> term array -> int -> term

  val apply: term -> term array -> term

  val reduce: term -> term

  val normalize: typ array -> term -> typ array * term * int array

  val unify: term -> int -> term -> int -> term array * bool array

end = struct

  let rec to_string (t:term): string =
    match t with
      Variable i -> string_of_int i
    | Application (f,args) ->
        let fstr = to_string f
        and argsstr = Array.to_list (Array.map to_string args)
        in
        fstr ^ "(" ^
        (String.concat "," argsstr)
        ^ ")"
    | Lam(tarr,t) ->
        let len = Array.length tarr in
        let args = Array.init len (fun i -> (string_of_int (len-1-i))) in
        let argsstr = String.concat "," (Array.to_list args) in
        "([" ^ argsstr ^ "]->" ^ (to_string t) ^ ")"


  let rec nodes (t:term): int =
    (* The number of nodes in the term t *)
    match t with
      Variable _ -> 1
    | Application (f,args) ->
        (Array.fold_left (fun sum t -> sum + (nodes t)) (nodes f) args)
    | Lam (tarr,t) ->
        1 + (nodes t)


  let bound_variables (t:term) (nb:int): IntSet.t =
    let rec bvars t nb set =
      match t with
        Variable i ->
          if i<nb then
            IntSet.add i set
          else
            set
      | Application (f,args) ->
          let fset = bvars f nb set
          and asets = Array.map (fun t -> bvars t nb set) args
          in
          Array.fold_left
            (fun cum_set set -> IntSet.union cum_set set)
            fset
            asets
      | Lam (tarr,t) ->
          bvars t (nb+(Array.length tarr)) set
    in
    bvars t nb IntSet.empty


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
            args.(len-1-jfree)
          else
            Variable(j + nbound - len)
      )
      t




  let apply (t:term) (args: term array): term =
    (* Reduce (beta reduction) the term ([v0,v1,...]->t)(a0,a1,...) i.e.
       apply the function ([v0,v1,...]->t) to the arguments in args
     *)
    sub t args 0




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



  let rec reduce (t:term): term =
    (* Do all possible beta reductions in the term 't' *)
    let app (f:term) (args: term array): term =
      match f with
        Lam(tarr,t) ->
          assert ((Array.length tarr)=(Array.length args));
          apply t args
      | _ -> Application (f,args)
    in
    match t with
      Variable _ -> t
    | Application (f,args) ->
        let fr = reduce f
          and argsr = Array.map reduce args
        in
        app fr argsr
    | Lam(tarr,t) ->
        Lam (tarr, reduce t)




  let unify (t1:term) (nb1:int) (t2:term) (nb2:int)
      : term array * bool array =
    (* Find a substitution (i.e. an array of arguments) for the nb2 bound
       variable of the term t2 so that t1 = Lam(nb2,t2) (args). Clearly the
       size of args must be nb2. The term t1 is in an environment with nb1
       bound variables.

       The array of flags indicate which bound variables do occur in t2.
     *)
    let args  = Array.make nb2 t1
    and flags = Array.make nb2 false
    in
    let notfound_unless (cond:bool): unit =
      if cond then () else raise Not_found
    in
    let rec uni t1 t2 =
      match t1,t2 with
        _, Variable i2 ->
          if i2<nb2 then
            begin
              if not flags.(i2) then
                (args.(nb2-1-i2) <- t1;
                 flags.(i2) <- true)
              else
                notfound_unless (args.(nb2-1-i2)=t1)
            end
          else begin
            match t1 with
              Variable i1 ->
                notfound_unless ((i1-nb1) = (i2-nb2))
            | _ -> raise Not_found
          end
      | Application (f1,args1), Application (f2,args2) ->
          let l1,l2 = Array.length args1, Array.length args2 in
          if l1=l2 then begin
            uni f1 f2;
            Array.iteri (fun i e -> uni e args2.(i)) args1
          end
          else
            raise Not_found
      | Lam(tarr1,u1), Lam(tarr2,u2) ->
          let l1,l2 = Array.length tarr1, Array.length tarr2 in
          if l1=l2 then
            uni u1 u2
          else
            raise Not_found
      | _ -> raise Not_found
    in
    uni t1 t2;
    assert (t1 = (sub t2 args nb1));
    args,flags

end
