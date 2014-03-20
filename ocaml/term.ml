open Support
open Container


type term =
    Variable    of int
  | Application of term * term array
  | Lam         of int * int array * term


exception Term_capture

module TermSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = term
end)

module TermMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = term
end)






module Term: sig

  val is_variable: term -> int -> bool

  val to_string: term -> string

  val nodes: term -> int

  val depth: term -> int

  val split_variables: term -> int -> IntSet.t * IntSet.t

  val free_variables: term -> int -> IntSet.t

  val bound_variables: term -> int -> IntSet.t

  val no_names: term -> term

  val map: (int->int->term) -> term -> term

  val down_from: int -> int -> term -> term

  val down: int -> term -> term

  val upbound: int->int->term->term

  val up: int->term->term

  val sub_var: int -> term -> term -> term

  val part_sub: term -> int -> term array -> int -> term

  val sub:   term -> term array -> int -> term

  val apply: term -> term array -> term

  val abstract: term -> int array -> term

  val reduce: term -> term

  val lambda_split: term -> int * int array * term

  val unary: int -> term -> term

  val unary_split: term -> int -> term

  val binary: int -> term -> term -> term

  val binary_split: term -> int -> term * term

  val binary_right: term -> int -> term list

  val implication_chain2: term -> int -> term list * term

  val implication_chain: term -> int -> (term list * term) list

end = struct

  let is_variable (t:term) (i:int): bool =
    match t with
      Variable j when i=j -> true
    | _                   -> false


  let rec to_string (t:term): string =
    match t with
      Variable i -> string_of_int i
    | Application (f,args) ->
        let fstr = to_string f
        and argsstr = Array.to_list (Array.map to_string args)
        in
        fstr ^ "(" ^
        (String.concat "," (List.rev argsstr))
        ^ ")"
    | Lam(nargs,names,t) ->
        let nnames = Array.length names in
        assert (nnames=0 || nnames=nargs);
        let args = Array.init nargs
            (fun i ->
              if nnames = 0 then (string_of_int i)
              else ST.string names.(i))
        in
        let argsstr = String.concat "," (Array.to_list args) in
        "([" ^ argsstr ^ "]->" ^ (to_string t) ^ ")"




  let rec nodes (t:term): int =
    (* The number of nodes in the term t *)
    match t with
      Variable _ -> 1
    | Application (f,args) ->
        (Array.fold_left (fun sum t -> sum + (nodes t)) (nodes f) args)
    | Lam (_,_,t) ->
        1 + (nodes t)


  let rec depth (t:term): int =
    (* The depth of the term t *)
    match t with
      Variable _ -> 0
    | Application (f,args) ->
        Mylist.sum depth (1 + (depth f)) (Array.to_list args)
    | Lam (_,_,t) ->
        1 + (depth t)



  let split_variables (t:term) (nb:int): IntSet.t * IntSet.t =
    (* The set of bound variables strictly below 'n' and above 'n'
       in the term 't' *)
    let rec bfvars t nb bset fset =
      match t with
        Variable i ->
          if i<nb then
            (IntSet.add i bset), fset
          else
            bset, (IntSet.add i fset)
      | Application (f,args) ->
          let fbset,ffset = bfvars f nb bset fset
          and asets = Array.map (fun t -> bfvars t nb bset fset) args
          in
          Array.fold_left
            (fun (cum_bset,cum_fset) (bset,fset) ->
              IntSet.union cum_bset bset,
              IntSet.union cum_fset fset)
            (fbset,ffset)
            asets
      | Lam (nargs,_,t) ->
          bfvars t (nb+nargs) bset fset
    in
    bfvars t nb IntSet.empty IntSet.empty


  let free_variables (t:term) (nb:int): IntSet.t =
    (* The set of free variables above 'n' in the term 't' *)
    let _,fvars = split_variables t nb
    in
    fvars



  let bound_variables (t:term) (nb:int): IntSet.t =
    (* The set of bound variables strictly below 'n' in the term 't' *)
    let bvars,_ = split_variables t nb
    in
    bvars


  let rec no_names (t:term): term =
    (** The term [t] with all names in abstractions erased.
     *)
    match t with
      Variable _ -> t
    | Application (f,args) ->
        Application (no_names f,
                     Array.map (fun t -> no_names t) args)
    | Lam (n,_,t) -> Lam (n, [||], no_names t)



  let map (f:int->int->term) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'f j nb' where 'nb' is the
       number of bound variables in the context where 'j' appears
     *)
    let rec mapr nb t =
      match t with
        Variable j -> f j nb
      | Application (a,b) ->
          Application (mapr nb a, Array.map (fun t -> mapr nb t) b)
      | Lam (nargs,names,t) ->
          Lam(nargs, names, mapr (nb+nargs) t)
    in
    mapr 0 t


  let down_from (n:int) (start:int) (t:term): term =
    (** Shift all free variables of [t] above [start] down by [n]. In case
        that free variables get captured raise 'Term_capture'
     *)
    map
      (fun j nb ->
        if j < nb+start then
          Variable j
        else if n <= j-nb-start then
          Variable (j-n)
        else
          raise Term_capture
      )
      t


  let down (n:int) (t:term): term =
    (* Shift all free variables of 't' down by 'n', require that there
       are no free variables 0,1,...,n-1
     *)
    down_from n 0 t
    (*map
      (fun j nb ->
        if j<nb then
          Variable j
        else if n <= j-nb then
          Variable (j-n)
        else
          raise Term_capture
      )
      t*)



  let upbound (n:int) (start:int) (t:term): term =
    (* Shift all free variables up by 'n' from 'start' on in the term 't' *)
    assert (n>=0);
    if n=0 then
      t
    else
      map
        (fun j nb ->
          if j<nb+start then Variable(j)
          else Variable(j+n))
        t




  let up (n:int) (t:term): term =
    (* Shift all free variables up by 'n' in the term 't' *)
    upbound n 0 t



  let sub_var (i:int) (t:term) (u:term): term =
    (* Substitute the free variabe 'i' in the term 't' by the term 'u' *)
    assert (0<=i);
    map
      (fun k nb ->
        if i+nb=k then
          up nb u
        else
          Variable k
      )
      t

  let part_sub (t:term) (nargs:int) (args:term array) (n_delta:int): term =
    (** Perform a partial substitution.

        The term [t] has [nargs] argument variables. The first
        [Array.length args] of them will be substituted by the corresponding
        term in [args] and the others will be shifted down appropriately so
        that the new term has [(Array.length args)-nargs] argument variables.

        The arguments come from an environment with [n_delta] variables more
        than the term [t]. Therefore the variables in [t] above [nargs] have
        to be shifted up by [n_delta] to transform them into the environment
        of the arguments.
     *)
    let len = Array.length args in
    assert (len <= nargs);
    map
      (fun j nb ->
        if j<nb then
          Variable(j)
        else
          let jfree = j-nb in
          if jfree < len then
            up (nb+nargs-len) args.(jfree)
          else if jfree < nargs then
            Variable (j-len)
          else
            Variable(j+n_delta-len)
      )
      t


  let sub (t:term) (args:term array) (nbound:int): term =
    (** substitute the free variables 0,1,args.len-1 in term [t] by the
        arguments [args] which are from an environment with [nbound] bound
        variables more than the variable of the term [t], i.e. all free
        variables above [len] are shifted up by [nbound-args.len]
     *)
    let len = Array.length args in
    part_sub t len args nbound




  let apply (t:term) (args: term array): term =
    (* Reduce (beta reduction) the term ([v0,v1,...]->t)(a0,a1,...) i.e.
       apply the function ([v0,v1,...]->t) to the arguments in args
     *)
    sub t args 0



  let abstract (t:term) (args: int array): term =
    (* Abstract the free variables in the 'args' array, i.e. make 'args.(0)'
       to 'Variable 0', 'args.(1)' to 'Variable(1)' ... and all other
       'Variable j' to 'Variable (j+len).
     *)
    let len = Array.length args
    and mp  = ref IntMap.empty
    in
    Array.iteri
      (fun i i0 -> mp := IntMap.add i0 i !mp)
      args;
    let res =
      map
        (fun j nb ->
          if j < nb then Variable j
          else
            try
              Variable (nb+(IntMap.find (j-nb) !mp))
            with Not_found ->
              Variable (j+len)
        )
        t
    in
    assert ((apply res (Array.map (fun i -> Variable i) args)) = t);
    res




  let rec reduce (t:term): term =
    (* Do all possible beta reductions in the term 't' *)
    let app (f:term) (args: term array): term =
      match f with
        Lam(nargs,_,t) ->
          assert (nargs=(Array.length args));
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
    | Lam(nargs,names,t) ->
        (* assert (0 < nargs); (* bug: why not? *) *)
        let tred = reduce t in
        if 0 < nargs then
          Lam (nargs, names, tred)
        else
          tred  (* ??? *)


  let lambda_split (t:term): int * int array * term =
    match t with
      Lam (n,names,t) -> n,names,t
    | _ -> raise Not_found


  let unary (unid:int) (t:term): term =
    let args = [| t |] in
    Application (Variable unid, args)


  let unary_split (t:term) (unid:int): term =
    match t with
      Application (f,args) when (Array.length args) = 1 ->
        (match f with
          Variable i when i=unid -> args.(0)
        | _ -> raise Not_found)
    | _ -> raise Not_found


  let binary (binid:int) (left:term) (right:term): term =
    let args = [| right; left |] in
    Application (Variable binid, args)


  let binary_split (t:term) (binid:int): term * term =
    match t with
      Application (f,args) when (Array.length args) = 2 ->
        (match f with
          Variable i when i=binid ->
            (args.(0), args.(1))
        | _ -> raise Not_found)
    | _ -> raise Not_found



  let rec binary_right (t:term) (binid:int): term list =
    let rec binr (t:term) (lst:term list): term list =
      match t with
        Application (f,args) when Array.length args = 2 ->
          begin
            match f with
              Variable i when i = binid ->
                binr args.(0) (args.(1) :: lst)
            | _ -> t::lst
          end
      | _ -> t::lst
    in
    binr t []




  let implication_chain2 (t:term) (impid:int)
      : term list * term =
    (** Extract the implication chain of the term [t], i.e. if
        [t] has the form

            a => b => ... => e => z

        it returns

            [e,...,b,a] , z

        Note:
        a) The premises are returned in reverse order.
        b) If [t] is not an implication, then the list of premises is
           empty and [t] is returned as the consequence
     *)
    let rec chrec (t:term) (ps_rev:term list): term list * term =
      try
        let a,b = binary_split t impid in
        chrec b (a::ps_rev)
      with Not_found ->
        ps_rev, t
    in
    chrec t []




  let implication_chain (t:term) (impid:int)
      : (term list * term) list =
    (* Extract the implication chain of the term 't' i.e. we have

       t = (a=>b=>...=>z)

       result:
       [([],a=>b=>...=>z), ([a],b=>...=>z), ... , ([a,...,y],z)]

       In the case that 't' is not an implication then the returned list
       consists only of the first element.
     *)
    let rec chainr (t:term)
        : (term list * term) list =
      try
        let a,b = binary_split t impid in
        ([],t) :: (List.map
                     (fun (ps,tgt) -> a::ps,tgt)
                     (chainr b))
      with Not_found ->
        [([],t)]
    in
    chainr t
end (* Term *)






module Term_sub_arr: sig

  type t
  val make: int -> t
  val count: t -> int
  val get:   int -> t -> term
  val flags: t -> bool array
  val args:  t -> term array
  val add:   int -> term -> t -> unit
  val extend:int -> t -> t
  val extend_bottom: int -> t -> t
  val remove_bottom: int -> t -> t
  val unify: term -> term -> t -> unit

end = struct

  type t = {n:int; args: term array; flags: bool array}

  let flags (s:t): bool array = s.flags
  let args  (s:t): term array = s.args

  let make (n:int): t =
    {n     = n;
     args  = Array.init n (fun i -> Variable i);
     flags = Array.make n false}

  let count (s:t): int = s.n

  let get (i:int) (s:t): term =
    assert (i < (count s));
    s.args.(i)

  let add (i:int) (t:term) (s:t): unit =
    (** Add the substitution [i ~~> t] to the substitution [s] i.e.
        apply to [t] all already available substitutions and check for
        circularity and apply [i ~~> t] to all available substitutions.
     *)
    assert (i <= s.n);
    assert (not (Term.is_variable t i));
    let t = Term.sub t s.args s.n in
    if IntSet.mem i (Term.bound_variables t s.n) then
      raise Not_found (* circular substitution *)
    else begin
      Array.iteri
        (fun j e ->
          if s.flags.(j) then s.args.(j) <- Term.sub_var i e t
          else ())
        s.args;
      if not s.flags.(i) then
        (s.args.(i)<-t; s.flags.(i)<-true)
      else if t = s.args.(i) then
        ()
      else
        raise Not_found
    end

  let extend (n:int) (s:t): t =
    (** Introduce [n] new variables at the top, i.e. all
          terms are just copied into the new larger substitution.
     *)
    let snew = make (n+s.n) in
    Array.blit s.args  0  snew.args  0  s.n;
    Array.blit s.flags 0  snew.flags 0  s.n;
    snew


  let extend_bottom (n:int) (s:t): t =
    (** Introduce [n] new variables at the bottom, i.e. shift all
          terms up by [n].
     *)
    let snew = make (n+s.n) in
    Array.iteri (fun i t -> snew.args.(i+n) <- Term.up n t) s.args;
    Array.blit s.flags 0 snew.flags n  s.n;
    snew



  let remove_bottom (n:int) (s:t): t =
    (** Remove [n] variables from the bottom, i.e. shift all
          terms down by [n].
     *)
    assert (n <= (count s));
    let snew = make (s.n-n) in
    Array.iteri
      (fun i _ -> snew.args.(i) <- Term.down n s.args.(i+n)) snew.args;
    Array.blit s.flags n   snew.flags 0   (s.n-n);
    snew


  let unify (t1:term) (t2:term) (subst:t): unit =
    (** Unify the terms [t1] and [t2] using the substitution [subst], i.e.
        apply first the substitution [subst] to both terms and then
        add substitutions to [subst] so that when applied to both terms makes
        them identical.
     *)
    let nvars = count subst
    in
    let do_sub (i:int) (t:term) (nb:int): unit =
      assert (nb<=i); assert (i<nb+nvars);
      match t with
        Variable j when nb<=j && j<nb+nvars ->
          if i=j then ()
          else
            let lo,hi = if i<=j then i,j else j,i in
            add (lo-nb) (Variable (hi-nb)) subst
              (*Variable j when i=j ->
                ()*)
      | _ ->
          let i,t =
            try i-nb, Term.down nb t
            with Term_capture -> raise Not_found
          in
          add i t subst
    in
    let rec uni (t1:term) (t2:term) (nb:int): unit =
      match t1,t2 with
        Variable i, _ when nb<=i && i<nb+nvars ->
          do_sub i t2 nb
        | _, Variable j when nb<=j && j<nb+nvars ->
            do_sub j t1 nb
        | Variable i, Variable j ->
            assert (i<nb||nb+nvars<=i);
            assert (j<nb||nb+nvars<=j);
            if i=j then
              ()
            else
              raise Not_found
        | Application(f1,args1), Application(f2,args2) ->
            if (Array.length args1) <> (Array.length args2) then
              raise Not_found;
            uni f1 f2 nb;
            Array.iteri (fun i t1 ->  uni t1 args2.(i) nb) args1
        | Lam (nb1,_,t1), Lam (nb2,_,t2) ->
            if nb1=nb2 then
              uni t1 t2 (nb+nb1)
            else
              raise Not_found
        | _ -> raise Not_found
    in
    uni t1 t2 0;
    assert ((Term.sub t1 (args subst) nvars)
              = (Term.sub t2 (args subst) nvars))
  end (* Term_sub_arr *)











module Term_sub: sig
  type t
  val to_string:      t -> string
  val count:          t -> int
  val is_injective:   t -> bool
  val empty:          t
  val singleton:      int -> term -> t
  val find:           int -> t -> term
  val mem:            int -> t -> bool
  val add:            int -> term ->  t -> t
  val merge:          t -> t -> t
  val arguments:      int -> t -> term array
  val domain:         t -> IntSet.t
  val apply_0:        term -> int -> t -> bool -> term
  val apply_covering: term -> int -> t -> term
  val apply:          term -> int -> t -> term * int
end = struct

  type t = term IntMap.t

  let to_string (sub:t): string =
    let lst = IntMap.fold
        (fun i t lst -> ((string_of_int i)^"->"^(Term.to_string t))::lst
        )
        sub
        []
    in
    "{" ^ (String.concat "," (List.rev lst)) ^ "}"

  let count (sub:t): int =
    IntMap.fold
      (fun i _ sum -> sum+1)
      sub
      0

  let for_all (f: int -> term -> bool) (sub:t): bool =
    IntMap.fold (fun i t res -> res && f i t) sub true


  let inverse (sub:t): t =
    IntMap.fold
      (fun i t inv ->
        match t with
          Variable j when not (IntMap.mem j inv) ->
            IntMap.add j (Variable i) inv
        | _ -> raise Not_found
      )
      sub
      IntMap.empty

  let is_injective (sub:t): bool =
    try
      let _ = inverse sub in
      true
    with Not_found ->
      false



  let empty = IntMap.empty

  let singleton (i:int) (t:term): t =
    IntMap.add i t IntMap.empty

  let find (i:int) (sub:t): term =
    IntMap.find i sub

  let mem (i:int) (sub:t): bool =
    IntMap.mem i sub

  let add (i:int) (t:term) (sub:t): t =
    assert (not (mem i sub));
    IntMap.add i t sub

  let merge (sub1:t) (sub2:t): t =
    let res = ref sub2 in
    IntMap.iter
      (fun i t1 ->
        let t2_opt =
          try Some (IntMap.find i sub2)
          with Not_found -> None
        in
        match t2_opt with
          None ->
              res := IntMap.add i t1 !res
        | Some t2 ->
            if t1=t2 then ()
            else ((*Printf.printf "    Cannot merge sub\n";*) raise Not_found)
      )
      sub1;
    !res

  let arguments (nargs:int) (sub:t): term array =
    let args = Array.make nargs (Variable 0) in
    IntMap.iter
      (fun i t ->
        assert (i<nargs);
        args.(i) <- t)
      sub;
    args


  let domain (sub:t): IntSet.t =
    IntMap.fold
      (fun i _ set -> IntSet.add i set)
      sub
      IntSet.empty


  let up (n:int) (sub:t): t =
    IntMap.map (fun t -> Term.up n t) sub

  let is_covering (t:term) (nargs:int) (sub:t): bool =
    (* Does the substitution 'sub' cover all argument variables in the
       term 't'  which has 'nargs' formal arguments?
     *)
    let openvars
        = IntSet.diff (Term.bound_variables t nargs) (domain sub)
    in
    IntSet.is_empty openvars



  let apply_0 (t:term) (nargs:int) (sub:t) (covers:bool): term =
    (* Apply to the term 't' with 'nargs' formal arguments the substitution
       'sub'. If the substitution covers all formal arguments of 't' then
       all free variables (i.e. variables above 'nargs') are shifted down
       by nargs.

       Note that all substitution terms have to be shifted up by 'nargs'
       if the substitution is not covering.
     *)
    let nargs_res, sub =
      if covers then
        0, sub
      else
        nargs, up nargs sub
    in
    let args  = Array.init nargs (fun i -> Variable i)
    in
    IntMap.iter
      (fun i t ->
        assert (i<nargs);
        args.(i) <- t
      )
      sub;
    Term.sub t args nargs_res



  let apply_covering (t:term) (nargs:int) (sub:t): term =
    (* Apply to the term 't' with 'nargs' formal arguments the substitution
       'sub' assuming that the substitution covers all formal arguments
       contained in 't'
     *)
    assert ((domain sub) = (Term.bound_variables t nargs));
    apply_0 t nargs sub true




  let apply (t:term) (nargs:int) (sub:t): term * int =
    (* Apply to the term 't' with 'nargs' formal arguments the substitution
       'sub'. If the substitution covers all formal arguments of 't' then
       all free variables (i.e. variables above 'nargs') are shifted down
       by nargs and 0 is returned with the result term.

       Note that all substitution terms have to be shifted up by 'nargs'
       if the substitution is not covering.
     *)
    let covers = is_covering t nargs sub in
    let nargs_res = if covers then 0 else nargs
    in
    apply_0 t nargs sub covers, nargs_res


end


type substitution = Term_sub.t
