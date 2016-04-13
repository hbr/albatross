open Term
open Container

let extract_pattern (n:int) (t:term): (int*int*int*term) list =
  (* Extract a pattern of each variable in the term [t]. The result is a list of
     triples [i,j,n,p] where
         i: original variable
         j: variable in the pattern
         n: number of variables in the pattern
         p: pattern
   *)
  assert false
  (*let rec extract (var:int) (pos:int) (npat:int) (pat:term) (t:term) (nb:int) =
    let bvs = Term.bound_variables t (n+nb) in
    if not (IntSet.mem (var+nb) bvs) then
      var, pos, (pos+1), Variable (0+nb)
    else
      let extract_args pos npat pat args =
        Array.fold_left
          (fun (var,pos,npat,p) arg ->
            extract var pos npat pat arg nb)
          (var,pos,npat,pat)
          args in
      match t with
        Variable i ->
          assert (var = i + nb);
          var, pos, npat, Variable (pos+nb)
      | VAppl(i,args) ->
          assert (var <> i + nb);
          extract_args pos npat pat args
      | Application(f,args,pr) ->
          assert false (* nyi *)
      | Lam(n,nms,ps,t0,pr) ->
          assert false (* nyi *)
      | QExp(n,nms,t0,is_all) ->
          assert false (* nyi *)
      | Flow(ctrl,args) ->
          assert false (* nyi *)
      | Indset(n,nms,rs) ->
          assert false (* nyi *)
  in
  let vars = Term.bound_variables t n in
  IntSet.fold
    (fun i lst ->
      (extract i 0 1 (Variable 0) t 0) :: lst)
    vars []
*)






let unify_pattern
    (n1:int) (p1:term) (n2:int) (p2:term): term array =
  (* Find a unification of the pattern [p1] with [n1] variables and [p2] with [n2]
     variables. Both terms above their variables are from the same environment.

     The result (if unification is possible) is an array of size [n1+n2] which
     contains substitutions for all variables of the two pattern. The substitution
     applied to both pattern (with sufficiently space made for the variables of the
     other pattern) results in the same term.

     If unification is not possible then [Not_found] is raised
   *)
  let n = n1 + n2 in
  let subargs = Array.init n (fun i -> Variable i)
  and subflgs = Array.make n false
  and pat1 = Term.up_from n2 n1 p1
  and pat2 = Term.up n1 p2
  in
  let do_sub i t =
    assert (i < n);
    if subflgs.(i) && t <> subargs.(i) then
      raise Not_found
    else begin
      subflgs.(i) <- true;
      subargs.(i) <- t
    end in
  let rec uni t1 t2 =
    let uni_args args1 args2 =
      assert (Array.length args1 = Array.length args2);
      Array.iteri
        (fun i arg ->
          uni arg args2.(i))
        args1
    in
    match t1, t2 with
      Variable i, Variable j when i < n && j < n ->
        do_sub i t1;
        do_sub j t1
    | Variable i, _ when i < n ->
        assert (i < n1);
        do_sub i t2
    | _ , Variable j when j < n ->
        do_sub j t1
    | Variable i1, Variable i2 when i1 = i2 ->
        ()
    | VAppl(i1,args1,_), VAppl(i2,args2,_) when i1 = i2 ->
        uni_args args1 args2
    | Application(f1,args1,pr1), Application(f2,args2,pr2)
      when pr1 = pr2 && Array.length args1 = Array.length args2 ->
        assert false (* nyi: *)
    | Lam(n1,nms1,ps1,t01,pr1,_), Lam(n2,nms2,ps2,t02,pr2,_)
      when pr1 = pr2 ->
        assert false (* nyi: *)
    | QExp(n1,_,_,t01,all1), QExp(n2,_,_,t02,all2)
      when n1 = n2 && all1 = all2 ->
        assert false (* nyi: *)
    | Flow(ctrl1,args1), Flow(ctrl2,args2)
      when ctrl1 = ctrl2 && Array.length args1 = Array.length args2 ->
        assert false (* nyi: *)
    | _ ->
        raise Not_found
  in
  uni pat1 pat2;
  assert begin
    let ok = Term.subst pat1 n subargs = Term.subst pat2 n subargs in
    if not ok then begin
      Printf.printf "unify_pattern\n";
      Printf.printf "   n1 %d, p1 %s\n" n1 (Term.to_string p1);
      Printf.printf "   n2 %d, p2 %s\n" n2 (Term.to_string p2);
      Printf.printf "   pat1 %s\n" (Term.to_string pat1);
      Printf.printf "   pat2 %s\n" (Term.to_string pat2);
      Array.iteri (fun i t ->
        Printf.printf "   %d %s\n" i (Term.to_string t))
        subargs
    end;
    ok
  end;
  subargs



let unify (t1:term) (npat:int) (pat:term): term array =
  let args = unify_pattern 0 t1 npat pat in
  Array.map
    (fun t ->
      try Term.down npat t
      with Term_capture -> assert false (* cannot happen *))
    args


let can_unify_pattern (t:term) (npat:int) (pat:term): bool =
  try let _ = unify t npat pat in true
  with Not_found -> false




let unify0 (t1:term) (nargs:int) (t2:term): Term_sub.t =
  (* Unify the term [t1] with the term [t2] i.e. find a substitution for the
     [nargs] arguments of [t1] which applied to [t1] makes it equal to t2
   *)
  assert (IntSet.cardinal (Term.bound_variables t1 nargs) = nargs);
  let rec uni t1 t2 nb sub =
    let uni_args args1 args2 sub =
      assert (Array.length args1 = Array.length args2);
      let _,sub =
        Array.fold_left
          (fun (i,sub) a1 ->
            i+1,
            uni a1 args2.(i) nb sub)
          (0,sub)
          args1 in
      sub
    and uni_list lst1 lst2 sub =
      assert (List.length lst1 = List.length lst2);
      let _,sub =
        List.fold_left2
          (fun (i,sub) a1 a2 ->
            i+1,
            uni a1 a2 nb sub)
          (0,sub)
          lst1 lst2 in
      sub
    in
    match t1, t2 with
      Variable i, _ when i < nb || nb+nargs <= i ->
        if t1 = t2 then sub else raise Not_found
    | Variable i, _ ->
        assert (nb <= i);
        assert (i < nb+nargs);
        let t2 =
          try Term.down nb t2
          with Term_capture -> raise Not_found in
        let t_opt =
          try let t = Term_sub.find (i-nb) sub in Some t
          with Not_found -> None in
        begin match t_opt with
          None -> Term_sub.add (i-nb) t2 sub
        | Some t when t <> t2 -> raise Not_found
        | Some t -> assert (t=t2); sub
        end
    | VAppl (i1,args1,_), VAppl (i2,args2,_) when i1 = i2 ->
        uni_args args1 args2 sub
    | Application (f1,args1,pr1), Application (f2,args2,pr2)
      when Array.length args1 = Array.length args2  && pr1 = pr2 ->
        let sub = uni f1 f2 nb sub in
        uni_args args1 args2 sub
    | Lam(n1,_,ps1,t1,pr1,_), Lam(n2,_,ps2,t2,pr2,_)
      when n1 = n2 && pr1 = pr2 && List.length ps1 = List.length ps2 ->
        let sub = uni_list ps1 ps2 sub in
        uni t1 t2 (1 + nb) sub
    | QExp(n1,_,_,t01,is_all1), QExp(n2,_,_,t02,is_all2)
      when n1 = n2 && is_all1 = is_all2 ->
        uni t01 t02 (n1+nb) sub
    | Flow(ctrl1,args1), Flow(ctrl2,args2)
      when ctrl1 = ctrl2 && Array.length args1 = Array.length args2 ->
        uni_args args1 args2 sub
    | _ ->
        raise Not_found
  in
  let sub = uni t1 t2 0 Term_sub.empty in
  assert begin
    let args = Term_sub.arguments nargs sub in
    let t1sub = Term.subst t1 nargs args in
    Term.equivalent t1sub t2
  end;
  sub


let can_unify (t1:term) (nargs:int) (t2:term): bool =
  (* Can the term [t1] with [nargs] arguments be unified with the term [t2]? *)
  try
    ignore(unify0 t1 nargs t2);  true
  with Not_found ->
    false


(* Comparison of two terms and finding their differences

   We make a preorder traversal of the common part. Each node in this traversal
   has a unique position.

   Two nodes are structurally different if

   - they have different constructors
   - they are both unbound but different variables
   - one of them is a bound variable and the other is not the same bound variable
   - they are both applications with different number of arguments or different
     predicate flag
   - they are both lambda expression with different number of bound variables or
     different predicate flag

   If they are structurally different and contain no bound variables they are put
   outside the context and pushed to the pair list, the position is pushed onto the
   position list and the nextvar variable is incremented by one.

   If they have the same structure then some difference might appear in subterms.
 *)




let compare (t1:term) (t2:term) (eq:term->term->'a)
    : term * 'a array * term array * term array =
  (* Compare the terms and return an inner lambda term and two argument arrays so
     that the lambda term applied to the fist argument array results in the first
     term and the lambda term applied to the second argument array results in the
     second term. *)
  (* return n positions checked,
     positions with different subterms,
     pair list of different subterms *)
  let rec comp (t1:term) (t2:term) (nb:int)
      (pos:int) (poslst:int list) (elst:'a list) (tlst:(term*term) list)
      : int * int list * 'a list * (term*term) list =
    let different t1 t2 pos poslst elst tlst =
      try
        let t1 = Term.down nb t1
        and t2 = Term.down nb t2 in
        let e = eq t1 t2 in
        pos+1, pos::poslst, e::elst, (t1,t2)::tlst
      with Term_capture ->
        raise Not_found
    and comp_args pos poslst elst tlst args1 args2 =
      let args = Myarray.combine args1 args2 in
      Array.fold_left
        (fun (pos,poslst,elst,tlst) (a1,a2) ->
          comp a1 a2 nb pos poslst elst tlst)
        (pos,poslst,elst,tlst)
        args
    in
    match t1, t2 with
      Variable k, _ when k < nb ->
        if t1 = t2 then pos+1, poslst, elst, tlst
        else raise Not_found
    | _ , Variable k when k < nb ->
        if t1 = t2 then pos+1, poslst, elst, tlst
        else raise Not_found
    | Variable k, Variable l when k = l ->
        pos+1, poslst, elst, tlst
    | VAppl(i1,args1,_), VAppl(i2,args2,_)
      when i1 = i2 && Array.length args1 = Array.length args2 ->
        begin try
          let pos  = pos + 1 in
          comp_args pos poslst elst tlst args1 args2
        with Not_found ->
          different t1 t2 pos poslst elst tlst
        end
    | Application(f1,args1,pr1), Application(f2,args2,pr2)
      when Array.length args1 = Array.length args2 && pr1 = pr2 ->
        begin try
          let pos,poslst,elst,tlst = comp f1 f2 nb (1+pos) poslst elst tlst in
          comp_args pos poslst elst tlst args1 args2
        with Not_found ->
          different t1 t2 pos poslst elst tlst
        end
    | Lam(n1,nms1,ps1,t01,pr1,_), Lam(n2,nms2,ps2,t02,pr2,_)
      when n1 = n2 && pr1 = pr2 && List.length ps1 = List.length ps2 ->
        let nb = 1 + nb in
        begin try
          let pos,poslst,elst,tlst =
            List.fold_left2
              (fun (pos,poslst,elst,tlst) p1 p2 ->
                comp p1 p2 nb pos poslst elst tlst)
              (1+pos,poslst,elst,tlst)
              ps1 ps2 in
          comp t01 t02 nb pos poslst elst tlst
        with Not_found ->
          different t1 t2 pos poslst elst tlst
        end
    | QExp(n1,_,_,t01,is_all1), QExp(n2,_,_,t02,is_all2)
      when n1 = n2 && is_all1 = is_all2 ->
        begin try
          comp t01 t02 (n1+nb) (1+pos) poslst elst tlst
        with Not_found ->
          different t1 t2 pos poslst elst tlst
        end
    | Flow(ctrl1,args1), Flow(ctrl2,args2)
      when ctrl1=ctrl2 && Array.length args1 = Array.length args2 ->
        begin try
          let pos  = pos + 1 in
          comp_args pos poslst elst tlst args1 args2
        with Not_found ->
          different t1 t2 pos poslst elst tlst
        end
    | _, _ ->
        different t1 t2 pos poslst elst tlst
  in
  let npos, poslst, elst, tlst = comp t1 t2 0 0 [] [] [] in
  let nargs = List.length poslst
  and poslst  = List.rev poslst in
  if nargs = 0 then raise Not_found;
  (* return nextpos, nextvar, poslst, lambda term *)
  let rec mklambda (nextpos:int) (nextvar:int) (poslst:int list) (t:term) (nb:int)
      : int * int * int list * term =
    assert (nextpos < npos);
    let hd,tl =
      match poslst with
        [] -> -1,[]
      | hd::tl -> hd,tl
    in
    let mk_args nextpos nextvar poslst args =
      let nextpos,nextvar,poslst,arglst =
        Array.fold_left
          (fun (nextpos,nextvar,poslst,arglst) arg ->
            let nextpos,nextvar,poslst,arg =
              mklambda nextpos nextvar poslst arg nb in
            nextpos, nextvar, poslst, arg::arglst)
          (nextpos,nextvar,poslst,[])
          args in
      nextpos,nextvar,poslst, Array.of_list (List.rev arglst)
    in
    match t with
      Variable k when k < nb ->
        assert (nextpos <> hd);
        nextpos+1, nextvar, poslst, t
    | Variable k ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else nextpos+1, nextvar, poslst, Variable (k+nargs)
    | VAppl (i,args,ags) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nextpos = nextpos + 1 in
          let nextpos,nextvar,poslst,args =
            mk_args nextpos nextvar poslst args in
          nextpos, nextvar, poslst, VAppl(i+nargs,args,ags)
    | Application (f,args,pr) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nextpos,nextvar,poslst,f =
            mklambda (nextpos+1) nextvar poslst f nb in
          let nextpos,nextvar,poslst,args =
            mk_args nextpos nextvar poslst args in
          nextpos, nextvar, poslst, Application(f,args,pr)
    | Lam(n,nms,pres,t0,pr,tp) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nb = 1 + nb in
          let nextpos,nextvar,poslst,pres_rev =
            List.fold_left
              (fun (nextpos,nextvar,poslst,ps) p ->
                let nextpos,nextvar,poslst,p =
                  mklambda nextpos nextvar poslst p nb in
                nextpos, nextvar, poslst, p::ps)
              (1+nextpos,nextvar,poslst,[])
              pres in
          let pres = List.rev pres_rev in
          let nextpos,nextvar,poslst,t0 =
            mklambda nextpos nextvar poslst t0 nb in
          nextpos, nextvar, poslst, Lam(n,nms,pres,t0,pr,tp)
    | QExp(n,tps,fgs,t0,is_all) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nextpos,nextvar,poslst,t0 =
            mklambda (nextpos+1) nextvar poslst t0 (n+nb) in
          nextpos, nextvar, poslst, QExp(n,tps,fgs,t0,is_all)
    | Flow (ctrl,args) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nextpos = nextpos + 1 in
          let nextpos,nextvar,poslst,args =
            mk_args nextpos nextvar poslst args in
          nextpos, nextvar, poslst, Flow(ctrl,args)
    | Indset (nme,tp,rs) ->
        assert false (* nyi *)
  in
  let nextpos, nextvar, poslst, tlam = mklambda 0 0 poslst t1 0 in
  if nextpos = 1 then raise Not_found;
  assert (nextvar = nargs);
  assert (poslst = []);
  let tarr = Array.of_list (List.rev tlst)
  and earr = Array.of_list (List.rev elst) in
  let args1, args2 = Myarray.split tarr in
  let equi t1 t2 =
    if Term.equivalent t1 t2 then true
    else begin
      let argsstr args = "[" ^
        (String.concat "," (List.map Term.to_string (Array.to_list args))) ^ "]"
      in
      Printf.printf " tlam  %s\n" (Term.to_string tlam);
      Printf.printf " args1 %s\n" (argsstr args1);
      Printf.printf " args2 %s\n" (argsstr args2);
      Printf.printf " tappl %s\n" (Term.to_string t1);
      Printf.printf " torig  %s\n" (Term.to_string t2);
      false
    end
  in
  assert (equi (Term.apply tlam args1) t1);
  assert (equi (Term.apply tlam args2) t2);
  tlam, earr, args1, args2
