open Term
open Container


let unify (t1:term) (t2:term) (nargs:int): Term_sub.t =
  (* Unify the term [t1] with the term [t2] i.e. find a substitution for the
     [nargs] arguments which applied to [t1] makes it equal to t2
   *)
  let rec uni t1 t2 nb sub =
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
    | Application (f1,args1,pr1), Application (f2,args2,pr2)
      when Array.length args1 = Array.length args2  && pr1 = pr2 ->
        let sub = ref (uni f1 f2 nb sub) in
        for i = 0 to Array.length args1 - 1 do
          sub := uni args1.(i) args2.(i) nb !sub
        done;
        !sub
    | Lam(n1,nms1,t1,pr1), Lam(n2,nms2,t2,pr2) when n1 = n2 && pr1 = pr2 ->
        uni t1 t2 (n1+nb) sub
    | _ ->
        raise Not_found
  in
  let sub = uni t1 t2 0 Term_sub.empty in
  assert (let args = Term_sub.arguments nargs sub in
  Term.sub t1 args nargs = t2);
  sub


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
  (* Compare the terms and return a lambda term and two argument arrays so that
     the lambda term applied to the fist argument array results in the first term
     and the lambda term applied to the second argument array results in the second
     term. *)

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
    | Application(f1,args1,pr1), Application(f2,args2,pr2)
      when Array.length args1 = Array.length args2 && pr1 = pr2 ->
        begin try
          let pos,poslst,elst,tlst = comp f1 f2 nb (pos+1) poslst elst tlst in
          let args = Myarray.combine args1 args2 in
          Array.fold_left
            (fun (pos,poslst,elst,tlst) (a1,a2) ->
              comp a1 a2 nb pos poslst elst tlst)
            (pos,poslst,elst,tlst)
            args
        with Not_found ->
          different t1 t2 pos poslst elst tlst
        end
    | Lam(n1,nms1,t01,pr1), Lam(n2,nms2,t02,pr2)
      when n1 = n2 && pr1 = pr2 ->
        begin try
          comp t01 t02 (n1+nb) (pos+1) poslst elst tlst
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
    match t with
      Variable k when k < nb ->
        assert (nextpos <> hd);
        nextpos+1, nextvar, poslst, t
    | Variable k ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else nextpos+1, nextvar, poslst, Variable (k+nargs)
    | Application (f,args,pr) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nextpos,nextvar,poslst,f =
            mklambda (nextpos+1) nextvar poslst f nb in
          let nextpos,nextvar,poslst,arglst =
            Array.fold_left
              (fun (nextpos,nextvar,poslst,arglst) arg ->
                let nextpos,nextvar,poslst,arg =
                  mklambda nextpos nextvar poslst arg nb in
                nextpos, nextvar, poslst, arg::arglst)
              (nextpos,nextvar,poslst,[])
              args in
          let args = Array.of_list (List.rev arglst) in
          nextpos, nextvar, poslst, Application(f,args,pr)
    | Lam(n,nms,t0,pr) ->
        if nextpos = hd then (nextpos+1), (nextvar+1), tl, Variable (nextvar+nb)
        else
          let nextpos,nextvar,poslst,t0 =
            mklambda (nextpos+1) nextvar poslst t0 (n+nb) in
          nextpos, nextvar, poslst, Lam(n,nms,t0,pr)
  in
  let nextpos, nextvar, poslst, tlam = mklambda 0 0 poslst t1 0 in
  if nextpos = 1 then raise Not_found;
  let lam = Lam (nargs,[||],tlam,false) in
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
      Printf.printf " lam   %s\n" (Term.to_string lam);
      Printf.printf " args1 %s\n" (argsstr args1);
      Printf.printf " args2 %s\n" (argsstr args2);
      Printf.printf " tappl %s\n" (Term.to_string t1);
      Printf.printf " torig  %s\n" (Term.to_string t2);
      false
    end
  in
  assert (equi (Term.apply tlam args1) t1);
  assert (equi (Term.apply tlam args2) t2);
  lam, earr, args1, args2
