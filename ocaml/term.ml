(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Container


type term =
    Variable    of int
  | Application of term * term array * bool      (* fterm, args, is_pred *)
  | Lam         of int * int array * term * bool (* n, names, t, is_pred *)
  | QExp        of int * int array * term * bool (* n, names, t, is_all *)
and formal  = int * term (* name, type *)
and formals = formal array

type type_term = term

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

  val is_variable_i: term -> int -> bool

  val to_string: term -> string

  val variable:    term -> int
  val is_variable: term -> bool
  val is_argument: term -> int -> bool

  val nodes: term -> int

  val depth: term -> int

  val fold_with_level: ('a -> int -> int -> 'a) -> 'a -> term -> 'a
  val fold: ('a -> int -> 'a) -> 'a -> term -> 'a
  val fold_arguments: ('a -> int -> 'a) -> 'a -> term -> int -> 'a

  val least_free: term -> int

  val greatestp1_arg: term -> int -> int

  val split_variables: term -> int -> IntSet.t * IntSet.t

  val variables_filtered: term -> (int->bool) -> IntSet.t

  val free_variables: term -> int -> IntSet.t

  val bound_variables: term -> int -> IntSet.t

  val range_variables: term -> int -> int -> IntSet.t

  val used_variables:       term -> int -> int list
  val used_variables_from:  term -> int -> int list

  val equivalent: term -> term -> bool

  val map: (int->int->term) -> term -> term

  val map_free: (int->term) -> term -> int -> term

  val down_from: int -> int -> term -> term

  val down: int -> term -> term

  val upbound: int->int->term->term

  val up: int->term->term

  val array_up: int -> term array -> term array

  val sub_var: int -> term -> term -> term

  val part_sub_from: term -> int -> int -> term array -> int -> term

  val part_sub: term -> int -> term array -> int -> term

  val sub_from: term -> int -> term array -> int -> term

  val sub:   term -> term array -> int -> term

  val apply: term -> term array -> term

  val abstract: term -> int array -> term

  val reduce: term -> term

  val reduce_top: term -> term

  val lambda_split: term -> int * int array * term

  val qlambda_split: term -> int * int array * term * bool

  val unary: int -> term -> term

  val unary_split: term -> int -> term

  val quantified: bool -> int -> int array -> term -> term

  val all_quantified:  int -> int array -> term -> term

  val some_quantified:  int -> int array -> term -> term

  val quantifier_split: term -> bool -> int * int array * term

  val all_quantifier_split: term-> int * int array * term

  val some_quantifier_split: term -> int * int array * term

  val binary: int -> term -> term -> term

  val binary_split_0: term -> int * term * term

  val binary_split: term -> int -> term * term

  val binary_right: term -> int -> term list

  val split_implication_chain: term -> int -> term list * term
  val make_implication_chain:  term list -> term -> int -> term

  val implication_chain: term -> int -> (term list * term) list

  val is_normalized: term -> int -> int -> bool
  val used_args: term -> int -> int array
  val normalizing_args: term -> int -> term array * int
  val normalize: term -> int -> int array -> term * int array * int
  val keep_used: int array -> term -> int -> term

end = struct

  let is_variable_i (t:term) (i:int): bool =
    match t with
      Variable j when i=j -> true
    | _                   -> false


  let rec to_string (t:term): string =
    let argsstr nargs names =
      let nnames = Array.length names in
      assert (nnames=0 || nnames=nargs);
      let args = Array.init nargs string_of_int in
      String.concat "," (Array.to_list args)
    in
    let strlam nargs names t pred =
      let argsstr = argsstr nargs names in
      if pred then
        "{" ^ argsstr ^ ": " ^ (to_string t) ^ "}"
      else
        "((" ^ argsstr ^ ")->" ^ (to_string t) ^ ")"
    in
    match t with
      Variable i -> string_of_int i
    | Application (f,args,pr) ->
        let fstr = to_string f
        and argsstr = Array.to_list (Array.map to_string args)
        and predstr = if pr then "p" else ""
        in
        fstr ^ predstr ^ "(" ^
        (String.concat "," argsstr)
        ^ ")"
    | Lam(nargs,names,t,pred) ->
        strlam nargs names t pred
    | QExp (nargs,names,t,is_all) ->
        let argsstr = argsstr nargs names in
        let qstr    = if is_all then "all" else "some" in
        qstr ^ "(" ^ argsstr ^ ")" ^ (to_string t)


  let variable (t:term): int =
    match t with
      Variable i -> i
    | _ -> raise Not_found


  let is_variable (t:term): bool =
    try
      let _ = variable t in
      true
    with Not_found ->
      false


  let is_argument (t:term) (nargs:int): bool =
    try
      let i = variable t in i < nargs
    with Not_found -> false



  let rec nodes (t:term): int =
    (* The number of nodes in the term t *)
    match t with
      Variable _ -> 1
    | Application (f,args,_) ->
        (Array.fold_left (fun sum t -> sum + (nodes t)) (nodes f) args)
    | Lam (_,_,t,_) | QExp (_,_,t,_) ->
        1 + (nodes t)


  let rec depth (t:term): int =
    (* The depth of the term t *)
    match t with
      Variable _ -> 0
    | Application (f,args,_) ->
        Mylist.sum depth (1 + (depth f)) (Array.to_list args)
    | Lam (_,_,t,_) | QExp (_,_,t,_)->
        1 + (depth t)



  let fold_with_level (f:'a->int->int->'a) (a:'a) (t:term): 'a =
    (** Fold the free variables with their level (from the top) in the order
        in which they appear in the term [t] with the function [f] and
        accumulate the results in [a].
     *)
    let rec fld (a:'a) (t:term) (level) (nb:int): 'a =
      match t with
        Variable i ->
          if nb <= i then f a (i-nb) level else a
      | Application (f,args,_) ->
          let a = fld a f (level+1) nb in
          Array.fold_left (fun a t -> fld a t (level+1) nb) a args
      | Lam (n,_,t,_) ->
          fld a t (level+1) (nb+n)
      | QExp (n,_,t,_) ->
          fld a t (level+1) (nb+n)
    in
    fld a t 0 0



  let fold (f:'a->int->'a) (a:'a) (t:term): 'a =
    (** Fold the free variables in the order in which they appear in the
        term [t] with the function [f] and accumulate the results in [a].
     *)
    let f0 a i level = f a i in
    fold_with_level f0 a t



  let fold_arguments (f:'a->int->'a) (a:'a) (t:term) (nargs:int): 'a =
    (** Fold the arguments in the order in which they appear in the term
        [t] with [nargs] arguments with the function [f] and accumulate
        the results in [a].
     *)
    let fargs a i =
      if i < nargs then f a i else a
    in
    fold fargs a t


  let least_free (t:term): int =
    (** The least free variable of the term [t] or [-1] if the term does not
        have free variables.
     *)
    fold
      (fun least i ->
        if least = (-1) || i < least then i
        else least)
      (-1) t


  let greatestp1_arg (t:term) (nargs:int): int =
    (** The greatest (plus 1) argument variable of the term [t] with
        [nargs] arguments or [nargs] if there is no argument variable
     *)
    fold_arguments
      (fun gtst i -> if gtst <= i then i+1 else gtst)
      0
      t
      nargs


  let split_variables (t:term) (n:int): IntSet.t * IntSet.t =
    (** The set of bound variables strictly below [n] and above [n]
       in the term [t].
     *)
    fold
      (fun (lset,uset) i ->
        if i < n then
          IntSet.add i lset, uset
        else
          lset, IntSet.add i uset)
      (IntSet.empty,IntSet.empty)
      t


  let variables_filtered (t:term) (f:int->bool): IntSet.t =
    (* The set of variables which satisfy the predicate [f] *)
    fold
      (fun set i ->
        if f i then
          IntSet.add i set
        else
          set)
      IntSet.empty
      t


  let free_variables (t:term) (nb:int): IntSet.t =
    (* The set of free variables above 'n' in the term 't' *)
    variables_filtered t (fun i -> nb <= i)



  let bound_variables (t:term) (nb:int): IntSet.t =
    (* The set of bound variables strictly below 'n' in the term 't' *)
    variables_filtered t (fun i -> i < nb)


  let range_variables (t:term) (start:int) (beyond:int): IntSet.t =
    (* The set of variables [i] with [start <= i < beyond] *)
    variables_filtered t (fun i -> start <= i && i < beyond)


  let used_variables_filtered (t:term) (f:int->bool): int list =
    (* The list of variables of the term [t] which satisfy [f] in reversed
       order in which they appear *)
    let lst,_ =
      fold
        (fun (lst,set) ivar ->
          if not (f ivar) || IntSet.mem ivar set then
            lst,set
          else
            ivar::lst, IntSet.add ivar set)
        ([], IntSet.empty)
        t
    in
    lst


  let used_variables (t:term) (nvars:int): int list =
    (* The list of variables of the term [t] below [nvars] in reversed order in
       which they appear *)
    used_variables_filtered t (fun i -> i < nvars)


  let used_variables_from (t:term) (nvars:int): int list =
    (* The list of variables of the term [t] from [nvars] on in reversed order in
       which they appear *)
    used_variables_filtered t (fun i -> nvars <= i)


  let equivalent (t1:term) (t2:term): bool =
    (* Are the terms [t1] and [t2] equivalent ignoring names and predicate flags? *)
    let rec eq t1 t2 nb =
      match t1, t2 with
        Variable i, Variable j ->
          i = j
      | Application (f1,args1,_), Application (f2,args2,_) ->
          let n = Array.length args1 in
          n = Array.length args2 &&
          eq f1 f2 nb &&
          interval_for_all (fun i -> eq args1.(i) args2.(i) nb) 0 n
      | Lam(n1,nms1,t1,_), Lam(n2,nms2,t2,_) when n1 = n2 ->
          eq t1 t2 (n1+nb)
      | QExp(n1,nms1,t1,is_all1), QExp(n2,nms2,t2,is_all2)
        when n1 = n2 && is_all1 = is_all2 ->
          eq t1 t2 (n1+nb)
      | _, _ ->
          false
    in
    eq t1 t2 0






  let map (f:int->int->term) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'f j nb' where 'nb' is the
       number of bound variables in the context where 'j' appears
     *)
    let rec mapr nb t =
      match t with
        Variable j -> f j nb
      | Application (a,b,pred) ->
          Application (mapr nb a, Array.map (fun t -> mapr nb t) b, pred)
      | Lam (nargs,names,t,pred) ->
          Lam(nargs, names, mapr (nb+nargs) t, pred)
      | QExp (nargs,names,t,is_all) ->
          QExp(nargs, names, mapr (nb+nargs) t, is_all)
    in
    mapr 0 t



  let down_from (n:int) (start:int) (t:term): term =
    (* Shift all free variables of [t] above [start] down by [n]. In case that
       free variables get captured raise 'Term_capture' *)
    if n = 0 then
      t
    else
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
       are no free variables 0,1,...,n-1, otherwise raise [Term_capture].
     *)
    down_from n 0 t



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


  let array_up (n:int) (arr:term array): term array =
    if n = 0 then arr
    else Array.map (fun t -> up n t) arr


  let map_free (f:int->term) (t:term) (start:int): term =
    (* Map the free variable 'i' of the term 't' to 'f i *)
    let fb (i:int) (nb:int): term =
      if i < nb+start then
        Variable i
      else
        up (nb+start) (f (i-nb-start))
    in
    map fb t





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

  let part_sub_from
      (t:term)
      (start:int)
      (nargs:int)
      (args:term array)
      (n_delta:int)
      : term =
    (** Perform a partial substitution.

        The term [t] has above [start] [nargs] argument variables. The first
        [Array.length args] of them will be substituted by the corresponding
        term in [args] and the others will be shifted down appropriately so
        that the new term has [(Array.length args)-nargs] argument variables.

        The arguments come from an environment with [n_delta] variables more
        than the term [t]. Therefore the variables in [t] above [start+nargs]
        have to be shifted up by [n_delta] to transform them into the
        environment of the arguments.  *)
    let len = Array.length args in
    assert (len <= nargs);
    map
      (fun j nb ->
        let nb1 = nb + start in
        if j < nb1 then
          Variable(j)
        else
          let jfree = j - nb1 in
          if jfree < len then
            let arg = args.(jfree) in
            assert (arg <> Variable (-1));
            up (nb1+nargs-len) arg
          else if jfree < nargs then
            Variable (j-len)
          else
            Variable(j+n_delta-len)
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
    part_sub_from t 0 nargs args n_delta


  let sub_from (t:term) (start:int) (args:term array) (nbound:int): term =
    (** substitute the free variables start,start+1,..,start+args.len-1 of the
        term [t] by the arguments [args] which are from an environment with
        [nbound] bound variables more than the variable of the term [t],
        i.e. all free variables above [len] are shifted up by
        [nbound-args.len] *)
    let len = Array.length args in
    part_sub_from t start len args nbound


  let sub (t:term) (args:term array) (nbound:int): term =
    (** substitute the free variables 0,1,args.len-1 of the term [t] by the
        arguments [args] which are from an environment with [nbound] bound
        variables more than the variables of the term [t], i.e. all free
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
    let app (f:term) (args: term array) (pr:bool): term =
      match f with
        Lam(nargs,_,t,pr) ->
          assert (nargs=(Array.length args));
          reduce (apply t args)
      | _ -> Application (f,args,pr)
    in
    match t with
      Variable _ -> t
    | Application (f,args,pr) ->
        let fr = reduce f
        and argsr = Array.map reduce args
        in
        app fr argsr pr
    | Lam(nargs,names,t,pred) ->
        assert (0 < nargs);
        let tred = reduce t in
          Lam (nargs, names, tred, pred)
    | QExp(nargs,names,t,is_all) ->
        assert (0 < nargs);
        let tred = reduce t in
          QExp (nargs, names, tred, is_all)


  let reduce_top (t:term): term =
    match t with
      Application (Lam (n,nms,t,_), args, _) ->
        assert (n = Array.length args);
        apply t args
    | _ -> raise Not_found


  let lambda_split (t:term): int * int array * term =
    match t with
      Lam (n,names,t,_) -> n,names,t
    | _ -> raise Not_found


  let qlambda_split (t:term): int * int array * term * bool =
    match t with
      QExp (n,names,t,is_all) -> n,names,t,is_all
    | _ -> raise Not_found


  let unary (unid:int) (t:term): term =
    let args = [| t |] in
    Application (Variable unid, args, false)


  let unary_split (t:term) (unid:int): term =
    match t with
      Application (f,args,_) ->
        let nargs = Array.length args in
        (match f with
          Variable i when i=unid ->
            if nargs=1 then args.(0)
            else assert false
        | _ -> raise Not_found)
    | _ -> raise Not_found


  let binary (binid:int) (left:term) (right:term): term =
    let args = [| left; right |] in
    Application (Variable binid, args,false)


  let binary_split_0 (t:term): int * term * term =
    match t with
      Application(Variable i,args,_) when Array.length args = 2 ->
        i, args.(0), args.(1)
    | _ ->
        raise Not_found


  let binary_split (t:term) (binid:int): term * term =
    let i,a,b = binary_split_0 t in
    if i = binid then
      a,b
    else
      raise Not_found



  let quantified (is_all:bool) (nargs:int) (names:int array) (t:term): term =
    assert (let nnms = Array.length names in nnms=0 || nnms = nargs);
    if nargs = 0 then
      t
    else
      QExp (nargs,names,t,is_all)


  let all_quantified (nargs:int) (names:int array) (t:term): term =
    quantified true nargs names t

  let some_quantified (nargs:int) (names:int array) (t:term): term =
    quantified false nargs names t


  let quantifier_split (t:term) (is_all:bool): int * int array * term =
    let n,nms,t0,is_all0 = qlambda_split t in
    if is_all = is_all0 then
      n,nms,t0
    else
      raise Not_found

  let all_quantifier_split (t:term): int * int array * term =
    quantifier_split t true

  let some_quantifier_split (t:term): int * int array * term =
    quantifier_split t false


  let rec binary_right (t:term) (binid:int): term list =
    let rec binr (t:term) (lst:term list): term list =
      match t with
        Application (f,args,_) when Array.length args = 2 ->
          begin
            match f with
              Variable i when i = binid ->
                binr args.(0) (args.(1) :: lst)
            | _ -> t::lst
          end
      | _ -> t::lst
    in
    binr t []




  let split_implication_chain (t:term) (impid:int)
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



  let rec make_implication_chain
      (ps:term list) (tgt:term) (imp_id:int): term =
    match ps with
      [] -> tgt
    | p::ps0 ->
        make_implication_chain
          ps0
          (binary imp_id p tgt)
          imp_id



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


  exception Out_of_order

  let is_normalized (t:term) (nargs:int) (nused:int): bool =
    (** Is the term [t] with [nargs] arguments normalized, i.e. do all
        its arguments appear in ascending order starting from zero without
        holse and is [nused] the number of used arguments?
     *)
    try
      nused = fold_arguments
        (fun n i -> (* [n] is the number of arguments which already have
                       appeared in ascending order *)
          assert (i < nargs);
          if i<n then n
          else if i=0 then n+1
          else raise Out_of_order)
        0  t nargs
    with Out_of_order -> false



  let normalize_base (t:term) (nargs:int): int array * int =
    (** Find for the term [t] with [nargs] arguments which
        normalize the term and the number of used variables.

        To normalize the term [t] apply
        [sub t (Array.map Variable args) nused].
     *)
    assert (0 < nargs);
    let arr   = Array.make nargs (-1)
    in
    let nused =
      fold_arguments
        (fun n i ->
          assert (i < nargs);
          if arr.(i) <> -1 then
            n
          else
            (arr.(i) <- n;  n+1))
        0  t nargs
    in
    arr, nused



  let used_args (t:term) (nargs:int): int array =
    (** The used arguments of the the term [t] with [nargs] arguments
        in the order in which they appear in the term.
     *)
    let arr, n = normalize_base t nargs in
    Array.of_list
      (Array.fold_right
         (fun i lst -> if i<>(-1) then i::lst else lst)
         arr
         [])



  let normalizing_args (t:term) (nargs:int): term array * int =
    (** Find for the term [t] with [nargs] arguments which
        normalize the term and the number of used variables.

        To normalize the term [t] apply [sub t args nused].
     *)
    assert (0 < nargs);
    let args, nused = normalize_base t nargs
    in
    Array.map (fun i -> Variable i) args,
    nused


  let normalize (t:term) (nargs:int) (nms:int array)
    (** Normalize the term [t] with [nargs] arguments and the argument
        names [nms]. I.e. reorder the arguments so that they appear in
        ascending sequence starting from zero without holes and reorder
        the names and return the number of used arguments.
     *)
      : term * int array * int =
    let lennms = Array.length nms in
    assert (lennms = 0 || lennms = nargs);
    let argspos,nused = normalize_base t nargs in
    let args  = Array.map (fun i -> Variable i) argspos
    in
    let tnorm =  sub t args nargs
    in
    let nms =
      if lennms <> 0 then
        let nms1 = Array.make nargs 0
        and unused0 = ref nused
        in
        Array.iteri
          (fun var pos ->
            let p =
              if pos <> (-1) then
                pos
              else
                (let p = !unused0 in unused0 := !unused0 + 1; p)
            in
            nms1.(p) <- nms.(var))
          argspos;
        assert false
      else
        nms
    in
    assert (is_normalized tnorm nargs nused);
    tnorm, nms, nused



  let keep_used (used: int array) (t:term) (nargs:int): term =
    (** Keep the used arguments [used] within the term [t] with
        [nargs] arguments as the first [0,1,..,nused-1] variables.

        Note: [used] must contain all used variables of the term [t]!
     *)
    let nused = Array.length used in
    assert (nused <= nargs);
    let args = Array.make nargs (Variable (-1))in
    Array.iteri
      (fun i var ->
        assert (var < nargs);
        args.(var) <- Variable i)
      used;
    sub t args nused

end (* Term *)






module Term_sub: sig
  type t
  val to_string:      t -> string
  val count:          t -> int
  val for_all:        (int -> term -> bool) -> t -> bool
  val iter:           (int -> term -> unit) -> t -> unit
  val is_identity:    t -> bool
  val is_injective:   t -> bool
  val empty:          t
  val identity:       int -> t
  val is_empty:       t -> bool
  val singleton:      int -> term -> t
  val find:           int -> t -> term
  val mem:            int -> t -> bool
  val add:            int -> term ->  t -> t
  val merge:          t -> t -> t
  val to_list:        t -> (int*term) list
  val arguments:      int -> t -> term array
  val has_only_variables: t -> bool
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
    IntMap.cardinal sub

  let for_all (f:int-> term -> bool) (sub:t): bool =
    IntMap.for_all f sub

  let iter (f:int -> term -> unit) (sub:t): unit =
    IntMap.iter f sub

  let is_identity (sub:t): bool =
    IntMap.for_all (fun i t -> Variable i = t) sub

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

  let is_empty(sub:t) = IntMap.is_empty sub

  let singleton (i:int) (t:term): t =
    IntMap.add i t IntMap.empty

  let find (i:int) (sub:t): term =
    IntMap.find i sub

  let mem (i:int) (sub:t): bool =
    IntMap.mem i sub

  let add (i:int) (t:term) (sub:t): t =
    assert (not (mem i sub));
    IntMap.add i t sub

  let identity (n:int): t =
    assert (0 <= n);
    let res = ref empty in
    for i = 0 to n-1 do
      res := add i (Variable i) !res
    done;
    !res

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
            if Term.equivalent t1 t2 then ()
            else ((*Printf.printf "    Cannot merge sub\n";*) raise Not_found)
      )
      sub1;
    !res

  let to_list (sub:t): (int*term) list =
    let lst = IntMap.fold (fun i t lst -> (i,t)::lst) sub [] in
    List.rev lst

  let arguments (nargs:int) (sub:t): term array =
    assert (IntMap.cardinal sub = nargs);
    let args = Array.make nargs (Variable (-1)) in
    IntMap.iter
      (fun i t ->
        assert (i<nargs);
        args.(i) <- t)
      sub;
    args

  let has_only_variables (sub:t): bool =
    for_all
      (fun i t ->
        match t with
          Variable i -> true
        | _ -> false)
      sub

end (* Term_sub *)
