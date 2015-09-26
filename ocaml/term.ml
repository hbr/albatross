(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Container

type flow =
    Ifexp
  | Inspect
  | Asexp

type term =
    Variable    of int
  | VAppl       of int * term array              (* fidx, args *)
  | Application of term * term array * bool      (* fterm, args, is_pred *)
  | Lam         of int * int array * term list * term * bool
                   (* n, names, pres, t, is_pred *)
  | QExp        of int * int array * term * bool (* n, names, t, is_all *)
  | Flow        of flow * term array
  | Indset      of int * int array * term array
                               (* number of sets, (usually one), names, rules *)
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

let string_of_flow (ctrl:flow): string =
  match ctrl with
    Ifexp   -> "if"
  | Inspect -> "inspect"
  | Asexp   -> "as"

module Term: sig

  val is_variable_i: term -> int -> bool

  val to_string: term -> string

  val variable:    term -> int
  val is_variable: term -> bool
  val is_argument: term -> int -> bool

  val nodes: term -> int

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

  val map: (int->int->int) -> term -> term

  val map_to_term: (int->int->term) -> term -> term

  val map_free: (int->int) -> term -> int -> term

  val down_from: int -> int -> term -> term

  val down: int -> term -> term

  val upbound: int->int->term->term

  val up: int->term->term

  val array_up: int -> term array -> term array

  val part_sub_from: term -> int -> int -> term array -> int -> term

  val part_sub: term -> int -> term array -> int -> term

  val sub_from: term -> int -> term array -> int -> term

  val sub:   term -> term array -> int -> term

  val apply: term -> term array -> term

  val lambda_split: term -> int * int array * term list * term * bool

  val qlambda_split_0: term -> int * int array * term * bool
  val qlambda_split: term -> int * int array * term * bool

  val unary: int -> term -> term

  val unary_split: term -> int -> term

  val quantified: bool -> int -> int array -> term -> term

  val all_quantified:  int -> int array -> term -> term

  val some_quantified:  int -> int array -> term -> term

  val quantifier_split: term -> bool -> int * int array * term

  val all_quantifier_split: term-> int * int array * term

  val some_quantifier_split: term -> int * int array * term

  val pattern: int -> int array -> term -> term
  val pattern_split: term -> int * int array * term
  val case_split: term -> term -> int * int array * term * term

  val binary: int -> term -> term -> term

  val binary_split_0: term -> int * term * term

  val binary_split: term -> int -> term * term

  val split_implication_chain: term -> int -> term list * term
  val make_implication_chain:  term list -> term -> int -> term

  val implication_chain: term -> int -> (term list * term) list

  val split_rule: term -> int -> int * int array * term list * term

  val closure_rule: int -> term -> term
  val induction_law: int -> term -> term
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
    let strlam nargs names pres t pred =
      let argsstr = string_of_int 0 in
      if pred then begin
        assert (pres = []); (* predicates don't have preconditions *)
        "{" ^ argsstr ^ ": " ^ (to_string t) ^ "}"
      end else
        match pres with
          [] -> "((" ^ argsstr ^ ")->" ^ (to_string t) ^ ")"
        | _ ->
            let presstr = String.concat ";" (List.map to_string pres) in
            "(agent(" ^ argsstr ^ ") require " ^
            presstr ^
            " ensure Result = " ^ (to_string t) ^ " end)"
    in
    match t with
      Variable i -> string_of_int i
    | VAppl (i,args) ->
        let fstr = string_of_int i
        and argsstr = Array.to_list (Array.map to_string args)
        in
        fstr ^ "v(" ^
        (String.concat "," argsstr)
        ^ ")"
    | Application (f,args,pr) ->
        let fstr = to_string f
        and argsstr = Array.to_list (Array.map to_string args)
        and predstr = if pr then "p" else "f"
        in
        fstr ^ predstr ^ "(" ^
        (String.concat "," argsstr)
        ^ ")"
    | Lam(nargs,names,pres,t,pred) ->
        strlam nargs names pres t pred
    | QExp (nargs,names,t,is_all) ->
        let argsstr = argsstr nargs names in
        let qstr    = if is_all then "all" else "some" in
        qstr ^ "(" ^ argsstr ^ ") " ^ (to_string t)
    | Flow (ctrl,args) ->
        let argsstr = Array.to_list (Array.map to_string args) in
        begin
          match ctrl with
            Ifexp ->
              assert (Array.length args <= 3);
              "if(" ^ (String.concat "," argsstr) ^ ")"
          | Inspect ->
              "inspect(" ^ (String.concat "," argsstr) ^ ")"
          | Asexp ->
              assert (Array.length args = 2);
              "as(" ^ (String.concat "," argsstr) ^ ")"
        end
    | Indset (n,nms,rs) ->
        "{(" ^ (string_of_int n) ^ "):"
        ^ (String.concat "," (List.map to_string (Array.to_list rs)))
        ^ "}"



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
    let nodeslst lst =
      List.fold_left (fun n t -> n + nodes t) 0 lst
    and nodesarr arr =
      Array.fold_left (fun sum t -> sum + (nodes t)) 0 arr
    in
    match t with
      Variable _ -> 1
    | VAppl (i,args) -> 1 + nodesarr args
    | Application (f,args,_) ->
        nodes f + nodesarr args
    | Lam (_,_,pres,t,_) ->
        1 + nodeslst pres + nodes t
    | QExp (_,_,t,_) ->
        1 + (nodes t)
    | Flow (ctrl,args) ->
        1 + nodesarr args
    | Indset (_,_,rs) ->
        1 + nodesarr rs





  let fold_with_level (f:'a->int->int->'a) (a:'a) (t:term): 'a =
    (** Fold the free variables with their level (from the top) in the order
        in which they appear in the term [t] with the function [f] and
        accumulate the results in [a].
     *)
    let rec fld (a:'a) (t:term) (level) (nb:int): 'a =
      let var i = if nb <= i then f a (i-nb) level else a
      and fldarr a arr =
        Array.fold_left (fun a t -> fld a t (level+1) nb) a arr
      in
      match t with
        Variable i -> var i
      | VAppl (i,args) ->
          let a = var i in
          fldarr a args
      | Application (f,args,_) ->
          let a = fld a f (level+1) nb in
          fldarr a args
      | Lam (n,_,pres,t,_) ->
          let level = 1 + level
          and nb    = 1 + nb in
          let a = List.fold_left (fun a t -> fld a t level nb) a pres in
          fld a t level nb
      | QExp (n,_,t,_) ->
          fld a t (level+1) (nb+n)
      | Flow (ctrl,args) ->
          fldarr a args
      | Indset (n,nms,rs) ->
          fldarr a rs
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
      | VAppl(i1,args1), VAppl(i2,args2)
        when i1 = i2 ->
          let n1 = Array.length args1
          and n2 = Array.length args2 in
          n1 = n2 &&
          interval_for_all (fun i -> eq args1.(i) args2.(i) nb) 0 n1
      | Application (f1,args1,_), Application (f2,args2,_) ->
          let n = Array.length args1 in
          n = Array.length args2 &&
          eq f1 f2 nb &&
          interval_for_all (fun i -> eq args1.(i) args2.(i) nb) 0 n
      | Lam(n1,nms1,pres1,t1,_), Lam(n2,nms2,pres2,t2,_) ->
          let nb = 1 + nb in
          (try List.for_all2 (fun t1 t2 -> eq t1 t2 nb) pres1 pres2
          with Invalid_argument _ -> false)
            &&
          eq t1 t2 nb
      | QExp(n1,nms1,t1,is_all1), QExp(n2,nms2,t2,is_all2)
        when n1 = n2 && is_all1 = is_all2 ->
          eq t1 t2 (n1+nb)
      | Flow(ctrl1,args1), Flow(ctrl2,args2) ->
          ctrl1 = ctrl2 &&
          let n1 = Array.length args1
          and n2 = Array.length args2 in
          n1 = n2 &&
          interval_for_all (fun i -> eq args1.(i) args2.(i) nb) 0 n1
      | Indset (n1,nms1,rs1), Indset (n2,nms2,rs2) ->
          let nrules1, nrules2 = Array.length rs1, Array.length rs2 in
          n1 = n2 &&
          nrules1 = nrules2 &&
          interval_for_all (fun i -> eq rs1.(i) rs2.(i) (n1+nb)) 0 nrules1
      | _, _ ->
          false
    in
    eq t1 t2 0



  let map (f:int->int->int) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'Variable(f j nb)' where 'nb'
       is the number of bound variables in the context where 'j' appears.
     *)
    let rec mapr nb t =
      let map_args nb args = Array.map (fun t -> mapr nb t) args
      in
      match t with
        Variable j -> Variable (f j nb)
      | VAppl (j,args) ->
          VAppl (f j nb, map_args nb args)
      | Application (a,b,pred) ->
          Application (mapr nb a, map_args nb b, pred)
      | Lam (nargs,names,pres,t,pred) ->
          let nb = 1 + nb in
          let pres = List.map (fun t -> mapr nb t) pres
          and t    = mapr nb t in
          Lam(nargs, names, pres, t, pred)
      | QExp (nargs,names,t,is_all) ->
          QExp(nargs, names, mapr (nb+nargs) t, is_all)
      | Flow (ctrl,args) ->
          Flow(ctrl,map_args nb args)
      | Indset (n,nms,rs) ->
          Indset (n,nms, map_args (n+nb) rs)

    in
    mapr 0 t


  let map_free (f:int->int) (t:term) (start:int): term =
    (* Map the free variable 'i' of the term 't' to 'f i *)
    let fb (i:int) (nb:int): int =
      if i < nb+start then
        i
      else
        nb + start + f (i-nb-start)
    in
    map fb t





  let map_to_term (f:int->int->term) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'f j nb' where 'nb' is the
       number of bound variables in the context where 'j' appears
     *)
    let rec mapr nb t =
      let map_args nb args = Array.map (fun t -> mapr nb t) args in
      match t with
        Variable j -> f j nb
      | VAppl (j,args) ->
          VAppl (j, Array.map (fun t -> mapr nb t) args)
      | Application (a,b,pred) ->
          Application (mapr nb a, map_args nb b, pred)
      | Lam (nargs,names,pres,t,pred) ->
          let nb = 1 + nb in
          let pres = List.map (fun t -> mapr nb t) pres
          and t = mapr nb t in
          Lam(nargs, names, pres , t, pred)
      | QExp (nargs,names,t,is_all) ->
          QExp(nargs, names, mapr (nb+nargs) t, is_all)
      | Flow (ctrl,args) ->
          Flow(ctrl, map_args nb args)
      | Indset (n,nms,rs) ->
          Indset (n,nms, map_args (n+nb) rs)

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
            j
          else if n <= j-nb-start then
            j - n
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
          if j<nb+start then
            j
          else
            j + n)
        t




  let up (n:int) (t:term): term =
    (* Shift all free variables up by 'n' in the term 't' *)
    upbound n 0 t


  let array_up (n:int) (arr:term array): term array =
    if n = 0 then arr
    else Array.map (fun t -> up n t) arr


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
    map_to_term
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
        that the new term has [nargs-(Array.length args)] argument variables.

        The arguments come from an environment with [n_delta] variables more
        than the term [t]. Therefore the variables in [t] above [start+nargs]
        have to be shifted up by [n_delta] to transform them into the
        environment of the arguments.  *)
    let len = Array.length args in
    assert (len <= nargs);
    let rec sub t nb =
      let sub_args nb args = Array.map (fun t -> sub t nb) args in
      let nb1 = nb + start in
      match t with
        Variable i when i < nb1 -> t
      | Variable i when i < nb1 + len ->
          up (nb1+nargs-len) args.(i-nb1)
      | Variable i when i < nb1 + nargs ->
          Variable (i-len)
      | Variable i ->
          Variable (i + n_delta - len)
      | VAppl (i,args) ->
          assert (nb1 + nargs - len <= i);
          VAppl (i + n_delta - len, sub_args nb args)
      | Application(f,args,pr) ->
          Application (sub f nb, sub_args nb args, pr)
      | Lam(n,nms,pres0,t0,pr) ->
          let nb = 1 + nb in
          let pres0 = List.map (fun t -> sub t nb) pres0
          and t0    = sub t0 nb in
          Lam (n, nms, pres0, t0, pr)
      | QExp(n,nms,t0,is_all) ->
          QExp (n, nms, sub t0 (n+nb), is_all)
      | Flow (ctrl,args) ->
          Flow (ctrl, sub_args nb args)
      | Indset (n,nms,rs) ->
          Indset (n,nms, sub_args (n+nb) rs)
    in
    sub t 0


  let part_sub (t:term) (nargs:int) (args:term array) (n_delta:int): term =
    (** Perform a partial substitution.

        The term [t] has [nargs] argument variables. The first
        [Array.length args] of them will be substituted by the corresponding
        term in [args] and the others will be shifted down appropriately so
        that the new term has [nargs-(Array.length args)] argument variables.

        The arguments come from an environment with [n_delta] variables more
        than the term [t]. Therefore the variables in [t] above [nargs] have
        to be shifted up by [n_delta] to transform them into the environment
        of the arguments.
     *)
    part_sub_from t 0 nargs args n_delta


  let sub_from (t:term) (start:int) (args:term array) (nbound:int): term =
    (** substitute the free variables start,start+1,..,start+args.len-1 of the
        term [t] by the arguments [args] which are from an environment with
        [nbound] bound variables more than the variables of the term [t],
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


  let lambda_split (t:term): int * int array * term list * term * bool =
    match t with
      Lam (n,names,pres,t,p) -> n,names,pres,t,p
    | _ -> raise Not_found


  let qlambda_split_0 (t:term): int * int array * term * bool =
    match t with
      QExp (n,names,t,is_all) -> n,names,t,is_all
    | _ ->
        0, [||], t, false

  let qlambda_split (t:term): int * int array * term * bool =
    match t with
      QExp (n,names,t,is_all) -> n,names,t,is_all
    | _ -> raise Not_found

  let pattern_split (t:term): int * int array * term =
    let n,nms,t,is_all = qlambda_split_0 t in
    assert (not is_all);
    n, nms, t

  let case_split (t1:term) (t2:term): int * int array * term * term =
    let n1,nms1,t1 = pattern_split t1
    and n2,nms2,t2 = pattern_split t2 in
    assert (n1 = n2);
    n1, nms1, t1, t2

  let unary (unid:int) (t:term): term =
    let args = [| t |] in
    VAppl (unid, args)


  let unary_split (t:term) (unid:int): term =
    match t with
      VAppl (i,args) when i = unid ->
        assert (Array.length args = 1);
        args.(0)
    | _ -> raise Not_found


  let binary (binid:int) (left:term) (right:term): term =
    let args = [| left; right |] in
    VAppl (binid, args)


  let binary_split_0 (t:term): int * term * term =
    match t with
      VAppl(i,args) when Array.length args = 2 ->
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


  let pattern (n:int) (nms:int array) (t:term): term =
    some_quantified n nms t

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


  let split_rule (t:term) (imp_id:int)
      : int * int array * term list * term =
    let n,nms,t0,is_all = qlambda_split_0 t in
    if n>0 && not is_all then
      0, [||], [], t
    else
      let ps_rev, tgt = split_implication_chain t0 (n+imp_id) in
      n,nms,ps_rev,tgt


  let rec make_implication_chain
      (ps_rev:term list) (tgt:term) (imp_id:int): term =
    (*  Make an implication chain from the reversed list of the premises, the target
        and the implication id.
     *)
    match ps_rev with
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


  let closure_rule (i:int) (t:term): term =
    assert (0 <= i);
    match t with
      Indset(n,nms,rs) ->
        if Array.length rs <= i then invalid_arg "Rule index out of bound";
        apply rs.(i) [|t|]
    | _ ->
        invalid_arg "Not an inductive set"




  let induction_law (imp_id:int) (p:term): term =
    (* Calculate the induction rule for the inductively defined set [p]

       all(a,q) p(a) ==> ind0 ==> ... ==> indn ==> q(a)

       indi: all(x,y,...) p(e1) ==> q(e1) ==>
                          ...
                          p(en) ==> q(en) ==>
                          e0              ==>
                          p(e) ==> q(e)

       where all(x,y,...) p(e1) ==> ... ==> p(en) ==> e0 ==> p(e) is the
       corresponding closure rule.
     *)
    let imp_id, p = imp_id + 2, up 2 p in (* space for a and q *)
    match p with
      Indset (n,nms,rs) ->
        assert (n = 1);
        let nrules = Array.length rs in
        let pair (n:int) (t:term): term * term =
          match t with
            Application(Variable i,args,pr) when i = n ->
              assert pr;
              assert (Array.length args = 1);
              sub_from t n [|p|] 0,
              sub_from t n [|Variable 1|] 0
          | _ ->
              raise Not_found
        in
        let rule (i:int): term =
          let n,nms,ps_rev,tgt = split_rule rs.(i) (imp_id+1) in
          let imp_id = imp_id + n in
          let chn =
            let t1,t2 =  try pair n tgt with Not_found -> assert false in
            binary imp_id t1 t2 in
          let chn = List.fold_left
              (fun chn t ->
                try
                  let t1,t2 = pair n t in
                  binary imp_id t1 (binary imp_id t2 chn)
                with Not_found ->
                  binary imp_id t chn)
              chn
              ps_rev in
          all_quantified n nms chn
        in
        let tgt =
          interval_fold
            (fun tgt j ->
              let i = nrules - j - 1 in
              let indi = rule i in
              binary imp_id indi tgt)
            (Application (Variable 1, [|Variable 0|],true))  (* q(a) *)
            0 nrules in
        let pa = Application (p,[|Variable 0|],true) in
        let t0 = binary imp_id pa tgt in
        all_quantified 2 [|ST.symbol "a";ST.symbol "q"|] t0
    | _ ->
        invalid_arg "Not an inductive set"
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
