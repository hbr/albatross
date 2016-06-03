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
  | VAppl       of int * arguments * arguments (* fidx, args, ags *)
  | Application of term * arguments * bool      (* fterm, args, is_pred *)
  | Lam         of int * names * term list * term * bool * type_term
                   (* n, names, pres, t, is_pred, type *)
  | QExp        of int * formals * formals * term * bool (* n, args, fgs, t, is_all *)
  | Flow        of flow * arguments
                   (* if:      args = [c e1 e2]   'e2' is optional
                      inspect: args = [inspe pat0 e0 pat1 e1 ... ]
                      as:      args = [e pat]
                    *)
  | Indset      of int * type_term * arguments (* name, type, rules *)
and names      = int array
and arguments  = term array
and agens      = type_term array
and types      = type_term array
and formals    = names * arguments
and type_term  = term

exception Term_capture
exception Empty_term
exception Name_clash of int

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


let empty_term:    term = Variable (-1)

let empty_formals: formals = [||], [||]


let standard_substitution (n:int): term array =
  assert (0 <= n);
  Array.init n (fun i -> Variable i)

let make_type (cls:int) (ags:arguments): type_term =
  VAppl (cls,ags,[||])


let count_formals ((nms,tps):formals): int =
  let n = Array.length nms in
  assert (n = Array.length tps);
  n


module Term: sig

  val is_variable_i: term -> int -> bool

  val to_string: term -> string

  val variable:    term -> int
  val is_variable: term -> bool
  val is_argument: term -> int -> bool

  val nodes0: term -> int -> int array -> int
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

  val used_variables_0:     term -> int -> int list -> int list
  val used_variables:       term -> int -> int list
  val used_variables_filtered: term -> (int -> bool) -> bool -> int list
  val used_variables_from:  term -> int -> bool -> int list
  val used_variables_transform: term -> int -> int array * int array
  val unused_transform:     formals -> int -> formals -> term ->
    formals * arguments * formals * arguments

  val equivalent: term -> term -> bool

  val equivalent_list: term list -> term list -> bool

  val equivalent_array: term array -> term array -> bool

  val map: (int->int->int) -> term -> term

  val map_to_term: (int->int->term) -> term -> term

  val map_free: (int->int) -> term -> int -> term

  val lambda_inner: term -> int -> term

  val lambda_inner_map: term -> int IntMap.t -> term

  val shift_from : int -> int -> int -> int -> term -> term
  val shift: int -> int -> term -> term

  val up_type:   int -> type_term -> type_term
  val down_type: int -> type_term -> type_term

  val down_from: int -> int -> term -> term

  val down: int -> term -> term

  val up_from: int->int->term->term

  val up: int->term->term

  val array_up: int -> term array -> term array

  val subst0_from: term -> int -> int -> arguments -> int -> int -> arguments -> term

  val subst0: term -> int -> term array -> int -> term array -> term

  val subst_from: term -> int -> int -> arguments -> term
  val subst:      term -> int -> arguments -> term
  val subst_array:arguments -> int -> arguments -> arguments

  val apply0: term -> term array -> term array -> term
  val apply:  term -> term array -> term

  val lambda_split: term -> int * int array * term list * term * bool * type_term

  val qlambda_split_0: term -> int * formals * formals * term * bool
  val qlambda_split: term -> int * formals * formals * term * bool

  val unary: int -> term -> term

  val unary_split: term -> int -> term

  val quantified: bool -> int -> formals -> formals -> term -> term

  val all_quantified:  int -> formals -> formals -> term -> term

  val some_quantified:  int -> formals -> term -> term

  val quantifier_split: term -> bool -> int * formals * formals * term

  val all_quantifier_split: term-> int * formals * formals * term

  val some_quantifier_split: term -> int * formals * term

  val is_all_quantified: term -> bool
  val is_generic: term -> bool

  val pattern: int -> formals -> term -> term
  val pattern_split: term -> int * formals * term
  val case_split: term -> term -> int * formals * term * term

  val binary: int -> term -> term -> term

  val binary_split_0: term -> int * term * term

  val binary_split: term -> int -> term * term

  val split_implication_chain: term -> int -> term list * term
  val make_implication_chain:  term list -> term -> int -> term

  val split_left_binop_chain: term -> int -> term list

  val split_general_implication_chain: term -> int -> int * formals * term list * term

  val closure_rule:   int -> term -> term -> term
  val induction_rule: int -> int -> term -> term -> term
    -> int * formals * term list * term
  val induction_law:  int -> term -> term -> type_term -> type_term -> term
  val prenex: term -> int -> int -> int -> term

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
            " ensure -> " ^ (to_string t) ^ " end)"
    in
    match t with
      Variable i -> string_of_int i
    | VAppl (i,args,_) ->
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
    | Lam(nargs,names,pres,t,pred,_) ->
        strlam nargs names pres t pred
    | QExp (nargs,(names,_),_,t,is_all) ->
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

  let nodes0 (t:term) (nb:int) (cargs:int array): int =
    (* The number of nodes in the term [t] which has [nb] bound variable,
       [#cargs] number of arguments. The arguments are substituted by terms
       which have a node count corresponding to the array [cargs].
     *)
    let nargs = Array.length cargs in
    let rec nds t nb =
      let ndsarr n args =
        Array.fold_left (fun sum t -> sum + nds t nb) n args
      in
      match t with
        Variable i when nb <= i && i < nb + nargs ->
          cargs.(i - nb)
      | Variable _ ->
          1
      | VAppl (i,args,_) ->
          ndsarr 1 args
      | Application (f,args,_) ->
          ndsarr (nds f nb) args
      | Lam (_,_,pres,t,_,_) ->
          1 + nds t (1 + nb) (* preconditions are not counted *)
      | QExp (n,_,_,t,_) ->
          1 + nds t (n + nb)
      | Flow (ctrl,args) ->
          ndsarr 1 args
      | Indset (_,_,rs) ->
          ndsarr 1 rs
    in
    nds t nb

  let rec nodes (t:term): int =
    (* The number of nodes in the term t *)
    let nodesarr arr =
      Array.fold_left (fun sum t -> sum + (nodes t)) 0 arr
    in
    match t with
      Variable _ -> 1
    | VAppl (i,args,_) -> 1 + nodesarr args
    | Application (f,args,_) ->
        nodes f + nodesarr args
    | Lam (_,_,pres,t,_,_) ->
        1 + nodes t (* preconditions are not counted *)
    | QExp (_,_,_,t,_) ->
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
      and fldarr a arr nb =
        Array.fold_left (fun a t -> fld a t (level+1) nb) a arr
      in
      match t with
        Variable i -> var i
      | VAppl (i,args,_) ->
          let a = var i in
          fldarr a args nb
      | Application (f,args,_) ->
          let a = fld a f (level+1) nb in
          fldarr a args nb
      | Lam (n,_,pres,t,_,_) ->
          let level = 1 + level
          and nb    = 1 + nb in
          let a = List.fold_left (fun a t -> fld a t level nb) a pres in
          fld a t level nb
      | QExp (n,_,_,t,_) ->
          fld a t (level+1) (nb+n)
      | Flow (ctrl,args) ->
          fldarr a args nb
      | Indset (n,nms,rs) ->
          fldarr a rs (n+nb)
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



  let equivalent (t1:term) (t2:term): bool =
    (* Are the terms [t1] and [t2] equivalent ignoring names and predicate flags? *)
    let rec eq t1 t2 nb =
      match t1, t2 with
        Variable i, Variable j ->
          i = j
      | VAppl(i1,args1,_), VAppl(i2,args2,_)
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
      | Lam(n1,nms1,pres1,t1,_,_), Lam(n2,nms2,pres2,t2,_,_) ->
          let nb = 1 + nb in
          (try List.for_all2 (fun t1 t2 -> eq t1 t2 nb) pres1 pres2
          with Invalid_argument _ -> false)
            &&
          eq t1 t2 nb
      | QExp(n1,_,_,t1,is_all1), QExp(n2,_,_,t2,is_all2)
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

  let equivalent_list (lst1:term list) (lst2:term list): bool =
    List.for_all2 (fun t1 t2 -> equivalent t1 t2) lst1 lst2


  let equivalent_array (arr1:term array) (arr2:term array): bool =
    let len = Array.length arr1 in
    len = Array.length arr2
      &&
    interval_for_all
      (fun i -> equivalent arr1.(i) arr2.(i))
      0 len



  let rec shift_from
      (delta1:int) (start1:int)
      (delta2:int) (start2:int)
      (t:term)
      : term =
    (* Shift all free variables by [delta1] starting from [start1] and all
       free type variables by [delta2] starting from [start2]. Raise
       [Term_capture] if a free variable gets bound.
     *)
    if delta1 = 0 && delta2 = 0 then
      t
    else
      let shift_i delta start i =
        if i < start then
          i
        else if i + delta < start then
          raise Term_capture
        else
          i + delta
      and shift_args d1 s1 d2 s2 args =
        if d1=0 && d2 = 0 then args
        else Array.map (fun t -> shift_from d1 s1 d2 s2 t) args
      and shift_list d1 s1 d2 s2 lst =
        if d1=0 && d2 = 0 then lst
        else List.map (fun t -> shift_from d1 s1 d2 s2 t) lst in
      match t with
        Variable i ->
          Variable (shift_i delta1 start1 i)
      | VAppl(j,args,ags) ->
          VAppl(shift_i delta1 start1 j,
                shift_args delta1 start1 delta2 start2 args,
                shift_args delta2 start2 0 0 ags)
      | Application(f,args,pr) ->
          Application(shift_from delta1 start1 delta2 start2 f,
                      shift_args delta1 start1 delta2 start2 args,
                      pr)
      | Lam(n,nms,pres,t,pred,tp) ->
          let start1 = 1 + start1 in
          Lam(n,nms,
              shift_list delta1 start1 delta2 start2 pres,
              shift_from delta1 start1 delta2 start2 t,
              pred,
              shift_from delta2 start2 0 0 tp)
      | QExp (n,(nms,tps),(fgnms,fgcon),t0,is_all) ->
          assert (n = Array.length tps);
          let start1 = n + start1
          and start2 = Array.length fgcon + start2 in
          QExp(n,
               (nms,   shift_args delta2 start2 0 0 tps),
               (fgnms, shift_args delta2 start2 0 0 fgcon),
               shift_from delta1 start1 delta2 start2 t0,
               is_all)
      | Flow (ctrl,args) ->
          Flow (ctrl, shift_args delta1 start1 delta2 start2 args)
      | Indset (nme,tp,rs) ->
          let start1 = 1 + start1 in
          Indset(nme,
                 shift_from delta2 start2 0 0 tp,
                 shift_args delta1 start1 delta2 start2 rs)



  let shift (d1:int) (d2:int) (t:term): term =
    shift_from d1 0 d2 0 t

  let shift_type (delta:int) (t:type_term): type_term =
    shift_from delta 0 0 0 t

  let up_type (n:int) (tp:type_term): type_term =
    shift_type n tp

  let down_type (n:int) (tp:type_term): type_term =
    shift_type (-n) tp


  let up_from (n:int) (start:int) (t:term): term =
    shift_from n start 0 0 t

  let up (n:int) (t:term): term =
    shift_from n 0 0 0 t

  let array_up (n:int) (arr:term array): term array =
    if n = 0 then
      arr
    else
      Array.map (fun t -> up n t) arr

  let down_from (n:int) (start:int) (t:term): term =
    shift_from (-n) start 0 0 t

  let down (n:int) (t:term): term =
    shift_from (-n) 0 0 0 t

  let rec partial_subst_from
      (t:term)
      (n1:int) (nb1:int) (d1:int) (args1:term array)
      (n2:int) (nb2:int) (d2:int) (args2:term array)
      : term =
    (*  Perform a partial substitution.

        The term [t] has [n1] argument variables and [n2] type variables and
        below [nb1/nb2] bound variables.  The first [Array.length args] of the
        arguments and the first [Array.length ags] of the type variables will
        be substituted by the corresponding terms/types in [args/ags] and the
        others will be shifted down appropriately so that the new term has
        [Array.length args - nargs] argument variables and [Array.length ags -
        ntvs] type variables.

        The arguments come from an environment with [d1/d2] variables/type
        variables more than the term [t]. Therefore the variables/type
        variables in [t] above [n1/n2] have to be shifted up by
        [n_delta/ntvs_delta] to transform them into the environment of the
        arguments.  *)
    let len1,len2    = Array.length args1, Array.length args2  in
    assert (len1 <= n1);
    assert (len2 <= n2);
    let free i = assert (nb1+n1 <= i); i+d1-len1 in
    let sub_args args n1 nb1 d1 args1 n2 nb2 d2 args2 =
      Array.map
        (fun t -> partial_subst_from t n1 nb1 d1 args1 n2 nb2 d2 args2)
        args
    and sub_list lst n1 nb1 d1 args1 n2 nb2 d2 args2 =
      List.map
        (fun t -> partial_subst_from t n1 nb1 d1 args1 n2 nb2 d2 args2)
        lst in
    if len1=0 && d1=0 && len2=0 && d2=0 then
      t
    else
      match t with
        Variable i when i < nb1 ->
          t
      | Variable i when i < nb1+len1 ->
          if args1.(i-nb1) = empty_term then
            raise Empty_term;
          shift (nb1+n1-len1) 0 args1.(i-nb1)
      | Variable i when i < nb1+n1 ->
          Variable (i-len1)
      | Variable i ->
          Variable (free i)
      | VAppl(j,args,ags) ->
          VAppl(free j,
                sub_args args n1 nb1 d1 args1 n2 nb2 d2 args2,
                sub_args ags  n2 nb2 d2 args2 0  0   0  [||])
      | Application (f,args,pr) ->
          Application (partial_subst_from f n1 nb1 d1 args1 n2 nb2 d2 args2,
                       sub_args args n1 nb1 d1 args1 n2 nb2 d2 args2,
                       pr)
      | Lam (n,nms,ps,t0,pr,tp) ->
          let nb1 = 1 + nb1 in
          Lam (n,nms,
               sub_list ps n1 nb1 d1 args1 n2 nb2 d2 args2,
               partial_subst_from t0 n1 nb1 d1 args1 n2 nb2 d2 args2,
               pr,
               partial_subst_from tp n2 nb2 d2 args2 0  0   0  [||])
      | QExp (n,(nms,tps),(fgnms,fgtps),t0,is_all) ->
          let nb1 = n + nb1
          and nb2 = nb2 + Array.length fgtps in
          QExp(n,
               (nms,   sub_args tps   n2 nb2 d2 args2 0 0 0 [||]),
               (fgnms, sub_args fgtps n2 nb2 d2 args2 0 0 0 [||]),
               partial_subst_from t0 n1 nb1 d1 args1 n2 nb2 d2 args2,
               is_all)
      | Flow(ctrl,args) ->
          Flow (ctrl, sub_args args n1 nb1 d1 args1 n2 nb2 d2 args2)
      | Indset (nme,tp,rs) ->
          let nb1 = 1 + nb1 in
          Indset (nme,
                  partial_subst_from tp n2 nb2 d2 args2 0 0 0 [||],
                  sub_args           rs n1 nb1 d1 args1 n2 nb2 d2 args2)



  let partial_subst
      (t:          term)
      (n1:int) (d1:int) (args1:term array)
      (n2:int) (d2:int) (args2:term array)
      : term =
    (*  Perform a partial substitution.

        The term [t] has [n1] argument variables and [n2] type variables.  The
        first [Array.length args] of the arguments and the first [Array.length
        ags] of the type variables will be substituted by the corresponding
        terms/types in [args/ags] and the others will be shifted down
        appropriately so that the new term has [Array.length args - n1]
        argument variables and [Array.length ags - n2] type variables.

        The arguments come from an environment with [d1/d2] variables/type
        variables more than the term [t]. Therefore the variables/type
        variables in [t] above [n1/n2] have to be shifted up by [d1/d2] to
        transform them into the environment of the arguments.  *)
    partial_subst_from t n1 0 d1 args1 n2 0 d2 args2



  let subst0_from
      (t:term)
      (nb1:int) (d1:int) (args1:term array)
      (nb2:int) (d2:int) (args2:term array)
      : term =
    let n1,n2 = Array.length args1, Array.length args2 in
    partial_subst_from t n1 nb1 d1 args1 n2 nb2 d2 args2


  let subst0
      (t:term)
      (d1:int) (args1:term array)
      (d2:int) (args2:term array): term =
    (*  Perform a substitution.

        The term [t] has [Array.length args1] argument variables and
        [Array.length args2] type variables.  The arguments and type variables
        will be substituted by the terms/types in the arrays, the others will
        be shifted down appropriately so that the new term has neither
        argument nor type variables.

        The arguments come from an environment with [d1/d2] variables/type
        variables more than the term [t] (above the variables). Therefore the
        variables/type variables in [t] above have to be shifted up by
        [d1/d2] to transform them into the environment of the arguments.  *)
    subst0_from t 0 d1 args1 0 d2 args2


  let apply0 (t:term) (args1:term array) (args2: term array): term =
    let n1,n2 = Array.length args1, Array.length args2 in
    partial_subst_from t n1 0 0 args1 n2 0 0 args2


  let apply (t:term) (args:term array): term =
    let n1 = Array.length args in
    partial_subst_from t n1 0 0 args 0 0 0 [||]


  let subst_from (t:term) (nb:int) (d:int) (args:arguments): term =
    subst0_from t nb d args 0 0 [||]

  let subst (t:term) (d:int) (args:arguments): term =
    (* Substitute the arguments of the term [t] by the actual arguments [args] which
       have [d] more variables than the term [t] above its arguments. I.e. all
       variables in [t] above [nargs] have to be shifted up. *)
    subst_from t 0 d args


  let subst_array (arr:term array) (d:int) (args:arguments): arguments =
    (* Substitute the arguments of the array [arr] by the actual arguments
       [args] which have [d] more variables than the term [t] above its
       arguments. I.e. all variables in [t] above [nargs] have to be shifted
       up. *)
    Array.map (fun t -> subst t d args) arr


  let swap_variable_blocks (n1:int) (m1:int) (n2:int) (m2:int) (t:term): term =
    (* The term [t] has [n1+m1] variables and [n2+m2] type variables. The
       variables and type variables in the two blocks have to be swapped *)
    let new_var i n m = if i<n then m+i else i-n in
    let mkargs n m = Array.init (n+m) (fun i -> Variable(new_var i n m)) in
    let args1 = mkargs n1 m1
    and args2 = mkargs n2 m2 in
    subst0 t (n1+m1) args1 (n2+m2) args2



  let map (f:int->int->int) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'Variable(f j nb)' where 'nb'
       is the number of bound variables in the context where 'j' appears.
     *)
    let rec mapr nb t =
      let map_args nb args = Array.map (fun t -> mapr nb t) args
      in
      match t with
        Variable j -> Variable (f j nb)
      | VAppl (j,args,ags) ->
          VAppl (f j nb, map_args nb args, ags)
      | Application (a,b,pred) ->
          Application (mapr nb a, map_args nb b, pred)
      | Lam (nargs,names,pres,t,pred,tp) ->
          let nb = 1 + nb in
          let pres = List.map (fun t -> mapr nb t) pres
          and t    = mapr nb t in
          Lam(nargs, names, pres, t, pred,tp)
      | QExp (nargs,args,fgs,t,is_all) ->
          QExp(nargs, args, fgs, mapr (nb+nargs) t, is_all)
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


  let  lambda_inner (t:term) (i:int): term =
    (* Extract a lambda inner term where variable [i] becomes variable [0], all
       other variables are shifted one up.
     *)
    let f j =
      if j=i then
        0
      else
        j+1
    in
    map_free f t 0


  let  lambda_inner_map (t:term) (map:int IntMap.t): term =
    (* Extract a lambda inner term where [map] maps i,j,k,... to the range
       0,1,...,n-1 where [n] is the cardinality of [map]. The variables from
       the map become the variables 0,1,...,n-1 and all other variables are
       shiftet up by [n]. *)
    let n = IntMap.cardinal map in
    let f j =
      try
        let i = IntMap.find j map in
        assert (i < n); i
      with Not_found ->
        j + n
    in
    map_free f t 0


  let map_to_term (f:int->int->term) (t:term): term =
    (* Map all variables 'j' of the term 't' to 'f j nb' where 'nb' is the
       number of bound variables in the context where 'j' appears
     *)
    let rec mapr nb t =
      let map_args nb args = Array.map (fun t -> mapr nb t) args in
      match t with
        Variable j -> f j nb
      | VAppl (j,args,ags) ->
          VAppl (j, Array.map (fun t -> mapr nb t) args, ags)
      | Application (a,b,pred) ->
          Application (mapr nb a, map_args nb b, pred)
      | Lam (nargs,names,pres,t,pred,tp) ->
          let nb = 1 + nb in
          let pres = List.map (fun t -> mapr nb t) pres
          and t = mapr nb t in
          Lam(nargs, names, pres , t, pred, tp)
      | QExp (nargs,args,fgs,t,is_all) ->
          QExp(nargs, args, fgs, mapr (nb+nargs) t, is_all)
      | Flow (ctrl,args) ->
          Flow(ctrl, map_args nb args)
      | Indset (n,nms,rs) ->
          Indset (n,nms, map_args (n+nb) rs)

    in
    mapr 0 t



  let used_variables_filtered_0
      (t:term) (f:int->bool) (dup:bool) (lst:int list)
      : int list =
    (* The list of variables of the term [t] which satisfy [f] in reversed
       order in which they appear *)
    fold
      (fun lst ivar ->
        if f ivar && (dup || not (List.mem ivar lst)) then ivar::lst
        else lst)
      lst
      t




  let used_variables_filtered (t:term) (f:int->bool) (dup:bool): int list =
    (* The list of variables of the term [t] which satisfy [f] in reversed
       order in which they appear *)
    used_variables_filtered_0 t f dup []



  let used_variables_0 (t:term) (nvars:int) (lst:int list): int list =
    (* The list of variables of the term [t] below [nvars] in reversed order in
       which they appear, accumulated to the list [lst] *)
    used_variables_filtered_0 t (fun i -> i < nvars) false lst


  let used_variables (t:term) (nvars:int): int list =
    (* The list of variables of the term [t] below [nvars] in reversed order in
       which they appear *)
    used_variables_0 t nvars []


  let used_variables_from (t:term) (nvars:int) (dup:bool): int list =
    (* The list of variables of the term [t] from [nvars] on in reversed order in
       which they appear *)
    used_variables_filtered t (fun i -> nvars <= i) dup



  let used_variables_transform (t:term) (nvars:int): int array * int array =
    (* Analyze the used variables of the term [t] with variables in the interval
       0,1,...,nvars-1 and return two arrays.

       arr1: 0,1,...nused-1     index of the used variable i
       arr2: 0,1,...nvars-1     position of the variable i in the term [t]
     *)
    let arr1  = Array.of_list (List.rev (used_variables t nvars)) in
    let nused = Array.length arr1 in
    let arr2  = Array.make nvars (-1) in
    for i = 0 to nused - 1 do
      arr2.(arr1.(i)) <- i
    done;
    arr1, arr2




  let used_variables_arr_transform (arr:term array) (nvars:int)
      : int array * int array =
    (* Analyze the used variables of the array of term [arr] with variables in
       the interval 0,1,...,nvars-1 and return two arrays.

       arr1: 0,1,...nused-1     index of the used variable i
       arr2: 0,1,...nvars-1     position of the variable i in the array [arr1]
     *)
    let lst =
      Array.fold_left
        (fun lst t -> used_variables_0 t nvars lst)
        []
        arr in
    let arr1  = Array.of_list (List.rev lst) in
    let nused = Array.length arr1 in
    let arr2  = Array.make nvars (-1) in
    for i = 0 to nused - 1 do
      arr2.(arr1.(i)) <- i
    done;
    arr1, arr2



  let unused_transform
      ((nms,tps):    formals)
      (ntvs:int)
      ((fgnms,fgcon):formals)
      (t:term)
      : formals  * arguments * formals  * agens =
    (* Find the used variables in the term [t] and the used type variables in the
       types [tps].

       It is required that the type variables in the range 0,..,ntvs-1 are not
       used anymore.

       Generate arguments which map the used variables to their new position
       and actual generics which map the used type variables to their new
       position.

       The new positions are generated in the order of appearance in the term
       [t] and the types [tps].

       Transform the signature (nms,tps) and the formal generics (fgnms,fgcon)
       with the arguments and the actual generics.
     *)
    let n1,n2 = Array.length nms, ntvs + Array.length fgnms
    in
    let usd,pos = used_variables_transform t n1 in
    let n1new = Array.length usd in
    let args  = Array.map (fun i -> Variable i) pos
    and nms   = Array.init n1new (fun i -> nms.(usd.(i)))
    and tps   = Array.init n1new (fun i -> tps.(usd.(i)))
    in
    let usd,pos = used_variables_arr_transform tps n2 in
    let n2new = Array.length usd in
    assert (interval_for_all (fun i -> ntvs<=usd.(i)) 0 n2new);
    let ags   = Array.map (fun i -> Variable i) pos (* might create [empty_term] *)
    and fgnms = Array.init n2new (fun i -> fgnms.(usd.(i)))
    and fgcon = Array.init n2new (fun i -> fgcon.(usd.(i)))
    in
    let tps   = subst_array tps   n2new ags
    and fgcon = subst_array fgcon n2new ags
    in
    (nms,tps), args, (fgnms,fgcon), ags



  let remove_unused
      ((nms,tps):formals)
      (ntvs:int)
      ((fgnms,fgcon):formals)
      (t:term)
      : formals * formals * term =
    let (nms,tps), args, (fgnms,fgcon), ags =
      unused_transform (nms,tps) ntvs (fgnms,fgcon) t in
    let n1new = Array.length nms
    and n2new = Array.length fgnms in
    let t = subst0 t n1new args n2new ags in
    (nms,tps), (fgnms,fgcon), t



  let lambda_split (t:term): int * names * term list * term * bool * type_term =
    match t with
      Lam (n,nms,pres,t,p,tp) -> n,nms,pres,t,p,tp
    | _ -> raise Not_found


  let qlambda_split_0 (t:term): int * formals * formals * term * bool =
    match t with
      QExp (n,args,fgs,t,is_all) -> n,args,fgs,t,is_all
    | _ ->
        0, empty_formals, empty_formals, t, false

  let qlambda_split (t:term): int * formals * formals * term * bool =
    match t with
      QExp (n,args,fgs,t,is_all) -> n,args,fgs,t,is_all
    | _ -> raise Not_found

  let pattern_split (t:term): int * formals * term =
    let n,fargs,_,t,is_all = qlambda_split_0 t in
    assert (not is_all);
    n, fargs, t

  let case_split (t1:term) (t2:term): int * formals * term * term =
    let n1,fargs1,t1 = pattern_split t1
    and n2,fargs2,t2 = pattern_split t2 in
    assert (n1 = n2);
    n1, fargs1, t1, t2


  let unary (unid:int) (t:term): term =
    let args = [| t |] in
    VAppl (unid,args,[||])


  let unary_split (t:term) (unid:int): term =
    match t with
      VAppl (i,args,_) when i = unid ->
        assert (Array.length args = 1);
        args.(0)
    | _ -> raise Not_found


  let binary (binid:int) (left:term) (right:term): term =
    let args = [| left; right |] in
    VAppl (binid, args, [||])


  let binary_split_0 (t:term): int * term * term =
    match t with
      VAppl(i,args,_) when Array.length args = 2 ->
        i, args.(0), args.(1)
    | _ ->
        raise Not_found


  let binary_split (t:term) (binid:int): term * term =
    let i,a,b = binary_split_0 t in
    if i = binid then
      a,b
    else
      raise Not_found



  let quantified (is_all:bool) (nargs:int) (args:formals) (fgs:formals) (t:term)
      : term =
    begin
      let (nms,tps), (fgnms,fgcon) = args, fgs in
      let n1,n2 = Array.length nms, Array.length fgnms in
      assert (n1 = Array.length tps);
      assert (n2 = Array.length fgcon);
      assert (nargs = 0 || nargs = n1)
    end;
    if nargs = 0 then
      t
    else
      QExp (nargs,args,fgs,t,is_all)


  let all_quantified (nargs:int) (args:formals) (fgs:formals) (t:term): term =
    quantified true nargs args fgs t

  let some_quantified (nargs:int) (args:formals)(t:term): term =
    quantified false nargs args empty_formals t


  let pattern (n:int) (args:formals) (t:term): term =
    some_quantified n args t


  let quantifier_split (t:term) (is_all:bool): int * formals * formals * term =
    let n,args,fgs,t0,is_all0 = qlambda_split t in
    if is_all = is_all0 then
      n,args,fgs,t0
    else
      raise Not_found


  let all_quantifier_split (t:term): int * formals * formals * term =
    quantifier_split t true

  let some_quantifier_split (t:term): int * formals * term =
    let n,tps,fgs,t = quantifier_split t false in
    assert (fgs = empty_formals);
    n,tps,t


  let is_all_quantified (t:term): bool =
    try ignore (all_quantifier_split t); true
    with Not_found -> false


  let is_generic (t:term): bool =
    try
      let _,_,(fgnms,fgcon),_ = all_quantifier_split t in
      let nfgs = Array.length fgnms in
      assert (nfgs = Array.length fgcon);
      nfgs > 0
    with Not_found ->
      false


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



  let split_left_binop_chain (t:term) (op_id:int): term list =
    (* If the term [t] has the form

           a op b op c op ... op z

       and the operator represented by [op_id] is left associative i.e.

           ((..(a op b) op c) .. ) op z

       then
       return the list

           [a,b,c,...,z]
     *)
    let rec split t lst =
      try
        let a,b = binary_split t op_id in
        split a (b :: lst)
      with Not_found ->
        t :: lst
    in
    split t []




  let split_general_implication_chain (t:term) (imp_id:int)
      : int * formals * term list * term =
    let n,fargs,fgs,t0,is_all = qlambda_split_0 t in
    assert (fgs = empty_formals);
    if n>0 && not is_all then
      0, empty_formals, [], t
    else
      let ps_rev, tgt = split_implication_chain t0 (n+imp_id) in
      n,fargs,ps_rev,tgt


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


  let prepend_names (nms1:int array) (nms2:int array): int array =
    let n1,n2 = Array.length nms1, Array.length nms2 in
    interval_iter
      (fun i ->
        if interval_exist (fun j -> nms1.(i)=nms2.(j)) 0 n2 then
          raise (Name_clash nms1.(i))
        else
          ())
      0 n1;
    Array.append nms1 nms2



  let rec prenex (t:term) (nb:int) (nb2:int) (imp_id:int): term =
    (* Calculate the prenex normal form of the term [t] with respect to
       universal quantifiers. All universal quantifiers are bubbled up in
       implication chains and merged with the upper universal
       quantifier. Unused variables in universally quantified expressions are
       eliminated. Variables are ordered according to their appearance.

       Note: The implication index is valid in the global environment!!
     *)
   let n,tps,fgs,t0 = prenex_0 t nb 0 nb2 imp_id in
   all_quantified n tps fgs t0



  and prenex_0 (t:term) (nb:int) (nargs:int) (nb2:int) (imp_id:int)
      : int * formals * formals * term =
    (* Calculate the number of variables (with their names and types) which
       bubble up from the term [t] because the target of an implication chain
       is universally quantified.

       nb:    total number of variables in the environment
       nargs: number of the variables to which bubbled up variables have to
              be appended
     *)
    let norm_args (args:term array) (nb:int) (nb2:int): term array =
      Array.map (fun t -> prenex t nb nb2 imp_id) args
    and norm_lst  (lst: term list) (nb:int) (nb2:int): term list =
      List.map (fun t -> prenex t nb nb2 imp_id) lst in
    match t with
      Variable i -> 0, empty_formals, empty_formals, t
    | VAppl(i,args,ags) when i = nb + imp_id ->
        assert (Array.length args = 2);
        assert (Array.length ags  = 0);
        let a = prenex args.(0) nb nb2 imp_id
        and n,(nms,tps),(fgnms,fgcon),b1 =
          prenex_0 args.(1) nb nargs nb2 imp_id in
        let a1 = shift n (Array.length fgnms) a in
        assert (not (is_all_quantified b1));
        let t = VAppl(i+n,[|a1;b1|],ags) in
        n, (nms,tps), (fgnms,fgcon), t
    | VAppl(i,args,ags) ->
        0, empty_formals, empty_formals,
        VAppl(i, norm_args args nb nb2, ags)
    | Application(f,args,pr) ->
        let f = prenex f nb nb2 imp_id
        and args = norm_args args nb nb2 in
        0, empty_formals, empty_formals, Application(f,args,pr)
    | Lam(n,nms,ps,t0,pr,tp) ->
        let ps = norm_lst ps (1+nb) nb2
        and t0 = prenex t0 (1+nb) nb2 imp_id in
          0, empty_formals, empty_formals, Lam(n,nms,ps,t0,pr,tp)
    | QExp(n0,(nms,tps),(fgnms,fgcon),t0,true) ->
        let nb  = nb  + n0
        and nb2 = nb2 + Array.length fgnms in
        let n1,(nms1,tps1),(fgnms1,fgcon1),t1 =
          prenex_0 t0 nb (n0+nargs) nb2 imp_id in
        assert (not (is_all_quantified t1));
        let nms   = prepend_names nms1 nms
        and tps   = Array.append tps1 tps
        and fgnms = prepend_names fgnms fgnms1
        and fgcon = Array.append fgcon fgcon1
        in
        let (nms,tps),(fgnms,fgcon),t1 =
          remove_unused (nms,tps) 0 (fgnms,fgcon) t1 in
        assert (not (is_all_quantified t1));
        Array.length nms, (nms,tps), (fgnms,fgcon), t1
    | QExp(n0,(nms,tps),(fgnms,fgcon),t0,false) ->
        assert ((fgnms,fgcon) = empty_formals);
        0, empty_formals, empty_formals,
        QExp(n0, (nms,tps), (fgnms,fgcon), prenex t0 nb nb2 imp_id, false)
    | Flow(ctrl,args) ->
        0, empty_formals, empty_formals,
        Flow(ctrl, norm_args args nb nb2)
    | Indset (nme,tp,rs) ->
        let rs = norm_args rs (1+nb) nb2 in
        0, empty_formals, empty_formals , Indset (nme,tp,rs)







  let closure_rule (i:int) (p:term) (p_rep:term): term =
    assert (0 <= i);
    match p with
      Indset(n,nms,rs) ->
        if Array.length rs <= i then invalid_arg "Rule index out of bound";
        apply rs.(i) [|p_rep|]
    | _ ->
        invalid_arg "Not an inductive set"




  let induction_rule (imp_id:int) (i:int) (p:term) (pr:term) (q:term)
      : int * formals * term list * term =
    (* Calculate the induction rule [i] for the inductively defined set [p]
       represented by [pr].

       The closure rule [i] is

           all(x,y,...)   c1 ==> c2  ==> ...  ==> p(e)

           where each ci has the form
                all(...) di ==> p(ei)
           or degenerate without quantifier and premises

       The induction rule [i] is

           all(x,y,...)   c1(p) ==> c1(q) ==>
                          c2(p) ==> c2(q) ==>
                          ...
                          p(e)  ==> q(e)

       The function returs the formal arguments, the list of premises and the
       target.
     *)
    let pair (n:int) (t:term): term * term =
      subst_from t n 0 [|pr|],
      subst_from t n 0 [|q |]
    in
    match p with
      Indset (nme,tp,rs) ->
        let nrules = Array.length rs in
        assert (i < nrules);
        let n,fargs,ps_rev,tgt = split_general_implication_chain rs.(i) (imp_id+1) in
        let last,tgt = pair n tgt in
        let ps = List.fold_left
            (fun ps t ->
              try
                let t1,t2 = pair n t in
                t1 :: t2 :: ps
              with Not_found ->
                let t = down_from 1 n t in
                t :: ps)
            [last]
            ps_rev
        in
        n,fargs,ps,tgt
    | _ ->
        invalid_arg "Not an inductive set"



  let induction_law
      (imp_id:int) (p:term) (pr:term) (el_tp:type_term) (set_tp:type_term)
      : term =
    (* Calculate the induction law for the inductively defined set [p] represented
       by [pr]

       all(q,a) ind1 ==> ... ==> indn ==> p(a) ==> q(a)

     *)
    let imp_id = imp_id + 2
    and p      = up 2 p
    and pr     = up 2 pr (* space for a and q *)
    in
    match p with
      Indset (nme,tp,rs) ->
        let nrules = Array.length rs in
        let rule i =
          let n,fargs,ps,tgt = induction_rule imp_id i p pr (Variable 0) in
          let chn = make_implication_chain (List.rev ps) tgt (imp_id+n) in
          all_quantified n fargs empty_formals chn in
        let pa = Application (pr,[|Variable 1|],true)
        and qa = Application (Variable 0, [|Variable 1|],true) in
        let tgt = binary imp_id pa qa in
        let tgt =
          interval_fold
            (fun tgt j ->
              let i = nrules - j - 1 in
              let indi = rule i in
              binary imp_id indi tgt)
            tgt
            0 nrules in
        let nms = [|ST.symbol "q";ST.symbol "a"|]
        and tps = [|set_tp; el_tp|] in
        all_quantified 2 (nms,tps) empty_formals tgt
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
    let args = Array.make nargs empty_term in
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
