(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Signature
open Printf


type definition = term

type formal     = int * term

type base_descriptor = {
    mutable spec:       Feature.Spec.t;
    mutable is_inh:     bool;
    mutable seed:       int;
    mutable variants:   int IntMap.t;  (* cls -> fidx *)
    mutable is_eq:      bool (* is equality inherited from ANY *)
  }

type descriptor = {
    mutable mdl: int;             (* -1: base feature, module not yet assigned*)
    mutable cls: int;             (* owner class *)
    anchor_cls:  int;
    anchor_fg:   int;
    fname:       feature_name;
    impl:        Feature.implementation;
    tvs:         Tvars.t;         (* only formal generics *)
    mutable anchored: int array;  (* formal generics anchored to the owner class *)
    argnames:    int array;
    sign:        Sign.t;
    mutable tp:  type_term;
    priv:        base_descriptor;
    mutable pub: base_descriptor option;
  }

type t = {
    mutable map: int Term_table.t ref Feature_map.t;
    seq:         descriptor seq;
    mutable base:int list ref IntMap.t; (* module name -> list of features *)
    ct:          Class_table.t;
    verbosity:   int
  }


let implication_index: int =  0
let false_index:       int =  1
let true_index:        int =  2
let not_index:         int =  3
let and_index:         int =  4
let or_index:          int =  5
let eq_index:          int =  6
let in_index:          int =  7
let domain_index:      int =  8
let tuple_index:       int =  9
let first_index:       int = 10
let second_index:      int = 11


let empty (verbosity:int): t =
  {map  = Feature_map.empty;
   seq  = Seq.empty ();
   base = IntMap.empty;
   ct   = Class_table.base_table ();
   verbosity = verbosity}


let class_table (ft:t):  Class_table.t   = ft.ct
let module_table (ft:t): Module_table.t = Class_table.module_table ft.ct

let is_private (ft:t): bool = Class_table.is_private ft.ct
let is_public  (ft:t): bool = Class_table.is_public  ft.ct
let is_interface_check  (ft:t): bool = Class_table.is_interface_check ft.ct
let is_interface_use (ft:t): bool = Class_table.is_interface_use ft.ct


let count (ft:t): int =
  Seq.count ft.seq


let verbosity (ft:t): int = ft.verbosity

let descriptor (i:int) (ft:t): descriptor =
  assert (i < count ft);
  Seq.elem i ft.seq


let base_descriptor_priv (i:int) (ft:t): base_descriptor =
  assert (i < count ft);
  let desc = descriptor i ft in
  desc.priv



let signature (i:int) (ft:t): Tvars.t * Sign.t =
  let desc = descriptor i ft in
  desc.tvs, desc.sign


let argument_names (i:int) (ft:t): int array =
  (descriptor i ft).argnames

let class_of_feature (i:int) (ft:t): int =
  (descriptor i ft).cls


let arity (i:int) (ft:t): int =
  Sign.arity (descriptor i ft).sign


let is_higher_order (i:int) (ft:t): bool =
  let desc = descriptor i ft in
  assert (Sign.has_result desc.sign);
  let ntvs = Tvars.count_all desc.tvs in
  let cls,_ = Class_table.split_type_term (Sign.result desc.sign) in
  assert (ntvs <= cls);
  let cls = cls - ntvs in
  cls = Class_table.predicate_index || cls = Class_table.function_index


let tuple_arity (i:int) (ft:t): int =
  assert (is_higher_order i ft);
  let desc = descriptor i ft in
  assert (Sign.has_result desc.sign);
  let ntvs = Tvars.count_all desc.tvs in
  let _,args = Class_table.split_type_term (Sign.result desc.sign) in
  assert (Array.length args = 1);
  let args = Class_table.extract_from_tuple_max ntvs args.(0) in
  Array.length args



let string_of_signature (i:int) (ft:t): string =
  let desc = descriptor i ft in
  (feature_name_to_string desc.fname) ^ " " ^
  (Class_table.string_of_complete_signature desc.sign desc.tvs ft.ct)


let is_feature_public (i:int) (ft:t): bool =
  assert (i < count ft);
  Option.has (descriptor i ft).pub


let feature_name (i:int) (ft:t): string =
  let desc = descriptor i ft in
  feature_name_to_string desc.fname


let base_descriptor (i:int) (ft:t): base_descriptor =
  assert (i < count ft);
  let desc = descriptor i ft in
  if is_private ft then
    desc.priv
  else
    match desc.pub with
      None ->
        printf "feature %d \"%s\" is not public\n" i (string_of_signature i ft);
        assert false (* cannot happen in public view *)
    | Some bdesc -> bdesc



let is_constructor (i:int) (ft:t): bool =
  assert (i < count ft);
  let desc = descriptor i ft in
  assert (desc.cls <> -1);
  IntSet.mem i (Class_table.constructors desc.cls ft.ct)



let inductive_arguments (i:int) (ft:t): int list =
  assert (is_constructor i ft);
  let desc = descriptor i ft in
  let ntvs = Tvars.count_all desc.tvs in
  let lst = interval_fold
      (fun lst i ->
        match Sign.arg_type i desc.sign with
          Variable cls when cls = desc.cls + ntvs ->
            i :: lst
        | VAppl(cls,_) when cls = desc.cls + ntvs ->
            i :: lst
        | _ ->
            lst)
      []
      0 (Sign.arity desc.sign) in
  List.rev lst



let constructor_rule (idx:int) (p:term) (nb:int) (ft:t) :term =
  assert false




let is_term_public (t:term) (nbenv:int) (ft:t): bool =
  let rec check_pub t nb =
    let check_pub_i i =
      let i = i - nb in
      assert (i < count ft);
      if not (is_feature_public i ft) then
        raise Not_found
      else
        ()
    and check_args args nb = Array.iter (fun t -> check_pub t nb) args
    and check_lst  lst nb  = List.iter  (fun t -> check_pub t nb) lst
    in
    match t with
      Variable i when i < nb ->
        ()
    | Variable i ->
        check_pub_i i
    | VAppl(i,args) ->
        check_pub_i i;
        check_args args nb
    | Application(f,args,_) ->
        check_pub f nb;
        check_args args nb
    | Lam(n,nms,pres0,t0,_) ->
        check_lst pres0 (1+nb);
        check_pub t0 (1+nb)
    | QExp(n,nms,t0,_) ->
        check_pub t0 (n+nb)
    | Flow (ctrl,args) ->
        check_args args nb
    | Indset (n,nms,rs) ->
        check_args rs (n+nb)
  in
  try
    check_pub t nbenv;
    true
  with Not_found ->
    false



(* removal of tuple accessors:
   We have to find pattern of the form

      0.second.second...second.first
      0.second.second...second.second

   where the sequence of second is less or equal [nargs-2].

   Example: nargs = 3

   [a,b,c]  ~> [0.first, 0.second.first, 0.second.second]

   There might be subexpressions of the following form in the original term:

      a.first   ~>   0.first.first
      a.second  ~>   0.first.second
      b.first   ~>   0.second.first.first
      b.second  ~>   0.second.first.second
      c.first   ~>   0.second.second.first
      c.second  ~>   0.second.second.second

   There is no ambiguity because none of these expressions fits the pattern of
   at most [nargs-2] seconds and a first or second as the outer function.
 *)



let remove_tuple_accessors (t:term) (nargs:int) (nbenv:int) (ft:t): term =
  (* Convert the inner term [t] which expects an [nargs] tuple back into its
     original form expecting [nargs] arguments.

     The function has to find subterms of the form
        0.second...first
        0.second...second
     where
        .second..
     is is zero up to [nargs-2] applications of [second] and replace them by
     the corresponding argument.  *)
  let rec untup (t:term) (nb:int) (outer:int) (nsnds:int) : term * int * int =
    (* outer 0: neither first nor second
             1: first
             2: second *)
    let first_id  = nb + 1 + nbenv + first_index
    and second_id = nb + 1 + nbenv + second_index
    and vappl i t   = VAppl (i + nargs - 1 , [|t|]), 0, 0
    in
    match t with
      Variable i when i < nb ->
        t, 0, 0
    | Variable i when i = nb ->
        assert (0 < outer);
        let nsnds2 = if nsnds <= nargs - 2 then nsnds else nargs - 2 in
        Variable (i + nsnds2 + outer - 1),
        outer,
        nsnds2
    | Variable i ->
        Variable (i + nargs - 1), 0 , 0
    | VAppl(i,args) when i = first_id ->
        assert (Array.length args = 1);
        let t,outer,nsnds = untup args.(0) nb 1 0 in
        assert (outer = 0 || outer = 1);
        assert (nsnds = 0);
        if outer = 1 then
          t, 0, 0
        else
          vappl i t
    | VAppl(i,args) when i = second_id && outer = 0 ->
        assert (Array.length args = 1);
        let t,outer,nsnds = untup args.(0) nb 2 0 in
        assert (outer = 0 || outer = 2);
        assert (nsnds = 0);
        if outer = 2 then
          t, 0, 0
        else
          vappl i t
    | VAppl(i,args) when i = second_id->
        assert (Array.length args = 1);
        assert (outer = 1 || outer = 2);
        let t1,outer1,nsnds1 = untup args.(0) nb outer (nsnds+1) in
        if outer1 = 0 || nsnds1 = 0 then
          vappl i t1
        else begin
          assert (outer1 = outer);
          t1, outer1, nsnds1-1
        end
    | VAppl(i,args) ->
        let args = Array.map (fun t -> untup0 t nb) args in
        VAppl(i + nargs - 1,args), 0, 0
    | Application(f,args,pr) ->
        let f = untup0 f nb
        and args = Array.map (fun t -> untup0 t nb) args in
        Application(f,args,pr), 0, 0
    | Lam (n,nms,pres0,t0,pr) ->
        let t0 = untup0 t0 (1+nb)
        and pres0 = untup0_lst pres0 (1+nb) in
        Lam(n,nms,pres0,t0,pr), 0, 0
    | QExp (n,nms,t0,is_all) ->
        let t0 = untup0 t0 (n+nb) in
        QExp(n,nms,t0,is_all), 0, 0
    | Flow (ctrl,args) ->
        Flow (ctrl, Array.map (fun t -> untup0 t nb) args), 0, 0
    | Indset (n,nms,rs) ->
        let rs = Array.map (fun r -> untup0 r (n+nb)) rs in
        Indset (n,nms,rs), 0, 0
  and untup0 t nb =
    let t,_,_ = untup t nb 0 0 in t
  and untup0_lst lst nb =
    List.map (fun t -> untup0 t nb) lst
  in
  if nargs <= 1 then
      t
  else
    untup0 t 0



let beta_reduce_0
    (tlam: term) (nbenv:int) (arg:term) (ndelta:int) (ft:t): term =
  (* Beta reduce the term [tlam] which comes from an environment with [nbenv+1]
     variables where variable 0 is the argument variable. [arg] is the argument
     which is an optional tuple and comes from an environment with [nbenv+ndelta]
     variables. All possible transformations of the form [(a,b).first ~> a] and
     [(a,b).second ~> b] are done.

     The reduced term is in an environment with [nbenv+ndelta] variables. *)
  assert (ndelta = 0);
  let rec reduce (t:term) (nb:int): term =
    let first_id  = nb + 1 + nbenv + first_index
    and second_id = nb + 1 + nbenv + second_index
    and tuple_id  = nb + nbenv + ndelta + tuple_index
    in
    let reduce_args args = Array.map (fun a -> reduce a nb) args
    in
    let reduce_tuple arg fstsnd_id fstsnd =
      assert (fstsnd = 0 || fstsnd = 1);
      let tup = reduce arg nb in
      match tup with
        VAppl (i,args) when i = tuple_id ->
          assert (Array.length args = 2);
          args.(fstsnd)
      | _ ->
          VAppl (fstsnd_id - 1 + ndelta, [|tup|])
    in
    match t with
      Variable i when i < nb ->
        t
    | Variable i when i = nb ->
        Term.up nb arg
    | Variable i ->
        Variable (i - 1 + ndelta)
    | VAppl (i,args) when i = first_id ->
        assert (Array.length args = 1);
        reduce_tuple args.(0) i 0
    | VAppl (i,args) when i = second_id ->
        assert (Array.length args = 1);
        reduce_tuple args.(0) i 1
    | VAppl (i,args) ->
        let args = reduce_args args in
        VAppl (i - 1 + ndelta, args)
    | Application(f,args,pr) ->
        let f    = reduce f nb
        and args = reduce_args args in
        Application(f,args,pr)
    | Lam(n,nms,pres0,t0,pr) ->
        Lam(n, nms, pres0, reduce t0 (1+nb), pr)
    | QExp(n,nms,t0,is_all) ->
        QExp(n, nms, reduce t0 (n + nb), is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, reduce_args args)
    | Indset (n,nms,rs) ->
        assert false (* nyi *)
  in
  reduce tlam 0



let args_of_tuple (t:term) (nbenv:int) (ft:t): term array =
  (* The tuple (a,b,...) transformed into an argument array [a,b,...].
   *)
  let tuple_id  = nbenv + tuple_index in
  let rec collect t lst =
    match t with
      VAppl (i,args) when i = tuple_id ->
        assert (Array.length args = 2);
        let lst = args.(0) :: lst in
        collect args.(1) lst
    | _ ->
        t :: lst
  in
  let lst = collect t [] in
  Array.of_list (List.rev lst)




let args_of_tuple_ext (t:term) (nbenv:int) (nargs:int) (ft:t): term array =
  (* The tuple (a,b,...) transformed into an argument array [a,b,...].
     If the tuple [t] is only an n-tuple and [m] arguments are needed with
     [n < m] the last tuple element [l] is used to generated the missing
     elements as

         l.first,  l.second.first, l.second...first, l.second...second
   *)
  assert (0 < nargs);
  let first_id  = nbenv + first_index
  and second_id = nbenv + second_index
  and tuple_id  = nbenv + tuple_index
  in
  let rec untup (t:term) (n:int) (lst:term list): int * term list =
    assert (n < nargs);
    if n + 1 = nargs then
      n + 1, t::lst
    else
      match t with
        VAppl(i,args) when i = tuple_id ->
          assert (Array.length args = 2);
          untup args.(1) (n+1) (args.(0)::lst)
      | _ ->
          n + 1, t::lst
  in
  let rec argument (i:int) (n:int) (t:term): term =
    assert (0 <= i);
    assert (i < n);
    assert (2 <= n);
    if i = 0 then
      VAppl (first_id, [|t|])
    else if i = 1 && n = 2 then
      VAppl (second_id, [|t|])
    else
      let t = VAppl(second_id, [|t|]) in
      argument (i-1) (n-1) t
  in
  let n, lst = untup t 0 [] in
  let lst =
    if n < nargs then begin
      match lst with
        [] ->
          assert false
      | h::tail ->
          let delta = nargs - n + 1 in
          let rec add_args_from i lst =
            if i = delta then
              lst
            else
              add_args_from (i + 1) ((argument i delta h) :: lst)
          in
          add_args_from 0 tail
    end else
      lst
  in
  assert (List.length lst = nargs);
  Array.of_list (List.rev lst)




let tuple_of_args (args:term array) (nbenv:int) (ft:t): term =
  (* The arguments [a,b,...] transformed to a tuple (a,b,...).
   *)
  let tup_id    = nbenv + tuple_index
  and nargs     = Array.length args in
  assert (0 < nargs);
  let rec to_tup (i:int) (t:term): term =
    if i = 0 then
      t
    else
      let i = i - 1 in
      let t = VAppl(tup_id, [|args.(i);t|]) in
      to_tup i t
  in
  let i = nargs - 1 in
  let t = args.(i) in
  let res = to_tup i t in
  assert (args = args_of_tuple_ext res nbenv nargs ft);
  assert (args = args_of_tuple res nbenv ft);
  res




let add_tuple_accessors (t:term) (nargs:int) (nbenv:int) (ft:t): term =
  (* Convert the inner term [t] which has [nargs] arguments to a term with one
     argument expecting an [nargs] tuple.

     nargs = 4
     args: [0.first, 0.second.first, 0.second.second.first, 0.second.second.second]
   *)
  if nargs <= 1 then
    t
  else
    let args = args_of_tuple_ext (Variable 0) (nbenv+1) nargs ft in
    Term.sub t args 1



let make_lambda
    (n:int) (nms:int array) (pres:term list) (t:term) (pr:bool) (nbenv:int) (ft:t)
    : term =
  assert (0 < n);
  assert (Array.length nms = 0 || Array.length nms = n);
  let add_tup t = add_tuple_accessors t n nbenv ft in
  let t0 = add_tup t
  and pres0 = List.map add_tup pres in
  Lam(n,nms,pres0,t0,pr)



let make_application
    (f:term) (args:term array) (pred:bool) (nbenv:int) (ft:t): term =
  assert (Array.length args > 0);
  let args =
    if Array.length args = 1 then
      args
    else
      [|tuple_of_args args nbenv ft|]
  in
  Application (f, args, pred)



let beta_reduce (n:int) (tlam: term) (args:term array) (nbenv:int) (ft:t): term =
  assert (0 < Array.length args);
  assert (Array.length args <= n);
  assert (Array.length args = 1);
  let t0   = remove_tuple_accessors tlam n nbenv ft in
  let args = args_of_tuple_ext args.(0) nbenv n ft in
  Term.apply t0 args


let adapt_names (nms:int array) (names:int array): int array =
  let nms  = Array.copy nms in
  let nnms = Array.length nms in
  let patch i =
    assert (i < nnms);
    let str = "$" ^ (ST.string nms.(i)) in
    nms.(i) <- ST.symbol str
  and has i =
    assert (i < nnms);
    try
      let _ = Search.array_find_min (fun nme -> nme = nms.(i)) names in
      true
    with Not_found ->
      false
  in
  let rec patch_until_ok i =
    if has i then begin
      patch i;
      patch_until_ok i
    end
  in
  for i = 0 to nnms - 1 do
    patch_until_ok i
  done;
  nms


let term_to_string
    (t:term)
    (norm:bool)
    (nanon: int)
    (names: int array)
    (ft:t)
    : string =
  (** Convert the term [t] in an environment with the named variables [names]
      to a string.
   *)
  let anon_symbol (i:int) (nanon:int): int =
      ST.symbol ("$" ^ (string_of_int (nanon+i)))
  in
  let rec to_string
      (t:term)
      (names: int array)
      (nanonused: int)
      (is_fun: bool)
      (outop: (operator*bool) option)
      : string =
    (* nanonused: number of already used anonymous variables
       is_fun: the term is used in a function position
       outop: the optional outer operator and a flag if the current term
              is the left operand of the outer operator
     *)
    let nnames = Array.length names
    and anon2sym (i:int): int = anon_symbol i nanonused
    in
    let find_op_int (i:int): operator * int=
      if nnames <= i then
        let idx = i - nnames in
        match (Seq.elem idx ft.seq).fname with
          FNoperator op -> op, idx
        | _ -> raise Not_found
      else
        raise Not_found
    in
    let var2str (i:int): string =
      if i < nnames then
        ST.string names.(i)
      else
        feature_name_to_string
          (Seq.elem (i-nnames) ft.seq).fname
    and find_op (f:term): operator * int =
      match f with
        Variable i -> find_op_int i
      | _ -> raise Not_found
    and args2str (n:int) (nms:int array): string =
      let nnms  = Array.length nms in
      assert (nnms = n);
      let argsstr = Array.init n (fun i -> ST.string nms.(i)) in
      String.concat "," (Array.to_list argsstr)
    in
    let local_names (n:int) (nms:int array): int * int array =
      let nnms  = Array.length nms in
      if n = nnms then
        nanonused, nms
      else
        nanonused+n, Array.init n anon2sym
    in
    let lam_strs (n:int) (nms:int array) (ps:term list) (t:term)
        : string * string *string =
      let nanonused, nms = local_names n nms in
      let names = Array.append nms names in
      args2str n nms,
      String.concat ";"
        (List.map (fun t -> to_string t names nanonused false None) ps),
      to_string t names nanonused false None
    in
    let default_fapp (f:term) (argsstr:string): operator option * string =
      None,
      (to_string f names nanonused true None) ^ "(" ^ argsstr ^ ")"
    in
    let funiapp2str (i:int) (argsstr:string): operator option * string =
      if nnames <= i then
        let fn = (descriptor (i-nnames) ft).fname in
        begin match fn with
          FNname fsym ->
            if fsym = (ST.symbol "singleton") then
              None, "{" ^ argsstr ^ "}"
            else if fsym = ST.tuple then
              Some Commaop, argsstr
            else
              default_fapp (Variable i) argsstr
        | _ -> default_fapp (Variable i) argsstr
        end
      else
        default_fapp (Variable i) argsstr
    in
    let funapp2str (f:term) (argsstr:string): operator option * string =
      match f with
        Variable i ->
          funiapp2str i argsstr
      | _ -> default_fapp f argsstr
    in
    let argsstr (args: term array): string =
      String.concat
        ","
        (List.map
           (fun t -> to_string t names nanonused false None)
           (Array.to_list args))
    in
    let op2str (op:operator) (fidx:int) (args: term array): string =
      match op with
        Allop | Someop | Asop -> assert false (* cannot happen *)
      | _ ->
          let nargs = Array.length args in
          if nargs = 1 && arity fidx ft = 0 then begin
            assert (is_higher_order fidx ft);
            let nargs_tup = tuple_arity fidx ft in
            assert (1 <= nargs_tup);
            if nargs_tup = 1 then
              "(" ^ (operator_to_rawstring op) ^ ")"
              ^ (to_string args.(0) names nanonused false (Some (op,false)))
            else
              let args = args_of_tuple_ext args.(0) nnames 2 ft in
              (to_string args.(0) names nanonused false (Some (op,true)))
              ^ " " ^ (operator_to_rawstring op) ^ " "
              ^ (to_string args.(1) names nanonused false (Some (op,false)))
          end else if nargs = 1 then
            (operator_to_rawstring op) ^ " "
            ^ (to_string args.(0) names nanonused false (Some (op,false)))
          else begin
            assert (nargs=2); (* only unary and binary operators *)
            (to_string args.(0) names nanonused false (Some (op,true)))
            ^ " " ^ (operator_to_rawstring op) ^ " "
            ^ (to_string args.(1) names nanonused false (Some (op,false)))
          end
    and lam2str (n:int) (nms: int array) (pres:term list) (t:term) (pr:bool)
        : string =
      let argsstr, presstr, tstr = lam_strs n nms pres t in
      if pr then
        "{" ^ argsstr ^ ": " ^ tstr ^ "}"
      else
        match pres with
          [] -> "((" ^ argsstr ^ ") -> " ^ tstr ^ ")"
        | _ -> "agent (" ^ argsstr ^ ") require " ^
            presstr ^
            " ensure Result = " ^ tstr ^ " end"
    and if2str (args:term array): string =
      let len = Array.length args in
      assert(2 <= len); assert (len <= 3);
      let to_str t = to_string t names nanonused false None in
      let cond_exp (c:term) (e:term) (isif:bool): string =
        (if isif then "if " else " elseif ") ^ (to_str c) ^ " then " ^ (to_str e)
      in
      let rec ifrest (t:term): string =
        match t with
          Flow (Ifexp,args) -> ifargs args false
        | _                 -> " else " ^ (to_str t)
      and ifargs (args: term array) (is_outer:bool): string =
        let len = Array.length args in
        assert(2 <= len); assert (len <= 3);
        (cond_exp args.(0) args.(1) true) ^
        (if len = 2 then "" else ifrest args.(2)) ^
        (if is_outer then " end" else "")
      in
      ifargs args true
    and insp2str (args:term array): string =
      let len = Array.length args in
      assert (len mod 2 = 1);
      assert (3 <= len);
      let ncases = len / 2 in
      let case (i:int): string =
        let n, nms, mtch, res = Term.case_split args.(2*i+1) args.(2*i+2) in
        let names1 = Array.append nms names in
        let to_str t = to_string t names1 nanonused false None in
        " case " ^ (to_str mtch) ^ " then " ^ (to_str res)
      in
      let rec cases_from (i:int) (str:string): string =
        if i = ncases then
          str
        else
          (cases_from (1+i) (str ^ (case i))) in
      let to_str t = to_string t names nanonused false None in
      "inspect "  ^  (to_str args.(0)) ^ (cases_from 0 "") ^ " end"
    and as2str (args:term array): string =
      let len = Array.length args in
      assert (len = 2);
      let str1 = to_string args.(0) names nanonused false (Some (Asop,true)) in
      let str2 =
        let n,nms,mtch = Term.pattern_split args.(1) in
        let names1 = Array.append nms names in
        to_string mtch names1 nanonused false (Some (Asop,false)) in
      str1 ^ " as " ^ str2
    in
    let inop, str =
      match t with
        Variable i ->
          None, var2str i
      | VAppl (i,args) ->
          begin try
            let op,fidx = find_op_int i in
            Some op, op2str op fidx args
          with Not_found ->
            funiapp2str i (argsstr args)
          end
      | Application (f,args,pr) ->
          begin
            try
              let op,fidx = find_op f in
              Some op, op2str op fidx args
            with Not_found ->
              funapp2str f (argsstr args)
          end
      | Lam (n,nms,pres,t,pr) ->
          let nms = adapt_names nms names in
          let nbenv = Array.length names in
          let remove_tup t = remove_tuple_accessors t n nbenv ft in
          let pres, t =
            if norm then
              List.map remove_tup pres,
              remove_tup t
            else
              pres,t in
          None, lam2str n nms pres t pr
      | QExp (n,nms,t,is_all) ->
          let nms = adapt_names nms names in
          let op, opstr  = if is_all then Allop, "all"  else Someop, "some"
          and argsstr, _, tstr = lam_strs n nms [] t in
          Some op, opstr ^ "(" ^ argsstr ^ ") " ^ tstr
      | Flow (ctrl,args) ->
          begin
            match ctrl with
              Ifexp   -> None, if2str args
            | Inspect -> None, insp2str args
            | Asexp   -> Some(Asop), as2str args
          end
      | Indset (n,nms,rs) ->
          let argsstr = args2str n nms in
          let nms = adapt_names nms names in
          let nanonused, nms = local_names n nms in
          let names = Array.append nms names in
          let rsstrs = List.map (fun t -> to_string t names nanonused false None)
              (Array.to_list rs) in
          let rsstr = String.concat "," rsstrs in
          let str = "{(" ^ argsstr ^ "):"
            ^  rsstr ^ "}" in
          None, str
    in
    match inop, outop with
      Some iop, Some (oop,is_left) ->
        let _,iprec,iassoc = operator_data iop
        and _,oprec,oassoc = operator_data oop
        in
        let paren1 = iprec < oprec
        and paren2 = (iop = oop) &&
          match oassoc with
            Left     -> not is_left
          | Right    -> is_left
          | Nonassoc -> true
        and paren3 = (iprec = oprec) && (iop <> oop)
        in
        if  paren1 || paren2 || paren3 then
          "(" ^ str ^ ")"
        else
          str
    | Some iop, None when is_fun ->
        "(" ^ str ^ ")"
    | _ -> str
  in
  let nnames = Array.length names in
  let names = Array.init (nnames + nanon)
      (fun i ->
        if i<nanon then anon_symbol i 0
        else names.(i-nanon))
  in
  to_string t names nanon false None


let string_of_term_anon (t:term) (nb:int) (ft:t): string =
  term_to_string t true nb [||] ft




let normalize_lambdas (t:term) (nb:int) (ft:t): term =
  let rec norm t nb =
    let norm_args args nb = Array.map (fun a -> norm a nb) args
    in
    match t with
      Variable i ->
        t
    | VAppl (i,args) ->
        let args = norm_args args nb in
        if i = in_index + nb then begin
          assert (Array.length args = 2);
          Application(args.(1), [|args.(0)|],true)
        end else
          VAppl (i, args)
    | Application (f,args,pr) ->
        let f    = norm f nb
        and args = norm_args args nb in
        make_application f args pr nb ft
    | Lam (n,nms,pres,t,pr) ->
        let pres = List.map (fun p -> norm p (n+nb)) pres
        and t = norm t (n+nb) in
        make_lambda n nms pres t pr nb ft
    | QExp (n,nms,t,is_all) ->
        QExp (n, nms, norm t (n+nb), is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, norm_args args nb)
    | Indset (n,nms,rs) ->
        Indset (n,nms, norm_args rs (n+nb))
  in
  norm t nb


let prepend_names (nms:int array) (names:int array): int array =
  let nms = adapt_names nms names in
  Array.append nms names


let prenex (t:term) (nb:int) (ft:t): term =
  (* Calculate the prenex normal form of the term [t] with respect to
     universal quantifiers. All universal quantifiers are bubbled up in
     implication chains and merged with the upper universal quantifier. Unused
     variables in universally quantified expressions are eliminated.  *)
  let rec norm (t:term) (nb:int): term =
    let n,nms,t = norm0 t nb in
    Term.all_quantified n nms t
  and norm_args (args:term array) (nb:int): term array =
    Array.map (fun t -> norm t nb) args
  and norm_lst  (lst: term list) (nb:int): term list =
    List.map (fun t -> norm t nb) lst
  and norm0 (t:term) (nb:int): int * int array * term =
    match t with
      Variable i -> 0, [||], t
    | VAppl(i,args) when i = nb + implication_index ->
        assert (Array.length args = 2);
        let a = norm args.(0) nb
        and n,nms,b1 = norm0 args.(1) nb in
        let b1 =
          let args = Array.init (n+nb)
              (fun i ->
                if i < n then Variable (nb+i)
                else Variable (i-n)) in
          Term.sub b1 args (n+nb)
        in
        let a1 = Term.upbound n nb a in
        let t = VAppl(i+n,[|a1;b1|]) in
        n, nms, t
    | VAppl(i,args) ->
        0, [||], VAppl(i, norm_args args nb)
    | Application(f,args,pr) ->
        let f = norm f nb
        and args = norm_args args nb in
        0, [||], Application(f,args,pr)
    | Lam(n,nms,ps,t0,pr) ->
        let ps = norm_lst ps (1+nb)
        and t0 = norm t0 (1+nb) in
        0, [||], Lam(n,nms,ps,t0,pr)
    | QExp(n0,nms0,t0,is_all) ->
        if is_all then
          let n1,nms1,t1 = norm0 t0 (n0+nb) in
          let nms = prepend_names nms0 nms1 in
          let t2, n2, nms2 =
            let usd = Array.of_list (List.rev (Term.used_variables t1 (n0+n1))) in
            let n   = Array.length usd in
            assert (is_all || n = n0 + n1);
            let args = Array.make (n0+n1) (Variable (-1))
            and nms2 = Array.make n (-1) in
            for i = 0 to n-1 do
              nms2.(i) <- nms.(usd.(i));
              args.(usd.(i)) <- (Variable i)
            done;
            Term.sub t1 args n, n, nms2
          in
          n2, nms2, t2
        else
          0, [||], QExp(n0, nms0, norm t0 (n0+nb), is_all)
    | Flow(ctrl,args) ->
        0, [||], Flow(ctrl, norm_args args nb)
    | Indset (n,nms,rs) ->
        0, [||], Indset (n,nms, norm_args rs (n+nb))
  in
  norm t nb



let definition (i:int) (nb:int) (ft:t): int * int array * term =
  assert (nb <= i);
  assert (i  <= nb + count ft);
  let i = i - nb in
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  let nargs = Sign.arity desc.sign in
  let t = Feature.Spec.definition_term bdesc.spec in
  let t = Term.upbound nb nargs t in
  nargs, desc.argnames, t


let has_definition (i:int) (ft:t): bool =
  try let _ = definition i 0 ft in true
  with Not_found -> false



let is_inductive_set (i:int) (nb:int) (ft:t): bool =
  try
    let n,nms,t = definition i nb ft in
    begin
      match t with
        Indset _ -> true
      | _        -> false
    end
  with Not_found ->
    false


let inductive_set (i:int) (args:term array) (nb:int) (ft:t): term =
  let n,nms,t = definition i nb ft in
  match t with
    Indset _ ->
      assert (n = Array.length args);
      Term.apply t args
  | _ ->
      raise Not_found


let preconditions (i:int) (nb:int) (ft:t): int * int array * term list =
  (* The preconditions (if there are some) of the feature [i] as optional number of
     arguments and a list of expressions transformed into an environment with [nb]
     bound variables.*)
  assert (nb <= i);
  let i = i - nb in
  let desc = descriptor i ft in
  let spec = (base_descriptor i ft).spec in
  let n = arity i ft in
  if Feature.Spec.has_preconditions spec then
    let lst = Feature.Spec.preconditions spec in
    let lst = List.map (fun t -> Term.upbound nb n t) lst in
    n, desc.argnames, lst
  else
    n, desc.argnames, []



let postconditions (i:int) (nb:int) (ft:t): int * int array * term list =
  assert (nb <= i);
  let i = i - nb in
  let desc = descriptor i ft in
  let spec = (base_descriptor i ft).spec in
  let n = arity i ft in
  let lst = Feature.Spec.postconditions spec in
  let lst = List.map (fun t -> Term.upbound nb n t) lst in
  n, desc.argnames, lst



let count_postconditions (i:int) (ft:t): int =
  let bdesc = base_descriptor i ft in
  Feature.Spec.count_postconditions bdesc.spec



let function_property
    (i:int) (fidx:int) (nb:int) (args:term array) (ft:t): term =
  assert (nb <= fidx);
  let fidx = fidx - nb in
  let spec = (base_descriptor fidx ft).spec in
  let n = arity fidx ft in
  if n <> Array.length args then invalid_arg "wrong size of arguments";
  if i < 0 || count_postconditions fidx ft <= i then
    invalid_arg "postcondition does not exist";
  let pres  = Feature.Spec.preconditions spec
  and post  = Feature.Spec.postcondition i spec in
  let chn =
    Term.make_implication_chain (List.rev pres) post (implication_index + n) in
  Term.sub chn args nb



let domain_of_feature (i:int) (nb:int) (ft:t): term =
  assert (nb <= i);
  assert (arity (i-nb) ft > 0);
  let n,nms,pres = preconditions i nb ft in
  let t =
    match pres with
      [] ->
        Variable (n+nb+true_index)
    | hd::tl ->
        let and_id = n + nb + and_index in
        List.fold_left
          (fun t1 t2 ->
            Term.binary and_id t1 t2)
          hd
          tl in
  make_lambda n nms [] t true nb ft



let private_body (i:int) (ft:t): Feature.body =
  assert (i < count ft);
  let desc = descriptor i ft in
  desc.priv.spec, desc.impl


let body (i:int) (ft:t): Feature.body =
  assert (i < count ft);
  let desc = descriptor i ft
  and bdesc = base_descriptor i ft in
  bdesc.spec, desc.impl


let owner (i:int) (ft:t): int =
  assert (i < count ft);
  (descriptor i ft).cls


let is_ghost_function (i:int) (ft:t): bool =
  assert (i < count ft);
  let desc = descriptor i ft in
  Sign.is_ghost desc.sign


let is_ghost_term (t:term) (nargs:int) (ft:t): bool =
  let rec is_ghost (t:term) (nb:int): bool =
    let rec ghost_args (args:term array) (i:int) (n:int): bool =
      if i = n then false
      else
        let ghost = is_ghost args.(i) nb in
        ghost || ghost_args args (i+1) n
    in
    match t with
      Variable i when i < nb+nargs -> false
    | Variable i ->
        is_ghost_function (i-nb-nargs) ft
    | Lam (n,_,_,t,_) ->
        is_ghost t (1+nb)
    | QExp(_,_,_,_) ->
        true
    | Flow (ctrl, args) ->
        let len = Array.length args in
        begin match ctrl with
          Ifexp ->
            ghost_args args 0 len
        | Asexp ->
            assert (len = 2);
            is_ghost args.(0) nb
        | Inspect ->
            assert (3 <= len);
            assert (len mod 2 = 1);
            let ncases = len / 2 in
            let rec cases_from i ghost =
              if ghost || i = ncases then
                ghost
              else
                let n,_,t   = Term.pattern_split args.(2*i+2) in
                let ghost = is_ghost t (n+nb) in
                cases_from (1+i) ghost
            in
            let ghost = is_ghost args.(0) nb in
            cases_from 0 ghost
        end
    | Indset _ ->
        true
    | VAppl (i,args) ->
        let ghost = is_ghost_function (i-nb-nargs) ft in
        ghost || ghost_args args 0 (Array.length args)
    | Application (f,args,_) ->
        let fghost = is_ghost f nb in
        fghost || ghost_args args 0 (Array.length args)
  in
  is_ghost t 0


let is_ghost_specification (spec:Feature.Spec.t) (ft:t): bool =
  Feature.Spec.has_postconditions spec ||
  (Feature.Spec.has_definition spec &&
   let nargs = Feature.Spec.count_arguments spec in
   is_ghost_term (Feature.Spec.definition_term spec) nargs ft)


let is_total (i:int) (ft:t): bool =
  assert (i < count ft);
  true  (* nyi: features with preconditions *)

let is_predicate (i:int) (ft:t): bool =
  let desc = descriptor i ft in
  let sign = desc.sign
  and tvs  = desc.tvs in
  let nfgs = Tvars.count_all tvs in
  0 < Sign.arity sign &&
  is_total i ft &&
  Sign.has_result sign &&
  let res = Sign.result sign in
  match res with
    Variable i when nfgs <= i ->
      i - nfgs = Class_table.boolean_index
  | _ ->
      false


let standard_bdesc (i:int) (cls:int) (spec: Feature.Spec.t) (nb:int) (ft:t)
    : base_descriptor =
  {is_inh     = false;
   seed       = i;                      (* each feature is its own seed *)
   variants   = IntMap.singleton cls i; (* and own variant in its owner class *)
   spec       = spec;
   is_eq      = (i = eq_index)}


let count_fgs (i:int) (ft:t): int =
  assert (i < count ft);
  Tvars.count_fgs (descriptor i ft).tvs


let anchor (i:int) (ft:t): int =
  let desc = descriptor i ft in
  (*let a = desc.anchor_fg in
  if a = -1 then
    raise Not_found
  else
    a*) (*anchor*)
  if Array.length desc.anchored = 1 then
    desc.anchored.(0)
  else
    raise Not_found


let has_anchor (i:int) (ft:t): bool =
  try let _ = anchor i ft in true
  with Not_found -> false


let seed (i:int) (ft:t): int =
  assert (i < count ft);
  (base_descriptor i ft).seed


let seeded_term (t:term) (nb:int) (ft:t): term =
  let rec seeded t nb =
    let seeded_args args nb = Array.map (fun t -> seeded t nb) args in
    match t with
      Variable i when i < nb -> t
    | Variable i ->
        Variable (nb + seed (i-nb) ft)
    | VAppl(i,args) ->
        assert (nb <= i);
        let i = nb + seed (i-nb) ft
        and args = seeded_args args nb in
        VAppl(i,args)
    | Application(f,args,pr) ->
        let f = seeded f nb
        and args = seeded_args args nb in
        Application(f,args,pr)
    | Lam(n,nms,pres,t0,pr) ->
        let t0 = seeded t0 (1+nb)
        and pres = List.map (fun t -> seeded t (1+nb)) pres in
        Lam(n,nms,pres,t0,pr)
    | QExp(n,nms,t0,is_all) ->
        let t0 = seeded t0 (n+nb) in
        QExp(n,nms,t0,is_all)
    | Flow(ctrl,args) ->
        let args = seeded_args args nb in
        Flow(ctrl,args)
    | Indset (n,nms,rs) ->
        let rs = seeded_args rs (n+nb) in
        Indset (n,nms,rs)
  in
  seeded t nb


let variant (i:int) (cls:int) (ft:t): int =
  (* The variant of the feature [i] in the class [cls] *)
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  let seed_bdesc = base_descriptor bdesc.seed ft
  in
  IntMap.find cls seed_bdesc.variants



let private_variant (i:int) (cls:int) (ft:t): int =
  (* The privat variant of the feature [i] in the class [cls] *)
  assert (i < count ft);
  let bdesc      = base_descriptor_priv i ft in
  let seed_bdesc = base_descriptor_priv bdesc.seed ft in
  IntMap.find cls seed_bdesc.variants


let has_variant (i:int) (cls:int) (ft:t): bool =
  try let _ = variant i cls ft in true
  with Not_found -> false

let has_private_variant (i:int) (cls:int) (ft:t): bool =
  try let _ = private_variant i cls ft in true
  with Not_found -> false




let variant_feature
    (i:int) (nb:int) (ags:type_term array) (tvs:Tvars.t) (ft:t): int =
  assert (i < nb + count ft);
  let idx = i - nb in
  assert (Array.length ags = count_fgs idx ft);
  let nfgs = Array.length ags in
  if nfgs = 0 || nfgs > 1 then
    i
  else begin
    let cls = Tvars.principal_class ags.(0) tvs in
    try
      nb + variant idx cls ft
    with Not_found ->
      i
  end



let variant_postcondition
    (t:term) (i:int) (inew:int) (nb:int) (base_cls:int) (cls:int) (ft:t): term =
  (* The variant of the postcondition term [t] of the feature [i] with [nb]
     bound variables in the class [cls] where all features of [t] from the
     class [base_class] are transformed into their inherited variant in class
     [cls] *)
  assert (Class_table.has_ancestor cls base_cls ft.ct);
  let cnt = count ft in
  let f (j:int): int =
    if inew <> (-1) && j = i then
      cnt
    else if class_of_feature j ft = base_cls && has_anchor j ft then
      try variant j cls ft
      with Not_found ->
        printf "there is no variant of \"%s\" in class %s\n"
          (string_of_signature j ft)
          (Class_table.class_name cls ft.ct);
          assert false (* If [cls] inherits [base_cls] then there has to be a variant
                          in the descendant *)
    else
      j
  in
  Term.map_free f t nb



let variant_term (t:term) (nb:int) (base_cls:int) (cls:int) (ft:t): term =
  (* The variant of the term [t] with [nb] bound variables in the class [cls] where
     all features of [t] from the class [base_class] are transformed into their
         inherited variant in class [cls] *)
  variant_postcondition t (-1) (-1) nb base_cls cls ft



let variant_spec (i:int) (inew:int) (base_cls:int) (cls:int) (ft:t)
    : Feature.Spec.t =
  (* The variant of the specification of the feature [i] in the class [cls] where
     all features of [spec] from the class [base_class] are transformed into their
     inherited variant in class [cls] *)
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  let nargs,nms   = Feature.Spec.names bdesc.spec in
  let pres = List.map
      (fun t -> variant_term t nargs base_cls cls ft)
      (Feature.Spec.preconditions bdesc.spec)
  in
  if Feature.Spec.has_postconditions bdesc.spec then
    let posts =
      List.map
        (fun t -> variant_postcondition t i inew nargs base_cls cls ft)
        (Feature.Spec.postconditions bdesc.spec) in
    Feature.Spec.make_func_spec nms pres posts
  else
    let def = Feature.Spec.definition bdesc.spec in
    match def with
      None -> Feature.Spec.make_func_def nms None pres
    | Some defterm ->
        Feature.Spec.make_func_def
          nms (Some (variant_term defterm nargs base_cls cls ft)) pres


let equality_index (cls:int) (ft:t): int =
  variant eq_index cls ft


let equality_index_of_type (tp:term) (tvs:Tvars.t) (ft:t): int =
  let cls = Tvars.principal_class tp tvs in
  equality_index cls ft



let definition_equality (i:int) (ft:t): term =
  assert (i < count ft);
  assert (has_definition i ft);
  let desc  = descriptor i ft
  and bdesc = base_descriptor i ft in
  assert (Sign.has_result desc.sign);
  let nargs = Sign.arity desc.sign in
  assert (desc.cls <> -1);
  let eq_id = equality_index_of_type (Sign.result desc.sign) desc.tvs ft in
  let eq_id = nargs + eq_id
  and f_id  = nargs + i
  in
  let t = Option.value (Feature.Spec.definition bdesc.spec) in
  let f =
    if nargs = 0 then Variable f_id
    else VAppl (f_id, Array.init nargs (fun i -> Variable i))
  in
  Term.binary eq_id f t



let specification (i:int) (ft:t): term list =
  let desc = descriptor i ft in
  let n, nms,  posts =
    if has_definition i ft then
      Sign.arity desc.sign, desc.argnames, [definition_equality i ft]
    else
      postconditions i 0 ft
  and n2,nms2, pres  = preconditions  i 0 ft in
  let pres_rev = List.rev pres in
  assert (n = n2);
  assert (nms = nms2);
  assert (n = arity i ft);
  let imp_id = n + implication_index in
  List.map
    (fun t ->
      let chn = Term.make_implication_chain pres_rev t imp_id in
      QExp(n,nms,chn,true))
    posts




let is_desc_deferred (desc:descriptor): bool =
  match desc.impl with
    Feature.Deferred -> true
  | _                -> false


let is_deferred (i:int) (ft:t): bool =
  assert (i < count ft);
  is_desc_deferred (descriptor i ft)


let names_of_formals (farr: formal array): int array =
  Array.map (fun (name,_) -> name) farr

let terms_of_formals (farr: formal array): term array =
  Array.map (fun (_,t) -> t) farr



let find_with_signature (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t): int =
  (* Find the feature with the characteristics.  *)
  let ntvs = Tvars.count_all tvs in
  let tp   = Class_table.to_dummy ntvs sign in
  let ntvs = Tvars.count_all tvs
  and tab = Feature_map.find fn ft.map in
  let lst  = Term_table.unify tp ntvs !tab in
  let idx_lst =
    List.fold_left
      (fun lst (i,sub) ->
        let desc = descriptor i ft in
        if Tvars.is_equivalent tvs desc.tvs && Term_sub.is_identity sub then
          i :: lst
        else
          let ok =
            Term_sub.for_all
              (fun j t ->
                Class_table.satisfies
                  t tvs
                  (Tvars.concept j desc.tvs) desc.tvs
                  ft.ct)
              sub
          in
          if ok then begin
            let owner = Class_table.owner tvs sign ft.ct in
            try
              let ivar = variant i owner ft in
              ivar :: lst
            with Not_found ->
              assert false (* cannot happen, feature must be inherited *)
          end else
            lst)
      []
      lst
  in
  match idx_lst with
    [] -> raise Not_found
  | idx::rest ->
      if not (List.for_all (fun i -> i=idx) rest) then begin
        List.iteri
          (fun i idx ->
            printf "%d %d %s\n" i idx (string_of_signature idx ft))
          idx_lst
      end;
      assert (List.for_all (fun i -> i=idx) rest);
      idx


let has_with_signature (fn:feature_name) (tvs: Tvars.t) (sign:Sign.t) (ft:t): bool =
  try
    let _ = find_with_signature fn tvs sign ft in true
  with Not_found -> false





let add_class_feature (i:int) (priv_only:bool) (pub_only:bool) (base:bool) (ft:t)
    : unit =
  (* Add the feature [i] as a class feature to the corresponding owner
     class and to the anchor class. *)
  assert (i < count ft);
  assert (not (priv_only && pub_only));
  let desc  = descriptor i ft in
  let _, anchor = Sign.anchor desc.tvs desc.sign in
  assert (0 <= desc.cls);
  Class_table.add_feature
    i
    desc.cls
    (is_desc_deferred desc)
    priv_only
    pub_only
    base
    ft.ct;
  if anchor <> -1 && anchor <> desc.cls then begin
    (*printf "add feature %s to anchor class %s\n"
      (string_of_signature i ft)
      (Class_table.class_name anchor ft.ct);*)
    Class_table.add_feature
      i
      anchor
      (is_desc_deferred desc)
      priv_only
      pub_only
      base
      ft.ct
  end


let add_key (i:int) (ft:t): unit =
  (** Add the key of the feature [i] to the key table. *)
  assert (i < count ft);
  let desc  = Seq.elem i ft.seq in
  let ntvs  = Tvars.count_all desc.tvs
  in
  desc.tp <- Class_table.to_dummy ntvs desc.sign;
  let tab =
    try Feature_map.find desc.fname ft.map
    with Not_found ->
      let tab = ref Term_table.empty in
      ft.map <- Feature_map.add desc.fname tab ft.map;
      tab
  in
  tab := Term_table.add desc.tp ntvs 0 i !tab




let add_keys (ft:t): unit =
  for i = 0 to (count ft)-1 do
    add_key i ft
  done


let add_feature
    (fn:       feature_name withinfo)
    (tvs:      Tvars.t)
    (argnames: int array)
    (sign:     Sign.t)
    (impl:     Feature.implementation)
    (ft:       t): unit =
  (* Add a new feature to the feature table with an empty specification *)
  assert (not (has_with_signature fn.v tvs sign ft));
  let is_priv = is_private ft
  and cnt     = Seq.count ft.seq
  and nargs   = Array.length argnames
  and spec    = Feature.Spec.make_empty argnames
  in
  let mdl = Class_table.current_module ft.ct in
  let cls = Class_table.owner tvs sign ft.ct
  and anchor_fg, anchor_cls = Sign.anchor tvs sign in
  let anchored = Class_table.anchored tvs cls ft.ct in
  let nanchors = Array.length anchored in
  begin match impl with
    Feature.Deferred ->
      Class_table.check_deferred cls nanchors fn.i ft.ct
  | _ -> ()
  end;
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    if is_priv then None else Some (standard_bdesc cnt cls spec nargs ft)
  and nfgs = Tvars.count_all tvs
  and base = (is_private ft || is_interface_use ft) &&
    not (Feature.Spec.has_definition spec)
  in
  let desc =
    {mdl      = mdl;
     cls      = cls;
     anchor_cls = anchor_cls;
     anchor_fg  = anchor_fg;
     fname    = fn.v;
     impl     = impl;
     tvs      = tvs;
     argnames = argnames;
     sign     = sign;
     tp       = Class_table.to_dummy nfgs sign;
     anchored = anchored;
     priv     = bdesc;
     pub      = bdesc_opt}
  in
  Seq.push desc ft.seq;
  add_key cnt ft;
  add_class_feature cnt false false base ft;
  if ft.verbosity > 1 then
    printf "  new feature %d %s\n" cnt (string_of_signature cnt ft)





let update_specification (i:int) (spec:Feature.Spec.t) (ft:t): unit =
  assert (i < count ft);
  let bdesc = base_descriptor i ft in
  assert (Feature.Spec.is_empty bdesc.spec);
  assert begin
    not (is_interface_check ft) ||
    Feature.Spec.private_public_consistent (base_descriptor_priv i ft).spec spec
  end;
  if is_interface_use ft then
    (base_descriptor_priv i ft).spec <- spec;
  bdesc.spec <- spec



let set_owner_class (idx:int) (cls:int) (ft:t): unit =
  assert (idx < count ft);
  (descriptor idx ft).cls <- cls


let export_feature (i:int) (withspec:bool) (ft:t): unit =
  (* Export the feature [i] unless it is already publicly available. *)
  assert (i < count ft);
  if ft.verbosity > 1 then
    printf "  export feature %d %s\n" i (string_of_signature i ft);
  let desc = descriptor i ft in
  match desc.pub with
    None ->
      let nargs = Array.length desc.argnames in
      let spec  =
        if withspec then desc.priv.spec
        else Feature.Spec.make_func_spec desc.argnames [] []
      in
      desc.pub <- Some (standard_bdesc i desc.cls spec nargs ft);
      add_class_feature i false true false ft;
  | Some _ ->
      ()


(*
let n_names_with_start (c:char) (size:int): int array =
  let code = Char.code c in
  Array.init size (fun i -> ST.symbol (String.make 1 (Char.chr (i + code))))

let standard_fgnames (size:int): int array =
  n_names_with_start 'A' size

let standard_argnames (size:int): int array =
  n_names_with_start 'a' size
*)

let add_base
    (mdl_nme: string)
    (cls: int)
    (fn:feature_name)
    (concepts: type_term array)
    (argtypes: type_term array)
    (res:  type_term)
    (defer: bool)
    (ghost: bool)
    (spec: Feature.Spec.t)
    (ft:t)
    : unit =
  assert (not defer || not (Feature.Spec.has_definition spec));
  let mdl_nme            = ST.symbol mdl_nme
  in
  let sign =
    if ghost then
      Sign.make_ghost argtypes res
    else
      Sign.make_func argtypes res
  and ntvs = Array.length concepts
  and cnt  = count ft
  and nargs = Array.length argtypes
  in
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    match fn with
      FNoperator Allop
    | FNoperator Someop ->
        Some (standard_bdesc cnt cls spec nargs ft)
    | _ -> None
  in
  let tvs = Tvars.make_fgs (standard_fgnames ntvs) concepts in
  let anchored = Class_table.anchored tvs cls ft.ct in
  let anchor_fg, anchor_cls = Sign.anchor tvs sign in
  let lst =
    try IntMap.find mdl_nme ft.base
    with Not_found ->
      let lst = ref [] in
      ft.base <- IntMap.add mdl_nme lst ft.base;
      lst
  and desc = {
    mdl = -1;
    fname    = fn;
    cls      = cls;
    anchor_cls = anchor_cls;
    anchor_fg  = anchor_fg;
    impl     =
    if Feature.Spec.has_definition spec then Feature.Empty
    else if defer then Feature.Deferred
    else Feature.Builtin;
    tvs      = tvs;
    anchored = anchored;
    argnames = standard_argnames nargs;
    sign     = sign;
    tp       = Class_table.to_dummy ntvs sign;
    priv     = bdesc;
    pub      = bdesc_opt
  }
  in
  Seq.push desc ft.seq;
  lst := cnt :: !lst



let base_table (verbosity:int) : t =
  (** Construct a basic table which contains at least implication.  *)
  let bool    = Class_table.boolean_type 0 in
  let ft      = empty verbosity
  in
  let any1  = Variable (Class_table.any_index+1)
  and any2  = Variable (Class_table.any_index+2)
  and bool1 = Variable (Class_table.boolean_index+1)
  and g_tp  = Variable 0
  and a_tp  = Variable 0
  and b_tp  = Variable 1 in
  let p_tp1 = VAppl (Class_table.predicate_index+1, [|g_tp|])
  and p_tp2 = VAppl (Class_table.predicate_index+2, [|a_tp|])
  and f_tp  = VAppl (Class_table.function_index+2, [|a_tp;b_tp|])
  and tup_tp= VAppl (Class_table.tuple_index+2, [|a_tp;b_tp|])
  and spec_none n = Feature.Spec.make_func_def (standard_argnames n) None []
  and spec_term n t = Feature.Spec.make_func_def (standard_argnames n) (Some t) []
  in
  add_base (* ==> *)
    "boolean" Class_table.boolean_index (FNoperator DArrowop)
    [||] [|bool;bool|] bool false false (spec_none 2) ft;

  add_base (* false *)
    "boolean" Class_table.boolean_index FNfalse
    [||] [||] bool false false (spec_none 0) ft;

  let imp_id1   = 1 + implication_index
  and false_id1 = 1 + false_index
  and false_id2 = 2 + false_index
  and imp_id2   = 2 + implication_index
  and not_id2   = 2 + not_index
  in
  let not_term = Term.binary imp_id1 (Variable 0) (Variable false_id1)
  and or_term  =  Term.binary imp_id2 (Term.unary not_id2 (Variable 0)) (Variable 1)
  and and_term =
    Term.unary  not_id2
      (Term.binary imp_id2
         (Variable 0)
         (Term.binary imp_id2 (Variable 1) (Variable false_id2)))
  and true_term =
    Term.binary implication_index (Variable false_index) (Variable false_index)
  in
  add_base (* true *)
    "boolean" Class_table.boolean_index FNtrue
    [||] [||] bool false false (spec_term 0 true_term) ft;

  add_base (* not *)
    "boolean" Class_table.boolean_index (FNoperator Notop)
    [||] [|bool|] bool false false (spec_term 1 not_term) ft;

  add_base (* and *)
    "boolean" Class_table.boolean_index (FNoperator Andop)
    [||] [|bool;bool|] bool false false (spec_term 2 and_term) ft;

  add_base (* or *)
    "boolean" Class_table.boolean_index (FNoperator Orop)
    [||] [|bool;bool|] bool false false (spec_term 2 or_term) ft;

  add_base (* equality *)
    "any" Class_table.any_index (FNoperator Eqop)
    [|any1|] [|g_tp;g_tp|] bool1 true false (spec_none 2) ft;

  add_base (* in *)
    "predicate" Class_table.predicate_index (FNoperator Inop)
    [|any1|] [|g_tp;p_tp1|] bool1 false false (spec_none 2) ft;

  add_base (* domain *)
    "function" Class_table.function_index (FNname ST.domain)
    [|any2;any2|] [|f_tp|] p_tp2 false true (spec_none 1) ft;

  add_base (* tuple *)
    "tuple" Class_table.tuple_index (FNname ST.tuple)
    [|any2;any2|] [|a_tp;b_tp|] tup_tp false false (spec_none 2) ft;

  add_base (* first *)
    "tuple" Class_table.tuple_index (FNname ST.first)
    [|any2;any2|] [|tup_tp|] a_tp false false (spec_none 1) ft;

  add_base (* second *)
    "tuple" Class_table.tuple_index (FNname ST.second)
    [|any2;any2|] [|tup_tp|] b_tp false false (spec_none 1) ft;

  assert ((descriptor implication_index ft).fname = FNoperator DArrowop);
  assert ((descriptor false_index ft).fname       = FNfalse);
  assert ((descriptor not_index ft).fname         = FNoperator Notop);
  assert ((descriptor and_index ft).fname         = FNoperator Andop);
  assert ((descriptor or_index ft).fname          = FNoperator Orop);
  assert ((descriptor eq_index ft).fname          = FNoperator Eqop);
  assert ((descriptor domain_index ft).fname      = FNname ST.domain);
  assert ((descriptor tuple_index ft).fname       = FNname ST.tuple);
  assert ((descriptor first_index ft).fname       = FNname ST.first);
  assert ((descriptor second_index ft).fname      = FNname ST.second);
  ft


let has_visible_variant (i:int) (ft:t): bool =
  (* Does the feature [i] has a visible variant in the current module?
   *)
  assert (is_interface_use ft);
  let bdesc = base_descriptor i ft
  and mt    = module_table ft in
  let used  = Module_table.current_used mt in
  IntMap.exists
    (fun cls ivar ->
      let desc  = descriptor ivar ft in
      IntSet.mem desc.mdl used)
    bdesc.variants



let find_funcs
    (fn:feature_name)
    (nargs:int) (ft:t)
    : (int * Tvars.t * Sign.t) list =
  let tab = Feature_map.find fn ft.map in
  let lst =
    List.fold_left
      (fun lst (i,_,_,_) ->
        let desc = descriptor i ft in
        let sign = desc.sign in
        let arity = Sign.arity sign
        and tvs   = Tvars.fgs_to_global desc.tvs
        in
        let nfgs = Tvars.count_all tvs in
        if is_public ft && not (Option.has desc.pub) then
          lst
        else if is_interface_use ft &&
          not (has_visible_variant i ft) then
          lst
        else if arity <= nargs then
          (i,tvs,sign) :: lst
        else if nargs = 0 then begin (* upgrade *)
          assert (0 < arity);
          let is_pred = is_predicate i ft in
          let tp = Class_table.upgrade_signature nfgs is_pred sign in
          let s  = Sign.make_const tp in
          (i,tvs,s) :: lst
        end else
          lst
      )
      []
      (Term_table.terms !tab)
  in
  if lst = [] then raise Not_found
  else lst






let find_unifiables (fn:feature_name) (tp:type_term) (ntvs:int) (ft:t)
    : (int*Term_sub.t) list =
  try
    let tab = Feature_map.find fn ft.map in
    Term_table.unify_with tp ntvs 0 !tab
  with Not_found ->
    []


let find_variant_candidate0 (i:int) (cls:int) (ft:t): int =
  (* Find the variant of the feature [i] in the class [cls] *)
  assert (has_anchor i ft); (* exactly one formal generic anchored
                               to the owner class *)
  let desc = descriptor i ft in
  let nfgs = Tvars.count_all desc.tvs
  and fg_anchor = anchor i ft in
  assert (nfgs = 1);
  assert (fg_anchor = 0);
  (*let candidates = Class_table.find_features
      (desc.fname, desc.tp, nfgs)
      cls
      ct*)
  let candidates = find_unifiables desc.fname desc.tp nfgs ft
  in
  let lst = List.filter
      (fun (idx,sub) ->
        try
          i <> idx &&
          let desc_heir = descriptor idx ft
          and tp1       = Term_sub.find 0 sub in
          Tvars.principal_class tp1 desc_heir.tvs = cls
        with Not_found ->
          false)
      candidates
  in
  match lst with
    [] -> raise Not_found
  | [i_variant,_] -> i_variant
  | _ ->
      printf "many variants of %s\n" (string_of_signature i ft);
      List.iter
        (fun (i_var,_) ->
          printf "  %d %s\n" i_var
            (string_of_signature i_var ft);)
        lst;
      assert false (* cannot happen *)


let find_variant_candidate (i:int) (cls:int) (ft:t): int =
  (* Find the variant of the feature [i] in the class [cls] *)
  try
    variant i cls ft
  with Not_found ->
    find_variant_candidate0 i cls ft



let has_variant_candidate (i:int) (cls:int) (ft:t): bool =
  (* Has the feature [i] a variant in the class [cls]? *)
  try let _ = find_variant_candidate i cls ft in true
  with Not_found -> false


let split_equality (t:term) (nbenv:int) (ft:t): int * int * term * term =
  (* Return [nargs, eq_id, left, right] if the term is an equality. *)
  let nargs, t =
    try
      let n,nms,t0 = Term.all_quantifier_split t in
      n, t0
    with Not_found ->
      0, t
  in
  let nbenv = nbenv + nargs in
  let i,a,b = Term.binary_split_0 t in
  let i = i - nbenv in
  assert (i < count ft);
  if (base_descriptor i ft).is_eq then begin
    nargs, i, a, b
  end else
    raise Not_found


let is_equality (t:term) (nbenv:int) (ft:t): bool =
  try
    let _ = split_equality t nbenv ft in true
  with Not_found -> false



let update_equality (seed:int) (bdesc:base_descriptor) (ft:t): unit =
  (* If the feature [seed] is the equality feature of ANY then mark the base
     descriptor [bdesc] as equality. *)
  if seed = eq_index then begin
    bdesc.is_eq <- true;
  end



let inherit_feature (i0:int) (i1:int) (cls:int) (export:bool) (ft:t): unit =
  (* Inherit the feature [i0] as the feature [i1] in the class [cls], i.e. add
     [i1] as a variant to the seed of [i0] and make the seed of [i0] to the seed
     of [i1]. Furthermore [i1] is no longer its own seed and cannot be found
     via the feature map *)
  assert (not export || is_interface_check ft);
  assert (i0 < count ft);
  assert (i1 < count ft);
  assert (i0 <> i1);
  assert (cls = (descriptor i1 ft).cls);
  let bdesc0 = base_descriptor i0 ft
  and bdesc1 = base_descriptor i1 ft
  in
  (* add variant to seed and seed to variant*)
  bdesc1.is_inh <- true;
  let bdesc_seed = base_descriptor bdesc0.seed ft in
  assert (not (IntMap.mem cls bdesc_seed.variants) ||
          IntMap.find cls bdesc_seed.variants = i1);
  bdesc_seed.variants <- IntMap.add cls i1 bdesc_seed.variants;
  bdesc1.seed         <- bdesc0.seed;
  update_equality bdesc0.seed bdesc1 ft;
  assert (has_variant bdesc0.seed cls ft);
  if not export && is_public ft then begin (* do the same for the private view *)
    let bdesc0 = base_descriptor_priv i0 ft
    and bdesc1 = base_descriptor_priv i1 ft
    in
    bdesc1.is_inh <- true;
    let bdesc_seed = base_descriptor_priv bdesc0.seed ft in
    assert (not (IntMap.mem cls bdesc_seed.variants) ||
            IntMap.find cls bdesc_seed.variants = i1);
    bdesc_seed.variants <- IntMap.add cls i1 bdesc_seed.variants;
    bdesc1.seed         <- bdesc0.seed;
    update_equality bdesc0.seed bdesc1 ft;
    assert (has_private_variant bdesc0.seed cls ft);
  end;
  let fn  = (descriptor i1 ft).fname in
  let tab = Feature_map.find fn ft.map in
  tab := Term_table.remove i1 !tab






let inherit_new_effective (i:int) (cls:int) (ghost:bool) (ft:t): int =
  let desc = descriptor i ft in
  let ctp0,tvs = Class_table.class_type cls ft.ct
  and anchor  = anchor i ft in
  assert (anchor <> -1);
  assert (Tvars.count_fgs desc.tvs = 1);
  let f_tp (tp:type_term): type_term =
    Term.sub tp [|ctp0|] (Tvars.count_all tvs) in
  let cnt = count ft
  and nargs = Array.length desc.argnames
  in
  let spec = variant_spec i cnt desc.cls cls ft in
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    if is_public ft then Some (standard_bdesc cnt cls spec nargs ft)
    else None
  and sign = Sign.map f_tp desc.sign
  in
  let sign = if ghost then Sign.to_ghost sign else sign in
  let anchor_fg, anchor_cls = Sign.anchor tvs sign in
  Seq.push
    {mdl       = Class_table.current_module ft.ct;
     fname     = desc.fname;
     cls       = cls;
     anchor_cls = anchor_cls;
     anchor_fg  = anchor_fg;
     impl      = desc.impl;
     tvs       = tvs;
     anchored  = Array.make 1 anchor (*(anchor+ntvs)*);
     argnames  = desc.argnames;
     sign      = sign;
     tp        = f_tp desc.tp;
     priv      = bdesc;
     pub       = bdesc_opt
   } ft.seq;
  add_class_feature cnt false false false ft;
  inherit_feature i cnt cls false ft;
  if ft.verbosity > 1 then
    printf "  new feature inherited %d %s\n" cnt (string_of_signature cnt ft);
  cnt



let add_function
    (fn:       feature_name withinfo)
    (tvs:      Tvars.t)
    (argnames: int array)
    (sign:     Sign.t)
    (body:     Feature.body)
    (ft:       t): unit =
  assert (not (has_with_signature fn.v tvs sign ft));
  let is_priv = is_private ft
  and cnt     = Seq.count ft.seq
  and nargs   = Array.length argnames
  and spec,impl = body
  in
  let ghost_required =
    Feature.Spec.has_postconditions spec ||
    match Feature.Spec.definition spec with
      Some t when is_ghost_term t nargs ft -> true
    | _ -> false
  in
  if ghost_required && not (Sign.is_ghost sign) then
      error_info fn.i "Must be a ghost function";
  let mdl = Class_table.current_module ft.ct in
  let cls = Class_table.owner tvs sign ft.ct
  and anchor_fg, anchor_cls = Sign.anchor tvs sign in
  let anchored = Class_table.anchored tvs cls ft.ct in
  let nanchors = Array.length anchored in
  begin match impl with
    Feature.Deferred ->
      Class_table.check_deferred cls nanchors fn.i ft.ct
  | _ -> ()
  end;
  let bdesc = standard_bdesc cnt cls spec nargs ft
  and bdesc_opt =
    if is_priv then None else Some (standard_bdesc cnt cls spec nargs ft)
  and nfgs = Tvars.count_all tvs
  and base = (is_private ft || is_interface_use ft) &&
    not (Feature.Spec.has_definition spec)
  in
  let desc =
    {mdl      = mdl;
     cls      = cls;
     anchor_cls = anchor_cls;
     anchor_fg  = anchor_fg;
     fname    = fn.v;
     impl     = impl;
     tvs      = tvs;
     argnames = argnames;
     sign     = sign;
     tp       = Class_table.to_dummy nfgs sign;
     anchored = anchored;
     priv     = bdesc;
     pub      = bdesc_opt}
  in
  Seq.push desc ft.seq;
  add_key cnt ft;
  add_class_feature cnt false false base ft



let update_function
    (idx: int)
    (info:info)
    (is_ghost: bool)
    ((spec,impl):  Feature.body)
    (ft:       t): unit =
  let desc    = descriptor idx ft
  and mdl     = Class_table.current_module ft.ct
  and is_priv = is_private ft
  in
  let not_match str =
    let str = "The " ^ str ^ " of \""
      ^ (feature_name_to_string desc.fname)
      ^ "\" does not match the previous definition"
    in
    error_info info str
  in
  desc.mdl <- mdl;
  if is_priv then begin
    if impl <> desc.impl then
      not_match "implementation status";
    if not (Feature.Spec.equivalent spec desc.priv.spec) then
      not_match "private definition"
  end else begin
    let def_opt = Feature.Spec.definition spec
    and def_priv_opt = Feature.Spec.definition desc.priv.spec in
    if Option.has def_opt && def_opt <> def_priv_opt then
      not_match "public definition";
    match desc.pub with
      None ->
        if Sign.is_ghost desc.sign && not is_ghost then
          error_info info "Must be a ghost function";
        let nargs = Array.length desc.argnames in
        desc.pub <- Some (standard_bdesc idx desc.cls spec nargs ft);
        add_class_feature idx false true false ft
    | Some bdesc ->
        let def_opt = Feature.Spec.definition spec
        and def_bdesc_opt = Feature.Spec.definition bdesc.spec in
        if def_bdesc_opt <> def_opt then
          not_match "public definition"
  end








let has_current_module (ft:t): bool =
  Class_table.has_current_module ft.ct

let current_module (ft:t): int =
  Class_table.current_module ft.ct

let count_modules (ft:t): int =
  Class_table.count_modules ft.ct

let used_modules (mdl:int) (ft:t): IntSet.t =
  Class_table.used_modules mdl ft.ct

let find_module (name:int*int list)  (ft:t): int =
  Class_table.find_module name ft.ct

let module_name (mdl:int) (ft:t): string = Class_table.module_name mdl ft.ct


let add_base_features (mdl_name:int) (ft:t): unit =
  try
    let lst = IntMap.find mdl_name ft.base in
    let curr_mdl = current_module ft in
    List.iter
      (fun idx ->
        let desc = descriptor idx ft in
        let base = not (Feature.Spec.has_definition desc.priv.spec) in
        assert (desc.mdl = -1);
        desc.mdl <- curr_mdl;
        add_key idx ft;
        add_class_feature idx true false base ft)
      !lst
  with Not_found ->
    ()




let add_used_module (name:int*int list) (used:IntSet.t) (ft:t): unit =
  Class_table.add_used_module name used ft.ct;
  add_base_features (fst name) ft




let add_current_module (name:int) (used:IntSet.t) (ft:t): unit =
  Class_table.add_current_module name used ft.ct;
  add_base_features name ft;
  if name <> ST.symbol "boolean" then begin
    let or_desc  = descriptor or_index ft
    and and_desc = descriptor and_index ft in
    or_desc.priv.spec   <- Feature.Spec.make_func_def or_desc.argnames  None [];
    and_desc.priv.spec  <- Feature.Spec.make_func_def and_desc.argnames None []
  end



let set_interface_check (used:IntSet.t) (ft:t): unit =
  Class_table.set_interface_check used ft.ct;
  ft.map <- Feature_map.empty;
  let mdl = current_module ft in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if desc.mdl = mdl || IntSet.mem desc.mdl used then
      match desc.pub with
        Some bdesc ->
          if not bdesc.is_inh then
            add_key i ft
      | None ->
          add_key i ft;
          if desc.mdl <> mdl then
            desc.pub <- Some (desc.priv)
  done



let check_interface (ft:t): unit =
  assert (is_interface_check ft);
  let mt = module_table ft in
  let curr = Module_table.current mt in
  for i = 0 to count ft - 1 do
    let desc = descriptor i ft in
    if curr = desc.mdl
        && is_desc_deferred desc
        && not (Option.has desc.pub)
        && Class_table.is_class_public desc.cls ft.ct then
      error_info (FINFO (1,0))
        ("deferred feature `" ^ (string_of_signature i ft) ^
         "' is not public")
  done




let pattern_subterms (n:int) (pat:term) (nb:int) (ft:t): (int*term*int) list =
  (* Return a list of all subterms of the pattern [n,pat] with their level.
   *)
  let rec subterms t level lst =
    match t with
      Variable i ->
        assert (i < n || n + nb <= i);
        assert (i < n || is_constructor (i-n-nb) ft);
        (n+nb,t,level)::lst
    | VAppl(i,args) ->
        assert (n + nb <= i);
        assert (is_constructor (i-n-nb) ft);
        let lst = (n+nb,t,level)::lst
        and level = level + 1 in
        Array.fold_left
          (fun lst arg -> subterms arg level lst)
          lst
          args
    | _ ->
        assert false (* cannot happen in pattern *)
  in
  subterms pat 0 []




let peer_constructors (i:int) (ft:t): IntSet.t =
  assert (i < count ft);
  assert (is_constructor i ft);
  let cls = class_of_feature i ft in
  assert (cls <> -1);
  let set = Class_table.constructors cls ft.ct in
  assert (IntSet.mem i set);
  IntSet.remove i set



let peer_matches (i:int) (nb:int) (ft:t): (int*term) list =
  (* Match expressions for the peer constructors on the constructor [i] transformed
     into an environment with [nb] variables. *)
  assert (i < count ft);
  assert (is_constructor i ft);
  let set = peer_constructors i ft in
  IntSet.fold
    (fun i lst ->
      assert (is_constructor i ft);
      let n = arity i ft in
      let t =
        if n = 0 then
          Variable (i + nb + n)
        else
          let args = Array.init n (fun i -> Variable i) in
          VAppl (i + nb + n, args) in
      (n,t)::lst)
    set
    []





(*  Peer Pattern
    ============

    We have a pattern [pat] and want to find the minimal set of complementary
    pattern so that one pattern of the complete set always matches.

    (a) The pattern is a variable: The complementary set is empty (catch all)

    (b) The pattern has the form [f(a,b,...)] (Note: [f] has to be a constructor).

        The first part of the complementary set consists of all trivial
        pattern of the peer constructors of [f].

        Each argument has a complementary set. We have to make a combination
        of the complementary sets of the arguments. We compute a list of
        argument pattern lists and start with the list of arguments and an
        an empty list of argument pattern lists:

        (a1) The argument list is empty: No pattern is added to the list of
             argument pattern lists.

        (a2) The argument list is 'rest+a':

             cset: The complementary pattern set of 'a'
             lst:  The list of argument pattern lists of the rest

             for each pattern in {a}+cset
                 for each argument pattern list in 'lst':
                     append a to the argument pattern list
             concatenate all list of argument pattern lists

             for each pattern p in cset
                     add [v0,v1,...,p] to the resulting argument pattern list ????

        (a3) At the end we have a complete list of argument pattern list

             The complementary set of 'f(a,b,...)' is

                   fcset + {f(a0,b0,...), f(a1,b1,...), ... }

             where [ai,bi,...] is an entry in the list of argument pattern lists.

    Boundary cases:

        f(a,b,...) is f(v0,v1,...) where vi is a variable:

        The complementary set of each vi is empty. The list of argument
        pattern lists before is empty before and remains empty during
        (a2). Therefore the complementary pattern set of f(v) consist of all
        primitive pattern of the peer constructors of f.

    Implementation hints:

        (a) A pattern set has the form

                 {(p0,n0), (p1,n1), ... }

            where p is the pattern term and n is the number of variables in
            the pattern.

        (b) A list of argument pattern lists has the form

                 [ ([p0a,p0b,...],n0), ([p1a,p1b,...],n1), ... ]

            where [pia,pib,...] is the ith argument pattern sequence and [ni]
            is the number of used variables in the pattern sequence.

            Appending an argument pattern (p,n) to the sequence ([pia,pib,...],ni)
            results in ([pia,pib,...p'],n+ni) where p' is p shifted up by n.


 *)
let complementary_pattern (n:int) (p:term) (nb:int) (ft:t): (int*term) list =
  let rec comp_pat (p:term): (int*term) list =
    let rec args_pat_lst (argsrev:term list) (nargs:int)
        (aplst:(term list * int) list)
        : (term list * int) * (term list * int) list =
      assert (List.length argsrev = nargs);
      match argsrev with
        [] ->
          ([],0), aplst
      | a::tl ->
          let cset  = comp_pat a
          and (argsrevtl,nargsrevtl), aplst = args_pat_lst tl (nargs-1) aplst in
          let a,na =
            let abnd  = Term.bound_variables a n
            and perm  = Array.make n (Variable (-1)) in
            let na = IntSet.fold
                (fun i na ->
                  perm.(i) <- Variable na; na+1)
                abnd 0 in
            let a = Term.sub a perm na in
            a,na
          in
          let push_arg n p nargsrev argsrev =
            let argsrev =
              List.map (fun t -> Term.upbound n nargsrev t) argsrev in
            let argsrev = (Term.up nargsrev p)::argsrev in
            argsrev,(n+nargsrev) in
          let prepend_pattern np p aplst =
            List.rev_map (fun (argsrev,n) -> push_arg np p n argsrev) aplst in
          let aplst =
            let cset = (na,a)::cset in
            let lstlst =
              List.rev_map (fun (n,p) -> prepend_pattern n p aplst) cset in
            List.concat lstlst in
          let push_arg0 n p = push_arg n p nargsrevtl argsrevtl in
          let aplst =
            List.fold_left
              (fun aplst (n,p) ->
                (push_arg0 n p)::aplst)
              aplst
              cset in
          push_arg0 na a, aplst
    in
    match p with
      Variable i when i < n ->
        []
    | Variable i ->
        assert (n + nb <= i);
       peer_matches (i-n-nb) nb ft
    | VAppl (i,args) ->
        assert (n + nb <= i);
        let idx = i-n-nb in
        let fcset = peer_matches idx nb ft in
        let nargs    = Array.length args
        and args_rev = List.rev (Array.to_list args) in
        let _,apl = args_pat_lst args_rev nargs [] in
        List.fold_left
          (fun cset (args_rev,n) ->
            let args = Array.of_list (List.rev args_rev) in
            assert (Array.length args = nargs);
            let p    = VAppl (idx+n+nb, args) in
            (n,p) :: cset)
          fcset
          apl
    | _ ->
        assert false (* cannot happen in pattern *)
  in
  comp_pat p


let is_pattern (n:int) (t:term) (nb:int) (ft:t): bool =
  (* Is the term [t] with [n] variables a pattern i.e. does it contain only variables
     or constructors?

     All variables below [n] must occur only once in a pattern.
   *)
  let is_constr i = (n+nb) <= i && is_constructor (i-n-nb) ft
  in
  let free = Term.free_variables     t n
  and bnd  = Term.bound_variables    t n
  and bnd_lst = Term.used_variables t n in
  let nbnd = IntSet.cardinal bnd
  in
  IntSet.for_all is_constr free &&
  n = nbnd &&
  nbnd = List.length bnd_lst




let case_substitution
    (nt:int) (t:term) (npat:int) (pat:term) (nb:int) (ft:t): (term array) option =
  (* The substitutions for the match expression [pat] which make the match
     expression equivalent to the term [t] (with [nt] variables) or [None] if
     the match definitely fails. The function raises [Not_found] if neither a
     positive or a negative match is possible i.e. if matching cannot be decided
     because the term does not provide enough information.

     Positive match: The term is more special than the pattern and substitutions
                     can be found.

     Negative match: The term has a different constructor than the pattern at a
                     corresponding position.

     Undecidable:    The term is more general than the pattern or the term has a
                     non constructor at some position where a constructor would be
                     needed to compare it with the corresponding constructor of the
                     pattern. The latter case cannot occur if the term is a pattern.

                     I.e. if the term is a pattern then Undecidable means that the
                     term is more general.
 *)
  let subargs = Array.make npat (Variable (-1))
  and subflgs = Array.make npat false
  and decid   = ref true
  and hassub  = ref true in
  let is_constr idx =
    nt + nb <= idx && is_constructor (idx-nt-nb) ft
  in
  let rec do_match t pat =
    let match_args args1 args2 =
      Array.iteri
        (fun i arg ->
          do_match arg args2.(i))
        args1
    in
    match t, pat with
      _, Variable i when i < npat ->
        assert (not subflgs.(i));
        subflgs.(i) <- true;
        subargs.(i) <- t
    | Variable idx1, Variable idx2 when is_constr idx1 ->
        hassub := !hassub && idx1 + npat = idx2
    | Variable idx1, VAppl(idx2,args2) when is_constr idx1 ->
        hassub := false
    | VAppl (idx1,_) , Variable idx2 when is_constr idx1 ->
        hassub := false
    | VAppl(idx1,args1), VAppl(idx2,args2) when  is_constr idx1 ->
        assert (nt + nb <= idx1);
        assert (npat + nb <= idx2);
        hassub :=  !hassub &&  idx1 - nt =  idx2 - npat;
        match_args args1 args2
    | _ ->
        decid := false
  in
  do_match t pat;
  assert (not !hassub || not !decid || interval_for_all (fun i -> subflgs.(i)) 0 npat);
  if not !hassub then
    None
  else if !decid then
    Some subargs
  else
    raise Not_found




let is_case_matching (t:term) (npat:int) (pat:term) (nb:int) (ft:t): bool =
  (* Is the term [t] matching the match expression [mtch] with [n] variables?
     Raise [Not_found] if the match is undecidable.
   *)
  match case_substitution 0 t npat pat nb ft with
    None   -> false
  | Some _ -> true





(*  Unmatched cases
    ===============


    Example:

        is_prefix (a,b:[G]): BOOLEAN
            -> inspect a, b
               case nil, _   then true
               case _  , nil then false
               case x^a, y^b then x = y and a.is_prefix(b)
               end

    The first case leaves us the unmatched cases:

         (0^1, 2)

    The second case has the pattern (0, nil) and should leave us with

         (0^1, 2^3)

    which is matched by the third case.

    The peer pattern of the second case:

        (0, 1^2)

    Check the second case:
        compare unmatched    (0^1,   2)
        with pattern         (0  , nil)

    An unmatched pattern has to be either
        removed                           the pattern is more general
        left in unchanged                 unmatched and pattern do not match
        modified and/or splitted up       the pattern matches partially

    Partial match: There is a substitution for the unmatched and for the pattern.
                   When both substitutions are applied the terms are equal

       (0^1,2)   sub [0~>0,1~>1,2~>nil]    res (0^1,nil)
       (0,nil)   sub [0~>0^1]              res (0^1,nil)

    The pattern is more general: Special case of a partial match where the
                                 substitution of the unmatched is empty

    No match: There is no substitution pair.


    Unification of two pattern:
    ===========================

    Example 1:
    (0^1,2) and (0,nil)

    With unique variables (0^1,2) and (3,nil)

    General substitution: [0~>0,1~>1,2~>nil,  3~>0^1]
    makes both to (0^1,nil)

    Example 2:
    (0^1,2) and (0,1)

    With unique variables (0^1,2) and (3,4)

    General substitution: [0~>0,1~>1,2~>2,  3~>0^1,4~>2]
    makes both to (0^1,2)

    If one pattern is more special than the other it gets the identity substitution.
    I.e. substitution happens only on the more general pattern.

    Computing unmatched pattern
    ===========================

    For each case clause we have a set of unmatched pattern of the previous clauses.

    For each pattern in the set of unmatched pattern the current pattern is either

    - unrelated:     The unmatched pattern remains
    - more general:  The unmatched pattern is resolved
    - partial match: The unmatched pattern has to be splitted into unmatched and
                     resolved subpattern. Only the unmatched subpattern remain.

    Splitting partially resolved pattern
    ====================================

    We have an unmatched pattern upat and a pattern pat. We unify the two pattern
    and get a substitution which is not the identity in the part of the variables
    of upat. The variables with a nontrivial substitution are only partially
    resolved.

    1. Do the substitution on upat to get upatsub
         The partially resolved variables dissappear and some variables of pat
         might be introduced

    2. Treat upatsub as a pattern and calculate all peer pattern

    3. Filter the peer pattern so that only pattern more special than upat remain

    The unmatched pattern upat has to be splitted up into the filtered set of peer
    pattern of upatsub.

 *)
let unmatched_and_splitted
    (n:int) (pat:term) (unmatched:(int*term)list) (nb:int) (ft:t)
    : (int*term) list * (int * term * term array option) list =
  (* Calculate the remaining unmatched pattern and a split list. The unmatched
     pattern are all the pattern which are left over with the pattern [n,pat]
     working of the unmatched cases in [unmatched]. The split list consist of one
     ore more pattern into which [n,pat] has to be splitted. The pattern has to be
     splitted if it is more general than some pattern in [unmatched].
   *)
  let is_trivial arr n =
    assert (n <= Array.length arr);
    interval_for_all
      (fun i ->
        match arr.(i) with
          Variable k -> k < n
        | _ -> false)
      0 n
  and unmatched_partial (n:int) (pat:term) (arr: term array): int * term =
    assert (n <= Array.length arr);
    let len = Array.length arr in
    let n2  = len - n in
    let upat  = Term.upbound n2 n pat in
    let upat  = Term.sub upat arr len in
    let used  = List.rev (Term.used_variables upat len) in
    let n_new = List.length used in
    let arr2  = Array.make len (Variable (-1)) in
    List.iteri (fun pos i -> arr2.(i) <- Variable pos) used;
    let upat  = Term.sub upat arr2 n_new in
    n_new, upat in
  let add_filtered_peers
      (peers:(int*term)list) (npat:int) (pat:term) (lst:(int*term)list)
      : (int*term)list =
    List.fold_left
      (fun lst (n,t) ->
        try
          let subarr = Term_algo.unify_pattern n t npat pat in
          if is_trivial subarr n then (n,t) :: lst else lst
        with Not_found ->
          lst)
      lst
      peers
  in
  let unmatched,splitted = List.fold_left
      (fun (unmatched,splitted) (npat0,pat0) ->
        try
          let subarr = Term_algo.unify_pattern npat0 pat0 n pat in
          assert (Array.length subarr = npat0 + n);
          if is_trivial subarr npat0 then begin
            (* pat is more general, i.e. pat0 no longer needed as unmatched *)
            let triple =
              if npat0 = n && pat = pat0 then (n,pat,None)
              else (npat0,pat0,Some subarr) in
            unmatched,
            triple::splitted
          end else begin
            (* pat resolves pat0 only partial, splitting of pat necessary *)
            let n2, upat2 = unmatched_partial npat0 pat0 subarr in
            let peers = complementary_pattern n2 upat2 nb ft
            and subarr =
              try Term_algo.unify_pattern n2 upat2 n pat
              with Not_found -> assert false
            in
            add_filtered_peers peers npat0 pat0 unmatched,
            (n2,upat2,Some subarr)::splitted
          end
        with Not_found -> (* pat and pat_i cannot be unified *)
          (npat0,pat0) :: unmatched, splitted)
      ([],[])
      unmatched in
  unmatched, splitted



let unmatched_inspect_cases (args:term array) (nb:int) (ft:t): (int * term) list =
  (* The unmatched cases of the inspect expression [Flow(Inspect,args)]
   *)
  let len = Array.length args in
  assert (3 <= len);
  assert (len mod 2 = 1);
  let ncases = len / 2 in
  let rec unmatched_from (i:int) (lst:(int*term) list): (int*term) list =
    assert (i <= ncases);
    if i = ncases then
      lst
    else begin
      let npat_i,_,pat_i = Term.pattern_split args.(2*i+1) in
      let unmatched,_ = unmatched_and_splitted npat_i pat_i lst nb ft in
      unmatched_from (i+1) unmatched
    end
  in
  unmatched_from 0 [1, Variable 0]




(* "Catch all" cases:

        (<=) (a,b:NATURAL): BOOLEAN
            -> inspect a,b
               case 0,            _            then true        -- critical!!
               case _,            0            then false
               case successor(n), successor(m) then n <= m
               end

   The first case is implicitly two cases. The inspect has to be unfolded

        (<=) (a,b:NATURAL): BOOLEAN
            -> inspect a,b
               case 0,            0            then true
               case 0,            successor(_) then true
               case successor(_), 0            then false
               case successor(n), successor(m) then n <= m
               end

   It might be possible that one inspect variable has only catchall cases.

        plus (t:(NATURAL,NATURAL): NATURAL
            -> inspect t
               case (a,0)            then a                   -- uncritical
               case (a,successor(b)) then successor(a + b)
               end

   In the first example the catchall case is critical in the third example it
   is uncritical and does not require unfolding. What's the difference? In the
   first example there are other cases where a constructor appears at the same
   position, i.e. the inspect expression actually distinguishes cases at this
   position.

   For each case we have to calculate the unmatched pattern of all previous
   cases. With the current pattern and the unmatched set we can calculate the
   new set of cases which will substitute the current case.

       Walk through all unmatched:

          a) unmatched pattern is more general: split up the unmatched
             pattern. The current case is not modified.

          b) current pattern is more general or equal: Add a case clause with
             the unmatched (there might be more unmatched pattern which are
             more special than the current pattern.

   If the set of unmatched pattern is empty then the case clause is not needed.
   This condition might be flagged as an error. *)


let inspect_unfolded (info:info) (args:term array) (nb:int) (ft:t): term array =
  (* Unfold case clauses in the inspect expression [Flow(Inspect,args)].

     A case clause has to be unfolded to a set of clauses if it is more general
     than some of the unmatched clauses.
   *)
  let len = Array.length args in
  assert (3 <= len);
  assert (len mod 2 = 1);
  let ncases = len / 2 in
  let rec unfolded_from
      (i:int) (unmatched: (int*term)list) (lst: term list): term list =
    if i = ncases then
      lst
    else
      let n,nms,pat,res = Term.case_split args.(2*i+1) args.(2*i+2) in
      let unmatched,splitted =
        unmatched_and_splitted n pat unmatched nb ft in
      if splitted = [] then
        error_info info ("Unneeded case " ^ (string_of_term_anon pat (n+nb) ft));
      let lst =
        List.fold_left
          (fun lst (n0,pat0,sub_opt) ->
            let n1,nms1,pat1,res1 =
              match sub_opt with
                None ->
                  assert (n = n0);
                  n,nms,pat,res
              | Some arr ->
                  assert (Array.length arr = n0 + n);
                  let res0 = Term.up n0 res in
                  let res0 = Term.sub res0 arr (n0+n) in
                  let res0 =
                    try Term.down_from n n0 res0
                    with Term_capture -> assert false in
                  n0, (standard_argnames n0), pat0, res0
            in
            (Term.pattern n1 nms1 res1) :: (Term.pattern n1 nms1 pat1) :: lst)
          lst
          splitted
      in
      unfolded_from (i+1) unmatched lst
  in
  let lst = unfolded_from 0 [1, Variable 0] [] in
  let lst = args.(0) :: (List.rev lst) in
  let args = Array.of_list lst in
  args




let downgrade_term (t:term) (nb:int) (ft:t): term =
  (* Downgrade all calls of the form [Application(Variable i,args)] to
     [VAppl(i,args')] if [i] is not a constant.
   *)
  let rec down t nb =
    let down_args args nb = Array.map (fun t -> down t nb) args
    and down_list lst nb  = List.map  (fun t -> down t nb) lst in
    match t with
      Variable _ ->
        t
    | VAppl (i,args) ->
        VAppl(i, down_args args nb)
    | Application(Variable i,args,pr) when nb <= i ->
        assert (Array.length args = 1);
        let nargs = arity (i - nb) ft in
        let args = down_args args nb in
        if nargs = 0 then
          Application(Variable i,args,pr)
        else
          let args = args_of_tuple_ext args.(0) nb nargs ft in
          VAppl(i,args)
    | Application(f,args,pr) ->
        Application (down f nb, down_args args nb, pr)
    | Lam(n,nms,pres,t0,pr) ->
        Lam (n,nms, down_list pres (1+nb), down t0 (1+nb), pr)
    | QExp (n,nms,t0,is_all) ->
        QExp (n,nms, down t0 (n+nb), is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, down_args args nb)
    | Indset (n,nms,rs) ->
        Indset (n,nms, down_args rs (n+nb))
  in
  down t nb
