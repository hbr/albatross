(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Signature
open Term
open Support
open Container

type t = {mutable tlist: term list;
          mutable sign:  Sign.t;  (* expected *)
          mutable tvars: TVars_sub.t;
          c: Context.t}

let signature (tb:t): Sign.t = Sign.substitute tb.sign tb.tvars

let ntvars (tb:t): int = TVars_sub.count tb.tvars


let string_of_type (tp:type_term) (tb:t): string =
  let ntvs    = ntvars tb
  and fgnames = Context.fgnames tb.c
  and ct      = Context.class_table tb.c in
  Class_table.type2string tp  ntvs fgnames ct


let string_of_signature (s:Sign.t) (tb:t): string =
  let ntvs    = ntvars tb
  and fgnames = Context.fgnames tb.c
  and ct      = Context.class_table tb.c in
  Class_table.string_of_signature s ntvs fgnames ct

let signature_string (tb:t): string =
  let s       = signature tb in
  string_of_signature s tb

let substitution_string (tb:t): string =
  let sub_lst  = Array.to_list (TVars_sub.args tb.tvars)
  and ntvs     = ntvars tb
  and fnames   = Context.fgnames tb.c
  and ct       = Context.class_table tb.c
  in
  "[" ^
  (String.concat
     ","
     (List.mapi
        (fun i tp ->
          (string_of_int i) ^ "~>" ^
          Class_table.type2string tp ntvs fnames ct)
        sub_lst)) ^
  "]"

let concepts_string (tb:t): string =
  let cpt_lst = Array.to_list (TVars_sub.concepts tb.tvars)
  and ct      = Context.class_table tb.c
  in
  "[" ^
  (String.concat
     ","
     (List.map
        (fun tp -> Class_table.type2string tp 0 [||] ct)
        cpt_lst)) ^
  "]"




let add_sub (ok:bool) (i:int) (t:term) (tb:t): unit =
  if ok then
    TVars_sub.add_sub i t tb.tvars
  else
    raise Not_found



let do_sub (i:int) (t:term) (tb:t): unit =
  (** Substitute the variable [i] by the term [t].
   *)
  let cnt     = TVars_sub.count tb.tvars
  and cnt_loc = TVars_sub.count_local tb.tvars
  in
  assert (i<cnt);
  match t with
    Variable j when j<cnt ->
      if i=j then ()
      else
        let lo,hi =
          if (cnt_loc<=j && j<=i) || (i<cnt_loc && i<=j) then
            i,j
          else
            j,i in
        let thi   = Variable hi in
        let ok =
          lo < cnt_loc ||
          Context.concept_satisfies_concept
            (TVars_sub.concept hi tb.tvars)
            (TVars_sub.concept lo tb.tvars)
            tb.c
        in
        add_sub ok lo thi tb
  | _ ->
      let ok =
        i < cnt_loc ||
        Context.type_satisfies_concept
          t
          (TVars_sub.tvars tb.tvars)
          (TVars_sub.concept i tb.tvars)
          tb.c
      in
      add_sub ok i t tb



let has_sub (i:int) (tb:t): bool = TVars_sub.has i tb.tvars

let get_sub (i:int) (tb:t): type_term = TVars_sub.get i tb.tvars


let unify
    (t1:term)
    (t2:term)
    (tb:t)
    : unit =
  (** Unify the terms [t1] and [t2] using the substitution [tvars_sub] in the
      context [c] , i.e.  apply first the substitution [tvars_sub] to both
      terms and then add substitutions to [tvars_sub] so that when applied to
      both terms makes them identical.
   *)
  let nvars = TVars_sub.count tb.tvars
  in
  let rec uni (t1:term) (t2:term) (nb:int): unit =
    let do_sub0 (i:int) (t:type_term): unit =
      let i,t = i-nb, Term.down nb t in
      if has_sub i tb then
        uni t (get_sub i tb) 0
      else
        do_sub i t tb
    in
    match t1,t2 with
      Variable i, _ when nb<=i && i<nb+nvars ->
        do_sub0 i t2
    | _, Variable j when nb<=j && j<nb+nvars ->
        do_sub0 j t1
    | Variable i, Variable j ->
        assert (i<nb||nb+nvars<=i);
        assert (j<nb||nb+nvars<=j);
        if i=j then
          ()
        else
          raise Not_found
    | Application(f1,args1), Application(f2,args2) ->
        let nargs = Array.length args1 in
        if nargs <> (Array.length args2) then
          raise Not_found;
        uni f1 f2 nb;
        for i = 0 to nargs-1 do
          uni args1.(i) args2.(i) nb
        done
    | Lam (nb1,_,t1), Lam (nb2,_,t2) ->
        if nb1=nb2 then
          uni t1 t2 (nb+nb1)
        else
          raise Not_found
    | _ -> raise Not_found
  in
  (try
    uni t1 t2 0
  with Term_capture ->
    assert false);
  assert ((TVars_sub.sub_star t1 tb.tvars)
            = (TVars_sub.sub_star t2 tb.tvars))



let unify_sign_0
    (sig_req:Sign.t)
    (sig_act:Sign.t)
    (tb:t)
    : unit =
  let n         = (Sign.arity sig_req)
  and has_res   = (Sign.has_result sig_req) in
  if not (n = (Sign.arity sig_act) &&
          has_res = (Sign.has_result sig_act)) then
    raise Not_found;
  if has_res then
    unify (Sign.result sig_req) (Sign.result sig_act) tb;
  for i=0 to (Sign.arity sig_req)-1 do
    unify (Sign.arguments sig_req).(i) (Sign.arguments sig_act).(i) tb
  done



let downgrade (tp:type_term) (nargs:int) (tb:t): Sign.t =
  let ntvs  = ntvars tb
  and nfgs  = Context.count_formal_generics tb.c
  and sign  = Sign.make_const tp
  in
  Class_table.downgrade_signature (ntvs+nfgs) sign nargs



let to_dummy (sign:Sign.t) (tb:t): type_term =
  assert (Sign.has_result sign);
  let n = Sign.arity sign in
  assert (0 < n);
  let ntvs_all = ntvars tb + Context.count_formal_generics tb.c in
  Class_table.to_dummy ntvs_all sign




let update_tv
    (sig_req:Sign.t)
    (sig_act:Sign.t)
    (itv:int)
    (tb:t)
    : unit =
  (** The required and actual signatures [sig_req,sig_act] are constant
      signatures, the type of the actual signature is the type variable
      [itv] which has already a substitution.

      Special case: The substitution of [itv] is callable (i.e. a dummy
      type) and the required type is either a function or a predicate and in
      case of a predicate the return type of [itv] is boolean:
      - unify the arguments
      - unify the return type for a function
      - update the substitution

      Otherwise: Do the usual unification *)
  assert (Sign.is_constant sig_req);
  assert (Sign.is_constant sig_act);
  let ntvs_all = ntvars tb + Context.count_formal_generics tb.c in
  let dum_idx  = ntvs_all + Class_table.dummy_index
  and pred_idx = ntvs_all + Class_table.predicate_index
  and fun_idx  = ntvs_all + Class_table.function_index
  and bool_tp  = Variable (ntvs_all + Class_table.boolean_index)
  and tp_req   = Sign.result sig_req
  and tp_act   = TVars_sub.get itv tb.tvars
  in
  match tp_req, tp_act with
    Application(Variable idx_req,args_req),
    Application(Variable idx_act,args_act)->
      if idx_req= pred_idx && idx_act = dum_idx then begin
        if args_act.(1) <> bool_tp then raise Not_found;
        unify args_req.(0) args_act.(0) tb;
        TVars_sub.update_sub
          itv
          (Application(Variable pred_idx, [|args_act.(0)|]))
          tb.tvars
      end else if idx_req = fun_idx && idx_act = dum_idx then begin
        unify args_req.(0) args_act.(0) tb;
        unify args_req.(1) args_act.(1) tb;
        TVars_sub.update_sub
          itv
          (Application(Variable fun_idx, [|args_act.(0);args_act.(1)|]))
          tb.tvars
      end else
        unify_sign_0 sig_req sig_act tb
  | _ ->
      unify_sign_0 sig_req sig_act tb




let unify_sign
    (sig_req:Sign.t)
    (sig_act:Sign.t)
    (tb:t)
    : unit =
  (** Unify the signatures [sig_req] and [sig_act] by adding substitutions
      to [tb] *)
  let n         = (Sign.arity sig_req)
  and is_tv,tv =
    let ntvs = TVars_sub.count tb.tvars in
    if Sign.is_constant sig_act then
      match Sign.result sig_act with
        Variable i when i < ntvs ->
          true, i
      | _ ->
          false, -1
    else
      false, -1
  in
  if n > 0 && is_tv then
    if TVars_sub.has tv tb.tvars then
      let tp        = TVars_sub.get tv tb.tvars in
      let sig_act_1 = downgrade tp n tb
      in
      unify_sign_0 sig_req sig_act_1 tb
    else
      TVars_sub.add_sub tv (to_dummy sig_req tb) tb.tvars
  else if Sign.is_constant sig_req  && is_tv &&
    TVars_sub.has tv tb.tvars
  then
    update_tv sig_req sig_act tv tb
  else
    unify_sign_0 sig_req sig_act tb






let make (e:type_term) (c:Context.t): t =
  (** New accumulator for an expression with the expected type [e] in the
      context with the type variables [tvars] *)
  {tlist = [];
   sign  = Sign.make_const e;
   tvars = (Context.type_variables c);
   c     = c}


let add_global (cs:type_term array) (tb:t): t =
  (** Add the constraints [cs] to the accumulator [tb] *)
  let n = Array.length cs
  and start = TVars_sub.count tb.tvars in
  {tb with
   sign  = Sign.up_from n start tb.sign;
   tvars = TVars_sub.add_global cs tb.tvars}


let add_leaf
    (i:int)
    (tvs:TVars.t)
    (s:Sign.t)
    (tb:t): t =
  assert (not (TVars.count_local tvs > 0 && TVars.count_global tvs > 0));
  let s =
    (* If [i] comes from a global environment, then it has no local type
       variables and space must be made for all type variables (locals and
       globals) of [tb.tvars].

       If [i] comes from a local environment then it has no global type
       variables. But the locals already in coincide with the locals of
       [tb.tvars]. Space has to be made for all type variables (globals
       and locals) of [tb.tvars] which are not yet in [tvs].
     *)
    let nglob = TVars_sub.count_global tb.tvars
    and nloc  = TVars_sub.count_local  tb.tvars - TVars.count_local tvs
    and start = TVars.count_local tvs
    in
    Sign.up nloc (Sign.up_from nglob start s)
  in
  let tb = add_global (TVars.concepts tvs) tb
  in
  unify_sign tb.sign s tb;
  {tb with tlist = (Variable i)::tb.tlist}




let expect_function (nargs:int) (tb:t): unit =
  (** Convert the currently expected signature to a function signature
      with [nargs] arguments and add to the type variables [nargs] fresh
      type variables, one for each argument.
   *)
  tb.tvars <- TVars_sub.add_local nargs tb.tvars;
  let s = tb.sign in
  let s =
    if Sign.is_constant s then s
    else
      (* Convert the function signature into a constant signature with
         a function type as result type. This is always possible because
         we are strengthening the expectations.

         However the argument types of the function signature might be
         fresh type variables without concept. These cannot be used to
         form a function type and/or a tuple type (in case of more than
         one argument). In order to do this without problems we have to
         introduce the corresponding constraints for the fresh type
         variables.
       *)
      assert false (* nyi: conversion from a function signature
                      into a function object *)
  in
  tb.sign  <- Sign.to_function nargs s



let expect_argument (i:int) (tb:t): unit =
  assert (i < (TVars_sub.count_local tb.tvars));
  tb.sign <- Sign.make_const (TVars_sub.get i tb.tvars)



let complete_function (nargs:int) (tb:t): unit =
  let arglst = ref [] in
  for i = 1 to nargs do  (* pop arguments *)
    assert (tb.tlist <> []);
    let t = List.hd tb.tlist in
    tb.tlist <- List.tl tb.tlist;
    arglst := t :: !arglst;
  done;
  let f = List.hd tb.tlist in
  tb.tlist <- List.tl tb.tlist;
  tb.tlist <- (Application (f, Array.of_list !arglst)) :: tb.tlist;
  tb.tvars <- TVars_sub.remove_local nargs tb.tvars



let expect_lambda (ntvs:int) (tb:t): unit =
  assert (Sign.has_result tb.sign);
  tb.tvars <- TVars_sub.add_local ntvs tb.tvars;
  tb.sign  <- Sign.up ntvs tb.sign;
  let rt = Sign.result tb.sign in
  if not (Sign.is_constant tb.sign) then
    tb.sign <- Sign.make_const rt
  else
    tb.sign <-
      try
        let ntvs = (ntvars tb) + (Context.count_formal_generics tb.c) in
        Sign.make_const (Class_table.result_type_of_compound rt ntvs)
      with Not_found ->
        assert false (* cannot happen *)



let complete_lambda (ntvs:int) (names:int array) (tb:t): unit =
  assert (tb.tlist <> []);
  let nargs = Array.length names in
  assert (0 < nargs);
  tb.tvars <- TVars_sub.remove_local ntvs tb.tvars;
  let t = List.hd tb.tlist in
  tb.tlist <- List.tl tb.tlist;
  tb.tlist <- Lam (nargs, names, t) :: tb.tlist


let check_type_variables (inf:info) (tb:t): unit =
  let ntvs_ctxt = Context.count_type_variables tb.c
  and ntvs_loc  = TVars_sub.count_local tb.tvars in
  assert (ntvs_ctxt = ntvs_loc);
  let ntvs_all = ntvars tb + Context.count_formal_generics tb.c in
  let dum_idx  = ntvs_all + Class_table.dummy_index
  in
  for i = 0 to Context.count_last_arguments tb.c - 1 do
    match Context.argument_type i tb.c with
      Variable j when j < ntvs_loc -> begin
        match TVars_sub.get j tb.tvars with
          Application(Variable idx,_) when idx = dum_idx ->
            error_info
              inf
              ("Cannot infer a complete type for " ^
               (ST.string (Context.argument_name i tb.c)))
        | _ -> ()
      end
    | _ -> ()
  done


let result (tb:t): term * TVars_sub.t =
  (** Return the term and the calculated substitutions for the type
      variables *)
  assert (Mylist.is_singleton tb.tlist);
  List.hd tb.tlist, tb.tvars
