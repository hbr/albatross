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

let class_table (tb:t): Class_table.t = Context.class_table tb.c

let signature (tb:t): Sign.t = Sign.substitute tb.sign tb.tvars

let count_local (tb:t): int = TVars_sub.count_local tb.tvars

let count (tb:t): int = TVars_sub.count tb.tvars

let concept (i:int) (tb:t): type_term = TVars_sub.concept i tb.tvars

let tvs (tb:t): Tvars.t  = TVars_sub.tvars tb.tvars

let satisfies (t1:type_term) (t2:type_term) (tb:t): bool =
  let ct  = class_table tb
  and tvs = tvs tb in
  Class_table.satisfies t1 tvs t2 tvs ct


let string_of_type (tp:type_term) (tb:t): string =
  let ct = class_table tb in
  Class_table.string_of_type tp (tvs tb) ct


let string_of_signature (s:Sign.t) (tb:t): string =
  let ct      = Context.class_table tb.c in
  Class_table.string_of_signature s (tvs tb) ct


let string_of_complete_signature (s:Sign.t) (tb:t): string =
  let ct      = Context.class_table tb.c in
  Class_table.string_of_complete_signature s (tvs tb) ct

let signature_string (tb:t): string =
  let s       = signature tb in
  string_of_signature s tb

let substitution_string (tb:t): string =
  let sub_lst  = Array.to_list (TVars_sub.args tb.tvars)
  and ntvs     = count tb
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
  let ct      = Context.class_table tb.c in
  Class_table.string_of_concepts (TVars_sub.tvars tb.tvars) ct


let string_of_tvs (tvs:Tvars.t) (tb:t): string =
  let ct  = Context.class_table tb.c in
  Class_table.string_of_tvs tvs ct


let string_of_tvs_sub (tb:t): string =
  let ct  = Context.class_table tb.c in
  Class_table.string_of_tvs_sub tb.tvars ct




let add_local (ntvs:int) (tb:t): unit =
  tb.tvars <- TVars_sub.add_local ntvs tb.tvars;
  tb.sign  <- Sign.up ntvs tb.sign

let remove_local (ntvs:int) (tb:t): unit =
  (* signature is irrelevant *)
  tb.tvars <- TVars_sub.remove_local ntvs tb.tvars


let add_fgs (tb:t): unit =
  let tvars_sub = Context.type_variables tb.c in
  let n = TVars_sub.count_fgs tvars_sub - TVars_sub.count_fgs tb.tvars
  and start = TVars_sub.count tb.tvars
  in
  tb.tvars <- TVars_sub.add_fgs tvars_sub tb.tvars;
  tb.sign  <- Sign.up_from n start tb.sign


let remove_fgs (tb:t): unit =
  (* signature is irrelevant *)
  tb.tvars <- TVars_sub.remove_fgs (Context.type_variables tb.c) tb.tvars


let has_sub (i:int) (tb:t): bool = TVars_sub.has i tb.tvars

let get_sub (i:int) (tb:t): type_term = TVars_sub.get i tb.tvars


let do_sub_var (i:int) (j:int) (tb:t): unit =
  (** Substitute the variable [i] by the variable [j] or vice versa, neither
      has substitutions *)
  assert (not (has_sub i tb));
  assert (not (has_sub j tb));
  if i=j then ();
  let add_sub (i:int) (j:int): unit =
    TVars_sub.add_sub i (Variable j) tb.tvars
  in
  let cnt_loc = count_local tb in
  let lo,hi = if i < j then i,j else j,i in
  if hi < cnt_loc || lo < cnt_loc then
    add_sub lo hi
  else begin
    assert (cnt_loc <= i);
    assert (cnt_loc <= j);
    let cpt_i, cpt_j = concept i tb, concept j tb in
    if satisfies cpt_j cpt_i tb then
      add_sub i j
    else if satisfies cpt_i cpt_j tb then
      add_sub j i
    else
      raise Not_found
  end



let add_sub (i:int) (t:term) (tb:t): unit =
  assert (not (has_sub i tb));
  TVars_sub.add_sub i t tb.tvars



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
  and nall  = TVars_sub.count_all tb.tvars
  and nloc  = count_local tb
  in
  let pred_idx = nall + Class_table.predicate_index
  and func_idx = nall + Class_table.function_index
  and dum_idx  = nall + Class_table.dummy_index
  in
  let rec uni (t1:term) (t2:term) (nb:int): unit =
    let rec do_sub0 (i:int) (t:type_term) (nb:int): unit =
      let i,t = i-nb, Term.down nb t in
      if has_sub i tb then
        uni t (get_sub i tb) 0
      else
        match t with
          Variable j when j < nvars ->
            do_sub1 i j
        | _ ->
            if i < nloc || satisfies t (concept i tb) tb then
              add_sub i t tb
            else
              raise Not_found
    and do_sub1 (i:int) (j:int): unit =
      assert (not (has_sub i tb));
      if not (has_sub j tb) then
        do_sub_var i j tb
      else if i < nloc then
        add_sub i (Variable j) tb
      else
        do_sub0 i (get_sub j tb) 0
    in
    let do_dummy
        (dum_args:type_term array)
        (j:int) (j_args:type_term array): unit =
      assert (Array.length dum_args = 2);
      if j = pred_idx then begin
        assert (Array.length j_args = 1);
        uni dum_args.(0) j_args.(0) nb
      end else if j = func_idx then begin
        assert (Array.length j_args = 2);
        uni dum_args.(0) j_args.(0) nb;
        uni dum_args.(1) j_args.(1) nb
      end else
        raise Not_found
    in
    match t1,t2 with
      Variable i, _ when nb<=i && i<nb+nvars ->
        do_sub0 i t2 nb
    | _, Variable j when nb<=j && j<nb+nvars ->
        do_sub0 j t1 nb
    | Variable i, Variable j ->
        assert (i<nb||nb+nvars<=i);
        assert (j<nb||nb+nvars<=j);
        if i=j then
          ()
        else
          raise Not_found
    | Application(Variable i,args1),
          Application(Variable j,args2) when i=dum_idx || j=dum_idx ->
        if i = dum_idx then
          do_dummy args1 j args2
        else
          do_dummy args2 i args1
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
  try
    uni t1 t2 0
  with Term_capture ->
    assert false



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
  let ntvs  = count tb
  and nfgs  = Context.count_formal_generics tb.c
  and sign  = Sign.make_const tp
  in
  Class_table.downgrade_signature (ntvs+nfgs) sign nargs



let to_dummy (sign:Sign.t) (tb:t): type_term =
  assert (Sign.has_result sign);
  let n = Sign.arity sign in
  assert (0 < n);
  let ntvs_all = count tb + Context.count_formal_generics tb.c in
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
  let ntvs_all = count tb + Context.count_formal_generics tb.c in
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
    (tvs:Tvars.t)
    (s:Sign.t)
    (tb:t): t =
  assert (not (Tvars.count_local tvs > 0 && Tvars.count_global tvs > 0));
  let tb = add_global (Tvars.concepts tvs) tb (* empty, if [tvs] doesn't come from
                                                 global *)
  in
  (* If [i] comes from a global environment, then it has no local type
     variables and space must be made for all type variables (locals and
     globals) of [tb.tvars]. ??? Formal generics ???

     If [i] comes from a local environment then it has no global type
     variables. But the locals already in coincide with the locals of
     [tb.tvars]. Space has to be made for all type variables (globals
     and locals) of [tb.tvars] which are not yet in [tvs].
   *)
  let nloctb  = TVars_sub.count_local  tb.tvars
  and nglobtb = TVars_sub.count_global tb.tvars
  and nfgstb  = TVars_sub.count_fgs    tb.tvars
  and nloc    = Tvars.count_local  tvs
  and nglob   = Tvars.count_global tvs
  and nfgs    = Tvars.count_fgs    tvs
  in
  assert (nloc=0 || nglob=0);
  assert (nloc <= nloctb);
  assert (nfgs=0 ||  nfgs=nfgstb);
  assert (nglob <= nglobtb);
  let s = Sign.up_from (nfgstb-nfgs) (nloc+nglob) s in
  let s = Sign.up_from (nglobtb-nglob) nloc s       in
  let s = Sign.up (nloctb-nloc) s in
  unify_sign tb.sign s tb;
  {tb with tlist = (Variable i)::tb.tlist}




let expect_function (nargs:int) (tb:t): unit =
  (** Convert the currently expected signature to a function signature
      with [nargs] arguments and add to the type variables [nargs] fresh
      type variables, one for each argument.
   *)
  add_local nargs tb;
  let s = tb.sign in
  let s =
    if Sign.is_constant s then s
    else begin
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
      Sign.make_const (to_dummy s tb)
    end
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
  remove_local nargs tb



let expect_lambda (ntvs:int) (tb:t): unit =
  assert (Sign.has_result tb.sign);
  add_local ntvs tb;
  add_fgs tb;
  assert (TVars_sub.count_local tb.tvars =
          TVars_sub.count_local (Context.type_variables tb.c));
  assert (TVars_sub.count_fgs tb.tvars =
          TVars_sub.count_fgs (Context.type_variables tb.c));
  let rt = Sign.result tb.sign in
  if not (Sign.is_constant tb.sign) then
    tb.sign <- Sign.make_const rt
  else
    tb.sign <-
      try
        let ntvs = (count tb) + (Context.count_formal_generics tb.c) in
        Sign.make_const (Class_table.result_type_of_compound rt ntvs)
      with Not_found ->
        assert false (* cannot happen *)



let complete_lambda (ntvs:int) (names:int array) (tb:t): unit =
  assert (tb.tlist <> []);
  let nargs = Array.length names in
  assert (0 < nargs);
  remove_fgs tb;
  remove_local ntvs tb;
  let t = List.hd tb.tlist in
  tb.tlist <- List.tl tb.tlist;
  tb.tlist <- Lam (nargs, names, t) :: tb.tlist


let check_type_variables (inf:info) (tb:t): unit =
  let ntvs_ctxt = Context.count_type_variables tb.c
  and ntvs_loc  = TVars_sub.count_local tb.tvars in
  assert (ntvs_ctxt = ntvs_loc);
  let ntvs_all = count tb + Context.count_formal_generics tb.c in
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


let update_term (tb:t): unit =
  assert (Mylist.is_singleton tb.tlist);
  let ft = Context.feature_table tb.c
  and tvs = TVars_sub.tvars tb.tvars
  in
  let rec upd (t:term) (nargs:int) (nglob:int): int*term =
    match t with
      Variable i when i < nargs ->
        nglob, t
    | Variable i ->
        let i = i - nargs in
        let nfgs = Feature_table.count_fgs i ft in
        begin
          try
            let anchor = Feature_table.anchor i ft in
            assert (anchor < nfgs);
            let tv  = Tvars.count_local tvs + nglob + anchor in
            assert (tv < Tvars.count_all tvs);
            let tvtp = TVars_sub.get_star tv tb.tvars in
            let pcls = Tvars.principal_class tvtp tvs in
            let i_var = Feature_table.variant i pcls ft in
            nglob+nfgs, Variable (nargs + i_var)
          with Not_found ->
            nglob+nfgs, t
        end
    | Application (f,args) ->
        let nglob,f = upd f nargs nglob in
        let nglob,arglst = Array.fold_left
            (fun (nglob,lst) t ->
              let nglob,t = upd t nargs nglob in
              nglob, t::lst)
            (nglob,[])
            args
        in
        let args = Array.of_list (List.rev arglst) in
        nglob, Application (f,args)
    | Lam (n,nms,t) ->
        let nglob, t = upd t (nargs+n) nglob in
        nglob, Lam (n,nms,t)
  in
  let nargs = Context.count_arguments tb.c
  and t     = List.hd tb.tlist in
  let nglob, t = upd t nargs 0 in
  assert (nglob = TVars_sub.count_global tb.tvars);
  tb.tlist <- [t]



let result (tb:t): term * TVars_sub.t =
  (** Return the term and the calculated substitutions for the type
      variables *)
  assert (Mylist.is_singleton tb.tlist);
  List.hd tb.tlist, tb.tvars
