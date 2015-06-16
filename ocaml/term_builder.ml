(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Signature
open Term
open Support
open Container
open Printf

type t = {mutable tlist: (term*Tvars.t*Sign.t) list; (* term, count_all, sign *)
          mutable stack: (Tvars.t*Sign.t) list;
          mutable sign:  Sign.t;  (* expected *)
          mutable tvars: TVars_sub.t;
          mutable norm:  bool; (* term is specialized and normalized *)
          mutable c: Context.t}

(* The type variables of the term builder and the context differ.

   context:          locs         +           fgs
   builder:  blocs + locs + globs + garbfgs + fgs

   Transformation from the context to the builder means
   - make space for the additional locals at the bottom
   - make space for the globals and the garbage formal generics in the middle

   Note: The context never has global type variables. These appear only in the
   term builder from the global functions with formal generics.
*)

let class_table (tb:t): Class_table.t = Context.class_table tb.c

let signature (tb:t): Sign.t = tb.sign

let count_local (tb:t): int  = TVars_sub.count_local tb.tvars

let count_global (tb:t): int = TVars_sub.count_global tb.tvars

let count (tb:t): int = TVars_sub.count tb.tvars

let count_fgs (tb:t): int = TVars_sub.count_fgs tb.tvars

let count_all (tb:t): int = TVars_sub.count_all tb.tvars

let count_terms (tb:t): int = List.length tb.tlist

let concept (i:int) (tb:t): type_term = TVars_sub.concept i tb.tvars

let tvars (tb:t): Tvars.t  = TVars_sub.tvars tb.tvars

let has_term (tb:t): bool = tb.tlist <> []

let head_term (tb:t): term =
  assert (has_term tb);
  let t,_,_  = List.hd tb.tlist in
  t

let head_signature (tb:t): Sign.t =
  assert (has_term tb);
  let _,_,s = List.hd tb.tlist in
  s

let satisfies (t1:type_term) (t2:type_term) (tb:t): bool =
  let ct  = class_table tb
  and tvs = tvars tb in
  Class_table.satisfies t1 tvs t2 tvs ct


let string_of_term (t:term) (tb:t): string =
  Context.string_of_term t tb.norm 0 tb.c


let string_of_head_term (tb:t): string =
  assert (has_term tb);
  string_of_term (head_term tb) tb


let string_of_type (tp:type_term) (tb:t): string =
  let ct = class_table tb in
  Class_table.string_of_type tp (tvars tb) ct


let string_of_signature (s:Sign.t) (tb:t): string =
  let ct      = Context.class_table tb.c in
  Class_table.string_of_signature s (tvars tb) ct


let string_of_head_signature (tb:t): string =
  assert (has_term tb);
  string_of_signature (head_signature tb) tb

let string_of_complete_signature (s:Sign.t) (tb:t): string =
  let ct      = Context.class_table tb.c in
  Class_table.string_of_complete_signature s (tvars tb) ct

let string_of_complete_signature_sub (s:Sign.t) (tb:t): string =
  let ct      = Context.class_table tb.c in
  Class_table.string_of_complete_signature_sub s tb.tvars ct

let signature_string (tb:t): string =
  let s       = signature tb in
  string_of_signature s tb

let complete_signature_string (tb:t): string =
  let s = signature tb in
  string_of_complete_signature s tb

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



let upgrade_signature (s:Sign.t) (is_pred:bool) (tb:t): Sign.t =
  (* The signature [s] upgraded to a predicate or a function. *)
  let ntvs = count_all tb  in
  let tp = Class_table.upgrade_signature ntvs is_pred s in
  Sign.make_const tp



let locals_added (ntvs:int) (tb:t): t =
  {tb with
   tvars = TVars_sub.add_local ntvs tb.tvars;
   sign  = Sign.up ntvs tb.sign}


let add_local (ntvs:int) (tb:t): unit =
  let tb1 = locals_added ntvs tb in
  tb.tvars <- tb1.tvars;
  tb.sign  <- tb1.sign


let remove_local (ntvs:int) (tb:t): unit =
  (* signature is irrelevant *)
  tb.tvars <- TVars_sub.remove_local ntvs tb.tvars


let fgs_added (nfgs:int) (tb:t): t =
  (* Add [nfgs] additional formal generics from the context.

     context:    loc          +         fgs1 + fgs2

     builder:    loc  + glob  +  garb +        fgs2

   *)
  let nlocs     = count_local tb in
  let tvars_sub = Context.type_variables tb.c in
  assert (nlocs = TVars_sub.count_local tvars_sub);
  assert (nfgs <= TVars_sub.count_fgs tvars_sub);
  let nfgs2 = TVars_sub.count_fgs tvars_sub - nfgs in
  assert (nfgs2 <= count_fgs tb);
  let ngarb = count_fgs tb - nfgs2 in
  let start = count tb + ngarb
  in
  {tb with
   sign  = Sign.up_from nfgs start tb.sign;
   tvars = TVars_sub.add_fgs nfgs tvars_sub tb.tvars}


let add_fgs (nfgs:int) (tb:t): unit =
  let tb1 = fgs_added nfgs tb in
  tb.sign  <- tb1.sign;
  tb.tvars <- tb1.tvars





let has_sub (i:int) (tb:t): bool = TVars_sub.has i tb.tvars

let get_sub (i:int) (tb:t): type_term = TVars_sub.get i tb.tvars


let do_sub_var (i:int) (j:int) (tb:t): unit =
  (** Substitute the variable [i] by the variable [j] or vice versa, neither
      has substitutions *)
  assert (not (has_sub i tb));
  assert (not (has_sub j tb));
  if i=j then
    ()
  else
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


let is_anchor (i:int) (tb:t): bool =
  assert (i < count tb);
  TVars_sub.anchor i tb.tvars = i

let dummy_index (tb:t): int =
  count_all tb + Class_table.dummy_index

let predicate_index (tb:t): int =
  count_all tb + Class_table.predicate_index

let function_index (tb:t): int =
  count_all tb + Class_table.function_index


let transformed_type (tp:term) (tb:t): type_term =
  (* The type 'tp' valid in the context of 'tb' transformed into the term builder

     tvs context:         loc      +              fgs
     builder:      bloc + loc  + glob  +   garb + fgs
  *)
  let ntvs_ctxt = Context.count_type_variables tb.c
  and ntvs_loc  = count_local tb
  and nfgs_ctxt = Context.count_formal_generics tb.c
  and nfgs      = count_fgs tb
  and nglobs    = count_global tb
  in
  assert (ntvs_ctxt <= ntvs_loc);
  assert (nfgs_ctxt <= nfgs);
  let tp = Term.upbound (nfgs-nfgs_ctxt+nglobs) ntvs_loc tp in
  Term.up (ntvs_loc-ntvs_ctxt) tp


let substituted_type (tp:term) (tb:t): type_term =
  (* The type 'tp' valid in the in the term builder 'tb' with all substitutions done.
   *)
  TVars_sub.sub_star tp tb.tvars


let substituted_signature (tb:t): Sign.t =
  (* The required signature of the term builder [tb] with all substitutions done..
   *)
  Sign.map (fun t -> substituted_type t tb) tb.sign


let string_of_reduced_substituted_signature (tb:t): string =
  let ct = class_table tb
  and s  = substituted_signature tb
  and tvs = tvars tb in
  Class_table.string_of_reduced_complete_signature s tvs ct


let variable_type (i:int) (tb:t): type_term =
  assert (i < Context.count_variables tb.c);
  transformed_type (Context.variable_type i tb.c) tb


let context_signature (tb:t): Sign.t =
  (* The signature of the context transformed into the environment of the term
     builder [tb].

     context:           loc          +         fgs

     builder:    bloc + loc  + glob  +  garb + fgs
   *)
  let s = Context.signature tb.c in
  Sign.map (fun t -> transformed_type t tb) s


let substituted_context_signature (tb:t): Sign.t =
  let s = Context.signature tb.c in
  Sign.map (fun t -> substituted_type (transformed_type t tb) tb) s


let to_tuple (args:type_term array) (tb:t): type_term =
  Class_table.to_tuple (count_all tb) 0 args

let boolean_type (tb:t): type_term =
  Variable (count_all tb + Class_table.boolean_index)

let upgrade_dummy (i:int) (t:term) (tb:t): unit =
  (* Upgrade a potential dummy in the type variable [i] to a predicate or a
  function, if possible. *)
  assert (i < count tb);
  assert (is_anchor i tb);
  assert (has_sub i tb);
  let nall = count_all tb in
  let t_i = get_sub i tb
  and t   = TVars_sub.sub_star t tb.tvars
  in
  let update_with t =
    if i < count_local tb || satisfies t (concept i tb) tb then
      TVars_sub.update_sub i t tb.tvars
    else
      raise Not_found
  in
  match t_i, t with
    VAppl(idx1, args1),
    VAppl(idx2, args2)
    when idx1 = nall + Class_table.dummy_index ->
      if idx2 = nall + Class_table.predicate_index then
        let t_new = VAppl(idx2, [|args1.(0)|]) in
        update_with t_new
      else if idx2 = nall + Class_table.function_index then
        let t_new = VAppl(idx2, args1) in
        update_with t_new
      else if idx2 = nall + Class_table.dummy_index then
        ()
      else
        assert false
  | _ ->
      ()



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
  (*printf "    unify t1 %s\n" (string_of_type t1 tb);
  printf "          t2 %s\n" (string_of_type t2 tb);*)
  let nvars = TVars_sub.count tb.tvars
  and nall  = TVars_sub.count_all tb.tvars
  and nloc  = count_local tb
  in
  let rec uni (t1:term) (t2:term) (nb:int): unit =
    assert (nb = 0);
    let pred_idx = nall + nb + Class_table.predicate_index
    and func_idx = nall + nb + Class_table.function_index
    and dum_idx  = nall + nb + Class_table.dummy_index
    in
    let rec do_sub0 (i:int) (t:type_term) (nb:int): unit =
      (*printf "    do_sub0 i %d, t %s\n" i (string_of_type t tb);*)
      let i,t = i-nb, Term.down nb t in
      let i = TVars_sub.anchor i tb.tvars in
      if has_sub i tb then
        ((*printf "    has_sub %s\n" (string_of_type (get_sub i tb) tb);*)
         uni t (get_sub i tb) 0;
         upgrade_dummy i t tb)
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
      (*printf "    do_sub1 i %d, j %d\n" i j;*)
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
    | VAppl(i,args1), VAppl(j,args2)
      when (i=dum_idx || j=dum_idx) && not (i=dum_idx && j=dum_idx) ->
        if i = dum_idx then
          do_dummy args1 j args2
        else
          do_dummy args2 i args1
    | VAppl(f1,args1), VAppl(f2,args2) ->
        let nargs = Array.length args1 in
        if nargs <> (Array.length args2) then
          raise Not_found;
        uni (Variable f1) (Variable f2) nb;
        for i = 0 to nargs-1 do
          uni args1.(i) args2.(i) nb
        done
    | Lam (_,_,_,_,_), _
    | _ , Lam (_,_,_,_,_) ->
        assert false (* lambda terms not used for types *)
    | _ ->
        raise Not_found
  in
  try
    uni t1 t2 0
  with Term_capture ->
    assert false



let adapt_arity (s:Sign.t) (n:int) (tb:t): Sign.t =
  assert (n < Sign.arity s);
  let args = Sign.arguments s
  and rt   = Sign.result_type s in
  let tup = Class_table.to_tuple (count_all tb) (n-1) args in
  let args =
    Array.init n
      (fun i ->
        if i < n - 1 then args.(i)
        else tup) in
  Sign.make args rt



let align_arity (s1:Sign.t) (s2:Sign.t) (tb:t): Sign.t * Sign.t =
  (* Both have to be constant or callable  *)
  assert (Sign.is_constant s1 = Sign.is_constant s2);
  let n1,n2 = Sign.arity s1, Sign.arity s2 in
  if n1 <> n2 then raise Not_found; (* remove when alignment is activated *)
  if n1 < n2 then
    s1, adapt_arity s2 n1 tb
  else if n2 < n1 then
    adapt_arity s1 n2 tb, s2
  else
    s1,s2



let unify_sign_0
    (sig_req:Sign.t)
    (sig_act:Sign.t)
    (tb:t)
    : unit =
  (*printf "  unify sign 0 req %s\n" (string_of_complete_signature_sub sig_req tb);
  printf "               act %s\n" (string_of_complete_signature_sub sig_act tb);*)
  let sig_req,sig_act = align_arity sig_req sig_act tb in
  let has_res = Sign.has_result sig_req in
  if has_res <> Sign.has_result sig_act then
    raise Not_found;
  if has_res then
    unify (Sign.result sig_req) (Sign.result sig_act) tb;
  for i=0 to (Sign.arity sig_req)-1 do
    unify (Sign.arguments sig_req).(i) (Sign.arguments sig_act).(i) tb
  done


(*
let downgrade (tp:type_term) (nargs:int) (tb:t): Sign.t =
  let ntvs  = count tb
  and nfgs  = Context.count_formal_generics tb.c
  and sign  = Sign.make_const tp
  in
  Class_table.downgrade_signature (ntvs+nfgs) sign nargs
*)


let to_dummy (sign:Sign.t) (tb:t): type_term =
  assert (Sign.has_result sign);
  let n = Sign.arity sign in
  assert (0 < n);
  let ntvs_all = count tb + Context.count_formal_generics tb.c in
  Class_table.to_dummy ntvs_all sign







let unify_sign
    (sig_req:Sign.t)
    (sig_act:Sign.t)
    (tb:t)
    : unit =
  (** Unify the signatures [sig_req] and [sig_act] by adding substitutions
      to [tb] *)
  (*printf "unify sign req %s\n" (string_of_complete_signature_sub sig_req tb);
  printf "           act %s\n" (string_of_complete_signature_sub sig_act tb);*)
  let n_req = Sign.arity sig_req
  and n_act = Sign.arity sig_act
  in
  if n_req > 0 && n_act = 0 then begin
    (*printf ".. sig_req has to be upgraded\n";*)
    let tp_req = to_dummy sig_req tb
    and tp_act = Sign.result sig_act in
    unify tp_req tp_act tb
  end else if n_req = 0 && n_act > 0 then begin
    raise Not_found (* nyi: automatic upgrade of signature, because it is a
                       conversion to a predicate or a function *)
    (*printf ".. sig_act has to be upgraded\n";
    let tp_req = Sign.result sig_req
    and tp_act = to_dummy sig_act tb in
    unify tp_req tp_act tb*)
  end else begin
    (*printf ".. both are constant or callable\n";*)
    unify_sign_0 sig_req sig_act tb
  end





let make (c:Context.t): t =
  (* New accumulator for an expression in the context [c] *)
  assert (Context.has_result c);
  {tlist = [];
   stack = [];
   sign  = Sign.make_const (Context.result_type c);
   tvars = (Context.type_variables c);
   norm  = false;
   c     = c}


let make_boolean (c:Context.t): t =
  let tvs = Context.type_variables c in
  let ntvs = TVars_sub.count_all tvs in
  let bool = Variable (ntvs + Class_table.boolean_index) in
  {tlist = [];
   stack = [];
   tvars = tvs;
   sign  = Sign.make_const bool;
   norm  = false;
   c     = c}



let expect_boolean (tb:t): unit =
  if not (Sign.is_constant tb.sign) then
    raise Not_found
  else
    unify (Sign.result tb.sign) (boolean_type tb) tb



let expect_boolean_expression (tb:t): unit =
  let ntvs = count_all tb in
  let tp   = Variable (ntvs + Class_table.boolean_index) in
  let s    = Sign.make_const tp in
  tb.sign <- s



let globals_added (cs:type_term array) (tb:t): t =
  (** Add the constraints [cs] to the accumulator [tb] *)
  let n = Array.length cs
  and start = TVars_sub.count tb.tvars in
  {tb with
   sign  = Sign.up_from n start tb.sign;
   tvars = TVars_sub.add_global cs tb.tvars}



let anys_added (n:int) (tb:t): t =
  assert (0 <= n);
  let any = Variable (n + Class_table.any_index) in
  let anys = Array.init n (fun i -> any) in
  globals_added anys tb



let pop_term (tb:t): term * Tvars.t * Sign.t =
  assert (tb.tlist <> []);
  let t,tvs,s = List.hd tb.tlist in
  tb.tlist <- List.tl tb.tlist;
  t,tvs,s


let push_expected (tb:t): unit =
  (* Push the expected signature onto the stack *)
  tb.stack <- (tvars tb,tb.sign)::tb.stack


let get_expected (tb:t): unit =
  (* Get the top expected signature from the stack *)
  assert (tb.stack <> []);
  let tvs,s = List.hd tb.stack in
  assert (count_local tb = Tvars.count_local tvs);
  assert (Tvars.count_global tvs <= count_global tb);
  assert (Tvars.count_fgs tvs <= count_fgs tb);
  let n = Tvars.count tvs
  and ndelta = count_all tb - Tvars.count_all tvs in
  let s = Sign.up_from ndelta n s in
  tb.sign <- s


let drop_expected (tb:t): unit =
  (* Drop the top expected signature from the stack *)
  assert (tb.stack <> []);
  tb.stack <- List.tl tb.stack


let add_leaf
    (i:int)
    (tvs:Tvars.t)
    (s:Sign.t)
    (tb:t): t =
  (* If [i] comes from a global environment, then it has no local type
     variables and space must be made for all type variables (locals and
     globals) of [tb.tvars]. ??? Formal generics ???

     If [i] comes from a local environment then it has no global type
     variables. But the locals already in coincide with the locals of
     [tb.tvars]. Space has to be made for all type variables (globals
     and locals) of [tb.tvars] which are not yet in [tvs].

     tvs global:                       glob

     tvs local:         loc      +                        fgs

     builder:    bloc + loc  + glob0           +   garb + fgs

     builder:    bloc + loc  + glob0 + glob    +   garb + fgs
     after add_global
   *)
  assert (not (Tvars.count_local tvs > 0 && Tvars.count_global tvs > 0));
  let tb = globals_added (Tvars.concepts tvs) tb (* empty, if [tvs] doesn't come
                                                    from global *)
  in
  let nloctb  = TVars_sub.count_local  tb.tvars
  and nglobtb = TVars_sub.count_global tb.tvars
  and nfgstb  = TVars_sub.count_fgs    tb.tvars
  and nloc    = Tvars.count_local  tvs
  and nglob   = Tvars.count_global tvs
  and nfgs    = Tvars.count_fgs    tvs
  in
  assert (nloc=0 || nglob=0);
  assert (nloc <= nloctb);
  assert (nfgs <= nfgstb);
  assert (nglob <= nglobtb);
  let s = Sign.up_from (nfgstb-nfgs) (nloc+nglob) s in
  let s = Sign.up_from (nglobtb-nglob) nloc s       in
  let s = Sign.up (nloctb-nloc) s in
  unify_sign tb.sign s tb;
  {tb with tlist = (Variable i, tvars tb, s)::tb.tlist}




let expect_function (nargs:int) (tb:t): unit =
  (** Convert the currently expected signature to a function signature
      with [nargs] arguments and add to the type variables [nargs] fresh
      type variables, one for each argument.
   *)
  add_local nargs tb;
  let s = tb.sign in
  let s =
    if Sign.is_constant s then
      s
    else
      Sign.make_const (to_dummy s tb)
  in
  tb.sign  <- Sign.to_function nargs s



let expect_argument (i:int) (tb:t): unit =
  (** Expect the [i]th argument of a function call [f(a,b,c,...)].  *)
  assert (i < (TVars_sub.count_local tb.tvars));
  tb.sign <- Sign.make_const (TVars_sub.get i tb.tvars)





let complete_function (nargs:int) (tb:t): unit =
  (** Complete the function call [f(a,b,c,...)] with [nargs] arguments. The
      function term and all arguments are on the top of the term list
      [tb.tlist] in reverse order, ie. [tb.tlist = [...,c,b,a,f]. The terms
      are popped of the list, the corresponding function application is
      generated and pushed onto the list and the [nargs] most recent type
      variables are removed.

      Note: The expected signature is no longer valid. This is no problem,
      because either we are ready, or the next action is a further call to
      [complete_function] or a call to [expect_argument]. *)
  let arglst = ref [] in
  for i = 1 to nargs do  (* pop arguments *)
    assert (tb.tlist <> []);
    let t,_,s = List.hd tb.tlist in
    tb.tlist <- List.tl tb.tlist;
    assert (Sign.is_constant s); (* not valid for automatically upgraded
                                    functions! *)
    arglst := t :: !arglst;
  done;
  let f,tvs,fsig = List.hd tb.tlist in
  assert (Tvars.count_all tvs <= count_all tb);
  let fsig = Sign.up_from
      (count_all tb - Tvars.count_all tvs) (count_local tb) fsig in
  tb.tlist <- List.tl tb.tlist;
  let ttp, is_pred  =
    if Sign.is_constant fsig then
      let dum_idx = dummy_index tb
      and f_idx   = function_index tb
      and p_idx   = predicate_index tb in
      let res = TVars_sub.sub_star (Sign.result fsig) tb.tvars in
      match res with
        VAppl(i,args) ->
          let nargs = Array.length args in
          if i = dum_idx || i = f_idx then begin
            assert (nargs = 2); args.(1), false
          end else if i = p_idx then begin
            assert (nargs = 1); boolean_type tb, true
          end else
            assert false (* cannot happen *)
      | _ -> assert false (* cannot happen *)
    else
      TVars_sub.sub_star(Sign.result fsig) tb.tvars, false in
  let t =
    if Sign.is_constant fsig then
      Application (f, Array.of_list !arglst, is_pred)
    else begin
      assert (Sign.arity fsig = nargs);
      assert (Term.is_variable f);
      VAppl(Term.variable f, Array.of_list !arglst)
    end
  in
  let ttp = try Term.down nargs ttp with Not_found -> assert false in
  let s   = Sign.make_const ttp in
  remove_local nargs tb;
  tb.tlist <- (t, tvars tb, s) :: tb.tlist





let expect_lambda (ntvs:int) (is_pred:bool) (c:Context.t) (tb:t): t =
  (* Expect the term of a lambda expression. It is assumed that all local
     variables of the lambda expression have been pushed to the context and
     the argument list of the lambda expression contained [ntvs] untyped
     variables and [nfgs] formal generics. *)
  assert (Sign.has_result tb.sign);
  let nargs = Context.count_last_arguments c
  and nfgs  = Context.count_last_formal_generics c in
  let tb = {tb with c = c} in
  let tb = locals_added ntvs tb in
  let nanys = nargs + if is_pred then 0 else 1 in
  let tb = anys_added nanys tb in
  let tb = fgs_added nfgs tb in
  assert (TVars_sub.count_local tb.tvars =
          TVars_sub.count_local (Context.type_variables tb.c));
  let csig =
    let csig  = context_signature tb
    and start = count tb - nanys in
    assert (Sign.arity csig = nargs);
    for i = 0 to nargs - 1 do
      unify (Sign.arg_type i csig) (Variable (start + i)) tb
    done;
    if not is_pred then
      unify (Sign.result csig) (Variable (start + nargs)) tb;
    csig in
  begin
    assert (Sign.arity csig > 0);
    let upsig = upgrade_signature csig is_pred tb in
    assert (Sign.has_result csig);
    try
      unify_sign tb.sign upsig tb
    with Not_found ->
      raise Not_found
  end;
  tb.sign <- Sign.make_const (Sign.result csig);
  tb





let complete_lambda (ntvs:int) (npres:int) (is_pred:bool) (tb:t): unit =
  assert (tb.tlist <> []);
  let names = Context.local_argnames tb.c
  and c     = Context.pop tb.c in
  let nargs = Array.length names in
  assert (0 < nargs);
  let pop_pres (npres:int): term list =
    let rec pop n lst =
      if n = 0 then lst
      else begin
        assert (tb.tlist <> []);
        let p,_,_ = List.hd tb.tlist in
        tb.tlist <- List.tl tb.tlist;
        pop (n-1) (p::lst)
      end
    in
    List.rev (pop npres [])
  in
  let pres = pop_pres npres in
  let t,ttvs,tsig = List.hd tb.tlist in
  assert (Tvars.count_all ttvs <= count_all tb);
  let tsig =
    Sign.up_from (count_all tb - Tvars.count_all ttvs) (count_local tb) tsig in
  assert (Sign.is_constant tsig);
  tb.tlist <- List.tl tb.tlist;
  let lam = Lam (nargs,names,pres,t,is_pred)
  and s   =
    let argtps = Array.init nargs
        (fun i -> TVars_sub.sub_star (variable_type i tb) tb.tvars) in
    let argtup = to_tuple argtps tb in
    let res = Sign.result tsig in
    let res = TVars_sub.sub_star res tb.tvars in
    let res =
      if is_pred then begin
        assert (res = boolean_type tb);
        VAppl(predicate_index tb,[|argtup|])
      end else
        VAppl(function_index tb, [|argtup;res|])
    in
    let res = try Term.down ntvs res with Term_capture ->
      printf "Term_capture ntvs %d\n" ntvs;
      raise Not_found in
    Sign.make_const res in
  remove_local ntvs tb;
  tb.c     <- c;
  tb.tlist <- (lam, tvars tb, s) :: tb.tlist



let expect_quantified (ntvs:int) (c:Context.t) (tb:t): unit =
  (* Expect the term of a quantified expression. It is assumed that all local
     variables of the quantified expression have been pushed to the context and
     the argument list of the lambda expression contained [ntvs] untyped
     variables and [nfgs] formal generics. *)
  assert (Sign.has_result tb.sign);
  let nfgs = Context.count_last_formal_generics c in
  tb.c <- c;
  add_local ntvs tb;
  add_fgs   nfgs tb;
  assert (TVars_sub.count_local tb.tvars =
          TVars_sub.count_local (Context.type_variables tb.c));
  expect_boolean tb



let complete_quantified (ntvs:int) (is_all:bool) (tb:t): unit =
  assert (tb.tlist <> []);
  let names = Context.local_argnames tb.c in
  let nargs = Array.length names in
  assert (0 < nargs);
  let t,ttvs,tsig = List.hd tb.tlist in
  assert (Tvars.count_all ttvs <= count_all tb);
  let tsig =
    Sign.up_from (count_all tb - Tvars.count_all ttvs) (count_local tb) tsig in
  assert (Sign.is_constant tsig);
  tb.tlist <- List.tl tb.tlist;
  remove_local ntvs tb;
  tb.c <- Context.pop tb.c;
  let qexp =
    if is_all then
      Context.all_quantified nargs names t tb.c
    else Context.some_quantified nargs names t tb.c in
  let nall = count_all tb in
  let tp   = Variable (nall + Class_table.boolean_index) in
  let s    = Sign.make_const tp in
  tb.tlist <- (qexp, tvars tb, s) :: tb.tlist


let complete_if (has_else:bool) (tb:t): unit =
  get_expected tb;
  let args =
    if has_else then begin
      assert (List.length tb.tlist >= 3);
      let t2,_,_ = pop_term tb in
      let t1,_,_ = pop_term tb in
      let cond,_,_ = pop_term tb in
      [|cond;t1;t2|]
    end else begin
      assert (List.length tb.tlist >= 2);
      let t1,_,_ = pop_term tb in
      let cond,_,_ = pop_term tb in
      [|cond;t1|]
    end
  in
  let t = Flow (Ifexp,args) in
  tb.tlist <- (t, tvars tb, tb.sign) :: tb.tlist



let update_called_variables (tb:t): unit =
  (* Arguments of the context might be called. E.g. if [a] is an argument there might
     be a subexpression [a(x)]. This requires that [a] has either a function or a
     predicate type.

     If the argument has predicate type then the predicate flag will be set in the
     application.

     Only arguments of the inner context will be updated and it is assumed that the
     arguments of the inner context have a complete type (no dummy). Variables of
     outer context might still have dummy types.
  *)
  assert (has_term tb);
  let nargs     = Context.count_last_arguments tb.c
  and ntvs_loc  = count_local tb in
  assert (ntvs_loc = Context.count_type_variables tb.c);
  let ntvs_all  = count tb + Context.count_formal_generics tb.c
  in
  let dum_idx = ntvs_all + Class_table.dummy_index
  and f_idx   = ntvs_all + Class_table.function_index
  and p_idx   = ntvs_all + Class_table.predicate_index
  in
  let is_pred i =
    assert (i < nargs);
    let tp = variable_type i tb in
    let tp = TVars_sub.sub_star tp tb.tvars in
    match tp with
      VAppl(idx,_) ->
        assert (idx <> dum_idx);
        assert (idx = p_idx || idx = f_idx);
        idx = p_idx
    | _ ->
        false
  in
  let rec update (t:term) (nb:int): term =
    match t with
      Variable _ ->
        t
    | VAppl (i,args) ->
        let args = Array.map (fun a -> update a nb) args in
        VAppl(i,args)
    | Application (Variable i,args,pr)
      when not pr && nb <= i && i < nb + nargs ->
        let args = Array.map (fun a -> update a nb) args in
        Application (Variable i, args, is_pred (i-nb))
    | Application (f,args,pr) ->
        let f = update f nb
        and args = Array.map (fun a -> update a nb) args in
        Application (f,args,pr)
    | Lam(n,nms,pres,t,pr) ->
        let nb = 1 + nb in
        let t = update t nb
        and pres = List.map (fun p -> update p nb) pres in
        Lam(n,nms,pres,t,pr)
    | QExp(n,nms,t,is_all) ->
        let t = update t (n+nb) in
        QExp(n,nms,t,is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, Array.map (fun a -> update a nb) args)
  in
  let t,nt,s = List.hd tb.tlist in
  tb.tlist <- List.tl tb.tlist;
  tb.tlist <- (update t 0,nt,s) :: tb.tlist



exception Incomplete_type of int

let check_untyped_variables (tb:t): unit =
  let ntvs_loc  = count_local tb in
  assert (ntvs_loc = Context.count_type_variables tb.c);
  let dum_idx  = count_all tb + Class_table.dummy_index in
  for i = 0 to Context.count_last_arguments tb.c - 1 do
    match variable_type i tb with
      Variable j when j < ntvs_loc -> begin
        match TVars_sub.get_star j tb.tvars with
          VAppl(idx,_) when idx = dum_idx ->
            printf "incompled type %d because of dummy\n" i;
            raise (Incomplete_type i)
        | Variable k when k < ntvs_loc ->
            printf "incompled type %d because of local\n" i;
            raise (Incomplete_type i)
        | _ -> ()
      end
    | _ -> ()
  done



let has_dummy (tb:t): bool =
  let n = count tb in
  let nall = count_all tb in
  let dum_idx = nall + Class_table.dummy_index in
  let rec has n =
    if n = 0 then false
    else
      let n = n - 1 in
      match TVars_sub.get n tb.tvars with
        VAppl(idx,_)  when idx = dum_idx -> true
      | _ -> has n
  in
  has n



let specialize_term_0 (tb:t): unit =
  (* Substitute all functions with the most specific ones. E.g. the term builder
     might have used [=] of ANY. But since the arguments are of type LATTICE it
     specializes [=] of ANY to [=] of LATTICE. *)
  assert (Mylist.is_singleton tb.tlist);
  let ft = Context.feature_table tb.c
  and tvs = TVars_sub.tvars tb.tvars
  in
  let rec upd (t:term) (nargs:int) (nglob:int): int*term =
    let var (i:int): int * int =
        let i = i - nargs in
        let nfgs = Feature_table.count_fgs i ft in
        try
          let anchor = Feature_table.anchor i ft in
          if anchor = -1 then
            raise Not_found;
          assert (anchor < nfgs);
          let tv  = Tvars.count_local tvs + nglob + anchor in
          assert (tv < Tvars.count_all tvs);
          let tvtp = TVars_sub.get_star tv tb.tvars in
          let pcls = Tvars.principal_class tvtp tvs in
          let i_var = Feature_table.variant i pcls ft in
          nglob+nfgs, nargs + i_var
        with Not_found ->
          nglob+nfgs, i+nargs
    and upd_args nglob args =
      let nglob,arglst = Array.fold_left
          (fun (nglob,lst) t ->
            let nglob,t = upd t nargs nglob in
            nglob, t::lst)
          (nglob,[])
          args
      in
      nglob, Array.of_list (List.rev arglst)
    in
    match t with
      Variable i when i < nargs ->
        nglob, t
    | Variable i ->
        let nglob, i = var i in
        nglob, Variable i
    | VAppl (i,args) ->
        let nglob, i = var i in
        let nglob, args = upd_args nglob args in
        let t =
          if i = nargs + Feature_table.in_index then begin
            assert (Array.length args = 2);
            Application (args.(1), [|args.(0)|], true)
          end else
            VAppl (i,args)
        in
        nglob, t
    | Application (f,args,pr) ->
        let nglob,f = upd f nargs nglob in
        let nglob, args = upd_args nglob args in
        nglob, Application (f,args,pr)
    | Lam (n,nms,pres,t,pr) ->
        let nargs = n + nargs
        and nglob = n + nglob + if pr then 0 else 1 in
        let nglob,pres_rev =
          List.fold_left
            (fun (nglob,ps) p ->
              let nglob,p = upd p nargs nglob in
              nglob, p::ps)
            (nglob,[])
            pres in
        let pres = List.rev pres_rev in
        let nglob, t = upd t nargs nglob in
        nglob, Lam (n,nms,pres,t,pr)
    | QExp (n,nms,t,is_all) ->
        let nglob, t = upd t (n+nargs) nglob in
        nglob, QExp (n,nms,t,is_all)
    | Flow (ctrl,args) ->
        let nglob,args = upd_args nglob args in
        nglob, Flow (ctrl,args)
  in
  let nargs = Context.count_variables tb.c
  and t,nt,s     = List.hd tb.tlist in
  let nglob, t = upd t nargs 0 in
  if nglob <> TVars_sub.count_global tb.tvars then begin
    printf "specialize_term nglob %d\n" nglob;
    printf "                cnt   %d\n" (TVars_sub.count_global tb.tvars)
  end;
  assert (nglob = TVars_sub.count_global tb.tvars);
  tb.tlist <- [t,nt,s]


let normalize_lambdas (tb:t): unit =
  assert (Mylist.is_singleton tb.tlist);
  let rec norm t nb =
    let norm_args args = Array.map (fun a -> norm a nb) args
    in
    match t with
      Variable i ->
        t
    | VAppl (i,args) ->
        VAppl (i, norm_args args)
    | Application (f,args,pr) ->
        let f    = norm f nb
        and args = norm_args args in
        Context.make_application f args nb pr tb.c
    | Lam (n,nms,pres,t,pr) ->
        let pres = List.map (fun p -> norm p (n+nb)) pres
        and t = norm t (n+nb) in
        Context.make_lambda n nms pres t pr tb.c
    | QExp (n,nms,t,is_all) ->
        QExp (n, nms, norm t (n+nb), is_all)
    | Flow (ctrl,args) ->
        Flow (ctrl, norm_args args)
  in
  let t,nt,s = List.hd tb.tlist in
  let t = norm t 0 in
  tb.tlist <- [t,nt,s]


let specialize_term (tb:t): unit =
  specialize_term_0 tb;
  normalize_lambdas tb;
  tb.norm <- true

let result (tb:t): term * TVars_sub.t =
  (** Return the term and the calculated substitutions for the type
      variables *)
  assert (Mylist.is_singleton tb.tlist);
  let t,_,_ =  List.hd tb.tlist in
  t, tb.tvars




let upgrade_potential_dummy (i:int) (pr:bool) (tb:t): unit =
  (* Check if variable [i] is an untyped variable which has a dummy type. If
     yes, upgrade it to a function or a predicate depending on the flag [pr] *)
  let nall = count_all tb in
  let dum_idx  = nall + Class_table.dummy_index
  and p_idx    = nall + Class_table.predicate_index
  and f_idx    = nall + Class_table.function_index
  and bool_idx = nall + Class_table.boolean_index
  in
  let tp = variable_type i tb in
  match tp with
    Variable i when i < count_local tb ->
      let i  = TVars_sub.anchor i tb.tvars in
      let tp = TVars_sub.get i tb.tvars in
      begin match tp with
        VAppl (j,args) when j = dum_idx ->
          assert (Array.length args = 2);
          assert (not pr || args.(1) = Variable bool_idx);
          let tp =
            if pr then VAppl(p_idx, [|args.(0)|])
            else VAppl (f_idx, args) in
          TVars_sub.update_sub i tp tb.tvars
      | _ ->
          ()
      end
  | _ ->
      ()



let upgrade_required_signature (pr:bool) (tb:t): unit =
  assert (Sign.arity tb.sign = 1);
  assert (Sign.has_result tb.sign);
  let res  = Sign.result tb.sign
  and arg  = Sign.arg_type 0 tb.sign
  and nall = count_all tb in
  let res  = substituted_type res tb
  and arg  = substituted_type arg tb in
  if not (not pr || res = boolean_type tb) then
    printf "upgrade_required pr %b, res is bool %b\n" pr (res = boolean_type tb);
  assert (not pr || res = boolean_type tb);
  let tp =
    if pr then
      let pred_id = nall + Class_table.predicate_index in
      VAppl(pred_id, [|arg|])
    else
      let fun_id = nall + Class_table.function_index in
      VAppl(fun_id, [|arg;res|])
  in
  tb.sign <- Sign.make_const tp



exception Illegal_term

let check_term (t:term) (tb:t): t =
  let rec check (t:term) (tb:t): t =
    let nargs   = Context.count_last_arguments tb.c in
    let upgrade_potential_dummy f pr tb =
      match f with
        Variable i when i < nargs ->
          upgrade_potential_dummy i pr tb
      | _ ->
          ()
    in
    let lambda n nms pres t is_pred tb =
      assert (0 < n);
      assert (Array.length nms = n);
      let nms = [|ST.symbol "$0"|] in
      let ntvs_gap = count_local tb - Context.count_type_variables tb.c
      and is_func = not is_pred in
      let c = Context.push_untyped_with_gap nms is_pred is_func false ntvs_gap tb.c in
      let ntvs    = Context.count_local_type_variables c - ntvs_gap
      in
      let tb = expect_lambda ntvs is_pred c tb in
      let tb = check t tb in
      let rec check_pres (pres:term list) (tb:t): t =
        match pres with
          [] -> tb
        | p::pres ->
            let tb = check p tb in
            check_pres pres tb
      in
      expect_boolean_expression tb;
      let tb = check_pres pres tb in
      begin try
        check_untyped_variables tb
      with Incomplete_type _ ->
        raise Illegal_term
      end;
      begin try
        complete_lambda ntvs 0 is_pred tb
      with Not_found -> assert false
      end;
      tb
    and qlambda n nms t is_all tb =
      assert (0 < n);
      assert (Array.length nms = n);
      let ntvs_gap = count_local tb - Context.count_type_variables tb.c in
      let c = Context.push_untyped_with_gap nms false false false ntvs_gap tb.c in
      let ntvs    = Context.count_local_type_variables c - ntvs_gap
      in
      expect_quantified ntvs c tb;
      let tb = check t tb in
      begin try
        check_untyped_variables tb
      with Incomplete_type _ ->
        raise Illegal_term
      end;
      begin try
        complete_quantified ntvs is_all tb
      with Not_found ->
        assert false
      end;
      tb
    and add_lf i =
      let tvs,s = Context.variable_data i tb.c in
      begin
        try add_leaf i tvs s tb
        with Not_found ->
          let ct = Context.class_table tb.c in
          printf "illegal term \"%s\" %s\n" (string_of_term t tb) (Term.to_string t);
          printf "  type     %s\n"
            (Class_table.string_of_complete_signature s tvs ct);
          printf "  expected %s\n" (complete_signature_string tb);
          raise Illegal_term
      end
    in
    match t with
      Variable i ->
        let tvs,s = Context.variable_data i tb.c in
        begin
          try add_leaf i tvs s tb
          with Not_found ->
            let ct = Context.class_table tb.c in
            printf "illegal term \"%s\" %s\n"
              (string_of_term t tb) (Term.to_string t);
            printf "  type     %s\n"
              (Class_table.string_of_complete_signature s tvs ct);
            printf "  expected %s\n" (complete_signature_string tb);
            raise Illegal_term
        end
    | VAppl(i,args) ->
        let nargs = Array.length args in
        expect_function nargs tb;
        let tb   = add_lf i in
        let tb,_ = Array.fold_left
            (fun (tb,i) a ->
              expect_argument i tb;
              check a tb, i+1)
            (tb,0)
            args
        in
        complete_function nargs tb;
        tb
    | Application (f,args,pr) ->
        let nargs = Array.length args in
        assert (nargs = 1);
        expect_function nargs tb;
        let tb = anys_added 2 tb in
        unify (Sign.arg_type 0 tb.sign) (Variable (count tb - 2)) tb;
        unify (Sign.result tb.sign)     (Variable (count tb - 1)) tb;
        upgrade_required_signature pr tb;
        let tb = check f tb in
        let tb,_ = Array.fold_left
            (fun (tb,i) a ->
              expect_argument i tb;
              check a tb, i+1)
            (tb,0)
            args
        in
        complete_function nargs tb;
        upgrade_potential_dummy f pr tb;
        tb
    | Lam(n,nms,pres,t0,is_pred) ->
        assert (0 < n);
        assert (n = Array.length nms);
        lambda n nms pres t0 is_pred tb
    | QExp(n,nms,t0,is_all) ->
        assert (n = Array.length nms);
        qlambda n nms t0 is_all tb
    | Flow (ctrl,args) ->
        let len = Array.length args in
        assert (2 <= len);
        assert (len <= 3);
        begin
          match ctrl with
            Ifexp ->
              push_expected tb;
              expect_boolean_expression tb;
              let tb = check args.(0) tb in
              get_expected tb;
              let tb = check args.(1) tb in
              let tb =
                if len = 3 then begin
                  get_expected tb;
                  check args.(2) tb
                end else tb in
              drop_expected tb;
              tb
        end
  in
  let depth = Context.depth tb.c in
  let tb = check t tb
  in
  assert (depth = Context.depth tb.c);
  tb


let set_normalized (tb:t): unit =
  tb.norm <- true


let is_valid (t:term) (is_bool: bool) (c:Context.t): bool =
  let tb =
    if is_bool then make_boolean c
    else make c in
  set_normalized tb;
  try
    let _ = check_term t tb in true
  with Illegal_term ->
    false
