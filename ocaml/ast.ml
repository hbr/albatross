(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Proof
open Signature
open Support
open Container
open Printf

module PC = Proof_context

type kind =
    PAxiom
  | PDeferred
  | PNormal


let is_deferred (k:kind): bool =
  match k with
    PDeferred -> true
  | _         -> false



let analyze_imp_opt
    (i:int)
    (info:    info)
    (imp_opt: implementation option)
    (c:Context.t)
    : kind * compound =
  let iface = Context.is_interface_use c || Context.is_interface_check c in
  let kind,is_do,clst =
    match imp_opt with
      None ->
        if Context.is_interface_use c then
          PAxiom,  false, []
        else
          PNormal, false, []
    | Some Impdeferred ->
        if 0 < i then
          error_info info "Deferred not allowed here";
        PDeferred,false, []
    | Some Impbuiltin ->
        if 0 < i then
          error_info info "Axiom not allowed here";
        if iface then
          error_info info "Axiom not allowed in interface file";
        PAxiom,   false, []
    | Some Impevent ->
        error_info info "Assertion cannot be an event"
    | Some (Impdefined (Some locs,is_do,cmp)) ->
        not_yet_implemented info "Local variables in assertions"
    | Some (Impdefined (None,is_do,cmp)) ->
        if Context.is_interface_use c then begin
          if is_do || cmp <> [] then
            error_info info "proof not allowed in interface file";
          PAxiom,  false, []
        end else
          PNormal, false, cmp
  in
  if is_do then
    not_yet_implemented info "Assertions with do block"
  else
    kind, clst


let analyze_body (i:int) (info:info) (bdy: feature_body) (c:Context.t)
    : kind * compound * compound * compound =
  match bdy with
    _, _, [] ->
      error_info info "Assertion must have an ensure clause"
  | rlst, imp_opt, elst ->
      let kind,clst =
        analyze_imp_opt i info imp_opt c
      in
      kind, rlst, clst, elst



let get_boolean_term (ie: info_expression) (pc:Proof_context.t): term =
  let c = Proof_context.context pc in
  Typer.boolean_term ie c

let term_preconditions (info:info) (t:term) (pc:PC.t): term list =
  let c = PC.context pc in
  try
    Context.term_preconditions t c
  with NYI ->
    not_yet_implemented info ("Calculation of the preconditions of " ^
                              (PC.string_of_term t pc))



let prove_insert_close (t:term) (pc:PC.t): unit =
  ignore(Prover.prove_and_insert t pc);
  PC.close pc



let verify_preconditions (t:term) (info:info) (pc:Proof_context.t): unit =
  if PC.is_private pc then
    let pres = term_preconditions info t pc in
    List.iter
      (fun p ->
        try
          ignore (Prover.prove_and_insert p pc)
        with Proof.Proof_failed msg ->
          error_info info ("Cannot prove precondition \"" ^
                           (PC.string_of_term p pc) ^
                           "\"\n  of term \"" ^
                           (PC.string_of_term t pc) ^ "\"" ^
                           msg))
      pres


let get_boolean_term_verified (ie: info_expression) (pc:Proof_context.t): term =
  let t = get_boolean_term ie pc in
  verify_preconditions t ie.i pc;
  t

let add_assumptions_or_axioms
    (lst:compound) (is_axiom:bool) (pc:Proof_context.t): (int*info) list =
  List.map
    (fun ie ->
      let t = get_boolean_term ie pc in
      if is_axiom && Term.is_all_quantified t then
        error_info ie.i "Universal quantification not allowed in ensure clause";
      verify_preconditions t ie.i pc;
      let idx =
        if is_axiom then
          Proof_context.add_axiom t pc
        else begin
          Proof_context.add_assumption t pc
        end in
      idx,ie.i)
    lst


let add_assumptions (lst:compound) (pc:Proof_context.t): unit =
  let _ = add_assumptions_or_axioms lst false pc in ();
  PC.close pc


let add_axioms (lst:compound) (pc:Proof_context.t): (int*info) list =
  add_assumptions_or_axioms lst true pc



let add_proved
    (defer: bool)
    (owner: int)
    (lst: (term*proof_term) list)
    (pc:Proof_context.t)
    : unit =
  Proof_context.add_proved_list defer owner lst pc




let prove_basic_expression (ie:info_expression) (ens:bool) (pc:Proof_context.t)
    : int * info =
  let t = get_boolean_term ie pc in
  if ens && Term.is_all_quantified t then
    error_info ie.i "Universal quantification not allowed in ensure clause";
  verify_preconditions t ie.i pc;
  try
    let res = Prover.prove_and_insert t pc in
    PC.close pc;
    res, ie.i
  with Proof.Proof_failed msg ->
    error_info ie.i ("Cannot prove" ^ msg)



let prove_ensure (lst:compound) (k:kind) (pc:Proof_context.t)
    : (term*proof_term) list =
  let idx_info_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst pc
    | PNormal ->
        List.map (fun ie -> prove_basic_expression ie true pc) lst
  in
  List.map
    (fun (idx,info) ->
      try
        Proof_context.discharged idx pc
      with Not_found ->
        error_info info "The proof uses more variables than the term")
    idx_info_lst



let beta_reduced (t:term) (pc:PC.t): term =
  match t with
    Application(Lam(n,_,_,t0,_,_),args,_) ->
      assert (Array.length args = 1);
      PC.beta_reduce n t0 args 0 pc
  | _ ->
      t


let error_string_case (ps_rev:term list) (goal:term) (pc:PC.t): string =
  let psstr = String.concat "\n"
      (List.rev_map
         (fun ass -> (PC.string_of_term (beta_reduced ass pc) pc))
         ps_rev)
  and tgtstr = PC.string_of_term (beta_reduced goal pc) pc in
  "\n" ^ psstr ^ "\n--------------------------\n" ^ tgtstr


let analyze_type_inspect
    (info:info)
    (id:int)
    (goal:term)
    (pc:PC.t)
    : IntSet.t * int * int * type_term =
  (* constructor set, induction law, induction variable, inductive type *)
  let c     = PC.context pc in
  let nvars = Context.count_variables c
  and ct    = Context.class_table c
  in
  let idx,tvs,s =
    try Context.variable id c
    with Not_found ->
      error_info info ("Unknown variable \"" ^ (ST.string id) ^ "\"") in
  assert (idx < nvars);
  assert (Sign.is_constant s);
  let cons_set, cls, tp =
    let tp = Sign.result s in
    let cls,_ = Class_table.split_type_term tp
    and ntvs = Tvars.count_all tvs in
    let set =
      if cls < ntvs then IntSet.empty
      else
        let cls = cls - ntvs in
        Class_table.constructors cls ct in
    if IntSet.is_empty set then
      error_info info ("Type of \"" ^ (ST.string id) ^ "\" is not inductive");
    set, cls-ntvs, tp
  in
  let ind_idx = PC.add_induction_law tp idx goal pc in
  cons_set,ind_idx,idx,tp



let analyze_type_case_pattern
    (ie:info_expression)
    (cons_set:IntSet.t)
    (tp:type_term)
    (pc:PC.t)
    : int * term * PC.t =
  (* cons_idx, pat, pc1 *)
  let c     = PC.context pc
  and nvars = PC.count_variables pc in
  let pat,nms = Typer.case_variables ie.i ie.v false c in
  let n = Array.length nms in
  let pc1 = PC.push_untyped nms pc in
  let c1  = PC.context pc1 in
  let pat = Typer.typed_term
      (withinfo ie.i pat)
      (Term.up n tp) c1 in
  let invalid_pat () =
    error_info ie.i
      ("Invalid pattern \"" ^ (string_of_expression ie.v) ^ "\"") in
  let cons_idx =
    match pat with
      VAppl(i,args,_) ->
        let argslen = Array.length args in
        if argslen <> n then invalid_pat ();
        for k = 0 to n-1 do
          if args.(k) <> Variable k then invalid_pat ()
        done;
        let cons_idx = i - nvars - n in
        if not (IntSet.mem cons_idx cons_set) then invalid_pat ();
        cons_idx
    | _ ->
        invalid_pat ()
  in cons_idx, pat, pc1


let rec make_proof
    (i:int) (* recursion counter *)
    (entlst: entities list withinfo)
    (kind: kind)
    (rlst: compound)
    (clst: compound)
    (elst: compound)
    (pc:   Proof_context.t)
    : unit =
  let pc1 = Proof_context.push entlst None false false false pc in
  let defer = is_deferred kind
  and owner = Proof_context.owner pc1
  in
  if defer then
    Proof_context.check_deferred pc1;  (* owner class has to be deferred *)
  add_assumptions rlst pc1;
  List.iter (fun ie -> prove_check_expression i ie pc1) clst;
  let pair_lst = prove_ensure elst kind pc1 in
  add_proved defer owner pair_lst pc;
  PC.close pc

and prove_check_expression (i:int) (ie:info_expression) (pc:PC.t): unit =
  let c = PC.context pc in
  match ie.v with
    Expquantified (q,entlst,Expproof(rlst,imp_opt,elst)) ->
      begin
        match q with
          Universal ->
            let kind, clst =
              analyze_imp_opt (i+1) entlst.i imp_opt c
            in
            make_proof (i+1) entlst kind rlst clst elst pc
        | Existential ->
            error_info ie.i "Only \"all\" allowed here"
      end
  | Expproof (rlst,imp_opt,elst) ->
      let kind, clst = analyze_imp_opt (i+1) ie.i imp_opt c in
      make_proof (i+1) (withinfo UNKNOWN []) kind rlst clst elst pc
  | Proofif (thenlist,elsepart,ens) ->
      if not (PC.has_excluded_middle pc) then
        error_info ie.i "Excluded middle law not available";
      if not (PC.has_or_elimination pc) then
        error_info ie.i "Or-elimination law not available";
      prove_if (i+1) ie.i thenlist elsepart ens pc
  | Proofgif (lst,ens) ->
      if not (PC.has_excluded_middle pc) then
        error_info ie.i "Excluded middle law not available";
      if not (PC.has_or_elimination pc) then
        error_info ie.i "Or-elimination law not available";
      prove_gif (i+1) ie.i lst ens pc
  | Proofinspect (e,lst,ens) ->
      begin match e with
        Identifier id ->
          prove_inductive_type (i+1) ie.i id lst ens pc
      | Expcolon (Funapp(Identifier p_id,elem),set) ->
          prove_inductive_set (i+1) ie.i p_id elem set lst ens pc
      | _ ->
          error_info ie.i "Illegal inspect proof"
      end
  | _ ->
      let _ = prove_basic_expression ie false pc in
      ()

and prove_branch
    (rcnt:int) (* recursion counter *)
    (info:info)
    (cond:term)
    (cmp:compound)
    (goal:term)
    (pc:PC.t): unit =
    let pc1 = PC.push_untyped [||] pc in
    ignore(PC.add_assumption cond pc1);
    PC.close pc1;
    List.iter (fun ie -> prove_check_expression rcnt ie pc1) cmp;
    try
      let gidx = Prover.prove_and_insert goal pc1 in
      let t,pt = PC.discharged gidx pc1 in
      ignore(PC.add_proved_0 false (-1) t pt 0 pc);
      PC.close pc
    with Proof.Proof_failed _ ->
      error_info info ("Cannot prove goal \"" ^
                        (PC.string_of_term goal pc1) ^ "\"")

and prove_gif
    (rcnt:int) (* recursion counter *)
    (info:info)
    (lst: (info_expression*compound)list)
    (ens:info_expression)
    (pc:PC.t): unit =
  assert (2 <= List.length lst);
  let rec analyze_conditions lst_rev =
    match lst_rev with
      [ie,cmp] ->
        let cond = get_boolean_term_verified ie pc in
        cond, [cond, withinfo ie.i cond, cmp]
    | (ie,cmp)::lst ->
        let disjunct,lst = analyze_conditions lst in
        let cond = get_boolean_term_verified ie pc in
        let disjunct = PC.disjunction cond disjunct pc in
        disjunct, (disjunct, withinfo ie.i cond, cmp)::lst
    | [] ->
        assert false (* cannot happen *)
  in
  let rec prove lst goal pc =
    match lst with
      [(dis1,cond1,cmp1);(dis2,cond2,cmp2)] ->
        prove_branch rcnt cond1.i cond1.v cmp1 goal pc;
        prove_branch rcnt cond2.i cond2.v cmp2 goal pc
    | (dis,cond,cmp)::rest ->
        not_yet_implemented info "Guarded if proofs with more than two alternatives"
    | _ ->
        assert false (* cannot happen *)
  in
  let disjunct,lst = analyze_conditions lst in
  begin try prove_insert_close disjunct pc
  with Proof.Proof_failed msg ->
    error_info info ("Cannot prove sufficiency of alternatives\n   \"" ^
                     (PC.string_of_term disjunct pc) ^ "\"" ^ msg) end;
  let goal = get_boolean_term_verified ens pc in
  prove lst goal pc


and prove_if
    (rcnt:int) (* recursion counter *)
    (info:info)
    (thenlist: (info_expression*compound)list)
    (elsepart: compound withinfo)
    (ens:info_expression)
    (pc:PC.t): unit =
  let goal = get_boolean_term_verified ens pc in
  let rec prove
      (thenlist:(info_expression*compound)list) (n:int) (pc:PC.t): unit =
    match thenlist with
      [ie,cmp] ->
        let cond = get_boolean_term_verified ie pc in
        let condneg = PC.negation cond pc in
        let em = PC.disjunction cond condneg pc in
        prove_insert_close em pc;
        prove_branch rcnt ie.i cond cmp goal pc;
        prove_branch rcnt elsepart.i condneg elsepart.v goal pc
    | (ie,cmp)::rest ->
        not_yet_implemented ie.i "Conditional proofs with \"elseif\""
    | _ ->
        assert false (* cannot happen *)
  in
  prove thenlist 0 pc



and prove_inductive_set
    (rcnt:int) (* recursion counter *)
    (info:info) (p_id:int) (elem:expression) (set:expression)  (* p(a): exp *)
    (lst:(info_expression*compound)list)
    (ens:info_expression)
    (pc:PC.t)
    : unit =
  assert (not (PC.is_global pc));
  let pc0   = PC.push_untyped [|p_id|] pc in
  let c0    = PC.context pc0 in
  let nvars = Context.count_variables c0 in
  let elem, p, prep, pa_idx, ind_idx, rules, goal, q =
    let bexp = get_boolean_term (withinfo info (Funapp (Expparen set,elem))) pc0
    and goal = Typer.boolean_term ens c0 in
    verify_preconditions bexp info pc0;
    ignore (get_boolean_term
              (withinfo info (Binexp(Eqop,(Identifier p_id),set))) pc0);
    let elem,set1 =
      match bexp with
        Application (f,[|elem|],_) ->
          elem, f
      | _ ->
          assert false (* cannot happen *) in
    let q =
      let tp = Context.variable_type 0 c0 in
      let np = Context.arity_of_downgraded_type tp c0 in
      let nms = anon_argnames np in
      let t0 =
        let ft = Context.feature_table c0 in
        let args = Feature_table.args_of_tuple elem nvars ft in
        let args = Array.map
            (fun arg ->
              match arg with
                Variable i when 1 <= i && i < nvars -> i
              | _ ->
                  error_info info ("\"" ^ (PC.string_of_term arg pc0) ^
                                   "\" is not a variable")) args in
        if np <> Array.length args then
          error_info info ("Must be " ^ (string_of_int np) ^ " arguments");
        let t0 =
          let _,map =
            Array.fold_left
              (fun (j,map) i ->
                assert (i < nvars);
                j+1, IntMap.add i j map)
              (0,IntMap.empty) args in
          Term.lambda_inner_map goal map in
        Feature_table.add_tuple_accessors t0 np nvars ft
      in
      assert (np = Array.length nms);
      let q = Lam (np, nms, [], t0, true,tp) in
      verify_preconditions (Application(q,[|elem|],true)) ens.i pc0;
      PC.close pc0;
      q
    in
    let set2 =
      try Context.inductive_set set1 c0
      with Not_found ->
        error_info info ("\"" ^ (PC.string_of_term set1 pc0) ^
                         "\" does not evaluate to an inductive set") in
    begin match set2 with
      Indset (n,nms,rs) ->
        assert (n = 1);
        let pa = Application(set1,[|elem|],true) in
        let pa_idx =
          try PC.find pa pc0
          with Not_found ->
            error_info info ("\"" ^ (PC.string_of_term elem pc0) ^
                             "\" is not in the inductive set") in
        let rs = Array.map (fun t -> Term.down_from 1 1 t) rs in
        let ind_idx = PC.add_set_induction_law set1 q elem pc0 in
        elem,set2,set1,pa_idx,ind_idx,rs,goal,q
    | _ ->
        error_info info ("\"" ^ (PC.string_of_term set1 pc0) ^
                         "\" does not evaluate to an inductive set")
    end
  in
  let prove_case
      (info:info) (rule:term) (ps:term list) (tgt:term) (cmp:compound)
      (pc1:PC.t) (pc0:PC.t)
      : int =
    List.iter (fun t -> ignore (PC.add_assumption t pc1)) ps;
    PC.close pc1;
    List.iter (fun ie -> prove_check_expression rcnt ie pc1) cmp;
    let gidx =
      try Prover.prove_and_insert tgt pc1
      with Proof.Proof_failed msg ->
        let errstr = error_string_case (List.rev ps) tgt pc1 in
        error_info info ("Cannot prove case \"" ^
                         (PC.string_of_term rule pc0) ^ "\"" ^ msg ^ errstr)
    in
    let t,pt = PC.discharged gidx pc1 in
    PC.add_proved_term t pt false pc0
  in
  let nrules = Array.length rules
  and imp_id = nvars + Feature_table.implication_index in
  let proved =
    List.fold_left
      (fun proved (ie,cmp) ->
        let pc1,rule =
          match ie.v with
            Expquantified(Universal,entlst,e) ->
              PC.push entlst None false false false pc0, e
          | _ ->
              PC.push_untyped [||] pc0, ie.v in
        let c1  = PC.context pc1 in
        let n    = Context.count_last_arguments c1
        and fargs = Context.local_formals c1
        and fgs   = Context.local_fgs c1 in
        let rule0 = Typer.boolean_term (withinfo ie.i rule) c1 in
        let rule  = Term.all_quantified n fargs fgs rule0 in
        let irule =
          let rule =
            Context.prenex_term rule c1 in
          try
            interval_find (fun i -> Term.equivalent rules.(i) rule) 0 nrules
          with Not_found ->
            error_info ie.i "Invalid case"
        in
        let ps,tgt =
          let n1,fargs1,fgs1,ps,tgt = Term.induction_rule imp_id irule p prep q in
          assert (n1 = n); (* The variables might be permuted *)
          let args =
            let usd = Array.of_list (List.rev (Term.used_variables rule0 n)) in
            assert (Array.length usd = n);
            Array.map (fun i -> Variable i) usd in
          let sub t = Term.subst t n args in
          List.map sub ps, sub tgt
        in
        let idx = prove_case ie.i rule ps tgt cmp pc1 pc0 in
        IntMap.add irule idx proved)
      IntMap.empty
      lst
  in
  let ind_idx =
    interval_fold
      (fun ind_idx irule ->
        let rule_idx =
          try
            IntMap.find irule proved
          with Not_found ->
            let n,(nms,tps),fgs,ps,tgt = Term.induction_rule imp_id irule p prep q in
            let nms = Context.unique_names nms c0 in
            let pc1 = PC.push_typed (nms,tps) fgs pc0 in
            (*let pc1 = PC.push_untyped nms pc0 in  (* push_typed !!! *)*)
            prove_case ens.i rules.(irule) ps tgt [] pc1 pc0 in
        PC.add_mp rule_idx ind_idx false pc0
      ) ind_idx 0 nrules in
  let gidx = PC.add_mp pa_idx ind_idx false pc0 in
  let t,pt = PC.discharged gidx pc0 in
  ignore(PC.add_proved_term t pt true pc);
  PC.close pc


and prove_type_case
    (rcnt:int) (* recursion counter *)
    (info:info)
    (cons_idx:int) (pat:term) (cmp:compound)
    (ivar:int) (goal:term)
    (pc1:PC.t) (pc:PC.t)
    : int =
  (* prove one case of an inductive type *)
  let nvars = PC.count_variables pc
  and ft    = PC.feature_table pc in
  let n,_,_,ps_rev,case_goal =
    let t0 = Term.lambda_inner goal ivar
    and tp = assert false in
    let p   = Lam(1,anon_argnames 1,[],t0,true,tp)
    and ags = assert false in
    Feature_table.constructor_rule cons_idx p ags nvars ft in
  assert (n = PC.count_last_arguments pc1);
  List.iter
    (fun ass ->
      ignore (PC.add_assumption ass pc1))
    (List.rev ps_rev);
  PC.close pc1;
  List.iter (fun ie -> prove_check_expression rcnt ie pc1) cmp;
  let gidx =
    try Prover.prove_and_insert case_goal pc1
    with Proof.Proof_failed msg ->
      let errstr = error_string_case ps_rev case_goal pc1 in
      error_info info ("Cannot prove case \"" ^
                       (PC.string_of_term pat pc1) ^
                       "\"" ^ msg ^ errstr)
  in
  let t,pt = PC.discharged gidx pc1 in
  PC.add_proved_term t pt false pc




and prove_inductive_type
    (rcnt:int) (* recursion counter *)
    (info:info) (id:int)
    (lst:(info_expression*compound)list)
    (ens:info_expression)
    (pc:PC.t)
    : unit =
  assert (not (PC.is_global pc));
  let pc_outer = pc in
  let pc = PC.push_untyped [||] pc_outer in
  let c   = PC.context pc in
  let nvars = Context.count_variables c
  and tgt = get_boolean_term ens pc
  and ft  = Context.feature_table c in
  let cons_set,ind_idx,ivar,tp =
    analyze_type_inspect info id tgt pc in
  let proved_cases =
    List.fold_left
      (fun map (ie,cmp) ->
        let cons_idx, pat, pc1 = analyze_type_case_pattern ie cons_set tp pc in
        let idx = prove_type_case rcnt ie.i cons_idx pat cmp ivar tgt pc1 pc in
        IntMap.add cons_idx idx map
      )
      IntMap.empty
      lst in
  let ind_idx =
    IntSet.fold
      (fun cons_idx ind_idx ->
        let idx =
          try
            IntMap.find cons_idx proved_cases
          with Not_found ->
            let n   = Feature_table.arity cons_idx ft in
            let nms = anon_argnames n in
            let pc1 = PC.push_untyped nms pc in
            let pat =
              let args = Array.init n (fun i -> Variable i) in
              Feature_table.feature_call cons_idx (nvars+n) args ft
            in
            prove_type_case rcnt ens.i cons_idx pat [] ivar tgt pc1 pc
        in
        PC.add_mp idx ind_idx false pc)
      cons_set ind_idx in
  let t,pt = PC.discharged ind_idx pc in
  ignore (PC.add_proved_term t pt true pc_outer);
  PC.close pc_outer



let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (pc: Proof_context.t)
    : unit =
  let c = Proof_context.context pc in
  let kind, rlst, clst, elst = analyze_body 0 entlst.i bdy c
  in
  make_proof 0 entlst kind rlst clst elst pc



let function_property_list (lst:compound) (pc:PC.t): term list =
  let pc1 = Proof_context.push_untyped [||] pc in
  List.map
    (fun e ->
      let t = get_boolean_term e pc1 in
      verify_preconditions t e.i pc1;
      let _ = PC.add_assumption t pc1 in
      t)
    lst



let result_term (lst:info_expression list) (context:Context.t): term * info =
  match lst with
    [] -> assert false
  | [e] -> begin
      match e.v with
        Binexp (Eqop, ExpResult,def) ->
          Typer.result_term
            (withinfo e.i def)
            context,
          e.i
      | _ ->
          raise Not_found
  end
  | _ -> raise Not_found




let add_property_assertion
    (idx:int)
    (pc: PC.t): unit =
  try
    let c = PC.context pc in
    let idx = idx + Context.count_variables c in
    let n, nms,  posts = Context.postconditions idx 0 c
    and n1,nms1, pres  = Context.preconditions  idx 0 c in
    assert (n = n1); assert (nms = nms1); assert (n = Array.length nms);
    let pc1 = PC.push_untyped nms pc in
    List.iter (fun t -> let _ = PC.add_assumption t pc1 in ()) pres;
    let lst = List.map (fun t -> PC.add_axiom t pc1) posts in
    let lst = List.map (fun i -> PC.discharged i pc1) lst in
    PC.add_proved_list false (-1) lst pc
  with Not_found ->
    ()



let update_feature
    (info:      info)
    (idx:       int)
    (is_new:    bool)
    (is_export: bool)
    (spec:      Feature.Spec.t)
    (impl:      Feature.implementation)
    (pc:        PC.t): unit =
  assert (not (is_new && is_export));
  let match_impl priv pub =
    match priv,pub with
      Feature.Deferred, Feature.Deferred |
      Feature.Builtin,  Feature.Empty |
      Feature.Empty,    Feature.Empty -> true
    | _ -> false
  in
  let ft          = PC.feature_table pc in
  let update (): unit =
    let is_ghost = Feature_table.is_ghost_specification spec ft in
    if is_ghost && not (Feature_table.is_ghost_function idx ft) then
      error_info info "Must be a ghost function";
    Feature_table.update_specification idx spec ft;
    Inherit.inherit_to_descendants idx info pc
  in
  if PC.is_private pc || not (PC.is_interface_check pc) then begin
    if not is_new then begin
      let spec0,impl0 = Feature_table.private_body idx ft in
      if not (Feature.Spec.private_public_consistent spec0 spec) then
        error_info info "Specification does not match the previous declaration";
      if not ((PC.is_private pc && impl0=impl) || match_impl impl0 impl) then
        error_info info
          "Implementation status does not match the previous declaration";
    end else
      update ()
  end else if is_export then begin
    assert (PC.is_interface_check pc);
    let spec0,impl0 = Feature_table.private_body idx ft in
    if not (match_impl impl0 impl) then
      error_info info "Implementation status is not consistent with private status";
    if not (Feature.Spec.private_public_consistent spec0 spec) then
      error_info info "Specification is not consistent with private specification";
    update ()
  end else begin
    assert (PC.is_interface_check pc);
    let spec0,impl0 = Feature_table.body idx ft in
    if not (Feature.Spec.equivalent spec spec0) then
      error_info info "Specification does not match the previous declaration";
    if not (match_impl impl0 impl) then
      error_info info "Implementation status is not consistent with private status"
  end


(* Functions defined by properties

      f(a:A,b:B,...):RT
          require
              r1; r2; ...
          ensure
              e1; e2; ...   -- 'ei' contains 'Result'
          end

   Proof obligations:

   a) Existence:

         some(x) e1[Result:=x] and e2[Result:=x] and ...

   b) Uniqueness:  (requires that RT derives from ANY)

         all(x,y) e1[Result:=x] ==> e2[Result:=x] ==> ...
                  e2[Result:=y] ==> e2[Result:=y] ==> ...
                  x = y

   Assertions:

        all(a,b,...) r1 ==> r2 ==> ... ==> ei[Result:=f(a,b,...)]
 *)

let adapt_inner_function_term
    (info:info)
    (t:term)
    (nargs:int)
    (pc: PC.t): term =
  (* Functions have a result variable with number [nargs]. However all preconditions,
     definition terms and postconditions finally don't contain the result variable.
     If a function is defined by properties then the variable 'Result' is replaced
     by the corresponding call. I.e. all variables starting from [nargs] are shifted
     down by one. *)
  if PC.has_result_variable pc then
    try
      Term.down_from 1 nargs t
    with Term_capture ->
      error_info info "illegal use of \"Result\""
  else
    t


let is_feature_term_recursive (t:term) (idx:int) (pc:PC.t): bool =
  let c = PC.context pc in
  let nvars = Context.count_variables c in
  let free  = Term.free_variables t nvars in
  IntSet.mem (idx+nvars) free




(* Recursion Checker
   =================

   Valid recursive call: At least one argument of the recursive call is
                         structurally smaller than the original argument.

   Algorithm: We maintain a list of quaduples

       (n,term,level,iarg)

   where (n,term) is a subterm of [iarg] where level indicates which level
   below. [level = 0] indicates that the term is at the same level as the
   argument.
 *)



let check_recursion0 (info:info) (idx:int) (t:term) (pc:PC.t): unit =
  (* Check that the term [t] is a valid recursive definition term for the
     feature [idx], i.e. all recursive calls are valid.

     [idx] is absolute
     [pc] is a valid environment for the term [t]
   *)
  assert (PC.is_toplevel pc);
  let c = PC.context pc
  and ft = PC.feature_table pc in
  let nargs   = Context.count_last_arguments c
  in
  let find (n:int) (t:term) (lst:(int*term*int*int) list): int * int =
    let _,_,level,iarg =
      List.find
        (fun (n0,t0,level,iarg) ->
          assert (n0 <= n);
          Term.up (n-n0) t0 = t)
        lst in
    level,iarg
  in
  let find_opt (n:int) (t:term) (lst:(int*term*int*int) list): (int * int) option =
    try
      let level,iarg = find n t lst in Some(level,iarg)
    with Not_found -> None
  in
  let add_pattern (insp_arr: (int*int) option array) (n:int) (parr:term array)
      (nb:int) (lst:(int*term*int*int) list): (int*term*int*int) list =
    let len_insp = Array.length insp_arr
    and len_pat  = Array.length parr in
    assert (len_pat <= len_insp);
    let len =
      if len_pat < len_insp then len_pat - 1 else len_insp in
    interval_fold
      (fun lst i ->
        match insp_arr.(i) with
          Some (level,iarg) ->
            let plst = Feature_table.pattern_subterms n parr.(i) nb ft in
            List.fold_left
              (fun lst (nall,p,plevel) -> (nall,p,level+plevel,iarg)::lst)
              lst
              plst
        | None ->
            lst)
      lst 0 len
  in
  let rec check (t:term) (nbranch:int) (tlst:(int*term*int*int) list) (c:Context.t)
      : unit =
    let nb = Context.count_variables c in
    let check_args args =
      Array.iter (fun arg -> check arg nbranch tlst c) args in
    match t with
      Variable i when i = idx + nb ->
        assert (nargs = 0);
        assert (Feature_table.arity idx ft = 0);
        error_info info ("Illegal recursive call of the constant " ^
                         Feature_table.feature_name idx ft)
    | Variable i ->
        ()
    | VAppl (i,args,_) when i = idx + nb ->
        if nbranch = 0 then
          error_info info "Recursive call must occur only within a branch";
        let len = Array.length args in
        if len = 0 then
          error_info info ("Illegal recursive call of the constant " ^
                           Feature_table.feature_name idx ft);
        let is_lower_arg i =
          try
            let level,iarg = find nb args.(i) tlst in
            iarg = i && level > 0
          with Not_found ->
            false
        in
        if not (interval_exist is_lower_arg 0 len) then
          error_info info ("Illegal recursive call \"" ^
                           (Context.string_of_term t c) ^ "\"")
    | VAppl (i,args,_) ->
        check_args args
    | Application (f,args,pr) ->
        check f nbranch tlst c;
        check_args args
    | Lam (n,nms,pres,t0,pr,tp) ->
        assert false (* nyi *)
        (*let c0 = Context.push_untyped [|ST.symbol "x"|] c in
        check t0 nbranch tlst c0*)
    | QExp (n,fargs,fgs,t0,_) ->
        assert false (* nyi *)
        (*let c0 = Context.push_untyped nms c in
        check t0 nbranch tlst c0*)
    | Flow (Ifexp, args) ->
        check_args args
    | Flow (Asexp, args) ->
        assert (Array.length args = 2);
        check args.(0) nbranch tlst c
    | Flow (Inspect,args) ->
        let len = Array.length args in
        assert (3 <= len);
        assert (len mod 2 = 1);
        let ncases = len / 2 in
        let insp_arr = Feature_table.args_of_tuple args.(0) nb ft in
        let insp_arr2 = Array.map (fun t -> find_opt nb t tlst) insp_arr in
        let ninsp    = Array.length insp_arr in
        interval_iter
          (fun i ->
            let n,fargs,pat,res = Term.case_split args.(2*i+1) args.(2*i+2) in
            let parr =
              let arr = Feature_table.args_of_tuple pat (n+nb) ft in
              if Array.length arr > ninsp then
                Feature_table.args_of_tuple_ext pat (n+nb) ninsp ft
              else arr in
            let tlst2 = add_pattern insp_arr2 n parr nb tlst in
            assert (Array.length parr = ninsp); (* because only constructors and
                                                   variables are allowed in patterns *)
            let c = Context.push_typed fargs empty_formals c in
            check res (nbranch+1) tlst2 c)
          0 ncases
    | Indset (n,nms,rs) ->
        assert false (* nyi *)
  in
  let nvars = Context.count_variables c in
  let tlst0 =
    interval_fold (fun lst i -> (nvars,Variable i,0,i)::lst) [] 0 nargs in
  check t 0 tlst0 c




let check_recursion (info:info) (idx:int) (t:term) (pc:PC.t): unit =
  if is_feature_term_recursive t idx pc then
    check_recursion0 info idx t pc


let feature_specification
    (info:info)
    (idx: int)
    (nms: int array)
    (reqlst: compound)
    (enslst: compound)
    (pc:PC.t)
    : Feature.Spec.t =
  let nargs = Array.length nms
  and context = PC.context pc in
  let adapt_term t = adapt_inner_function_term info t nargs pc in
  let adapt_list lst = List.map adapt_term lst in
  add_assumptions reqlst pc;
  let pres = PC.assumptions pc in
  if List.exists (fun t -> is_feature_term_recursive t idx pc) pres then
    error_info info "Recursive calls not allowed in preconditions";
  let pres = adapt_list pres in
  match enslst with
    [] ->
      Feature.Spec.make_func_spec nms pres []
  | _ ->
      let prove cond errstring =
        try Prover.prove cond pc
        with Proof.Proof_failed msg ->
          error_info info ("Cannot prove " ^ errstring ^ " of \"Result\"" ^ msg)
      in
      let posts = function_property_list enslst pc in
      if List.exists (fun t -> is_feature_term_recursive t idx pc) pres then
        error_info info "Recursive calls not allowed in postconditions";
      if PC.is_private pc then begin
        let exist = Context.existence_condition posts context in
        let unique =
          try Context.uniqueness_condition posts context
          with Not_found ->
            error_info info "Result type does not inherit ANY"
        in
        prove exist  "existence";
        prove unique "uniqueness"
      end;
      let posts = Context.function_postconditions idx posts context in
      assert (List.for_all (fun t -> is_feature_term_recursive t idx pc) posts);
      let posts = adapt_list posts
      in
      Feature.Spec.make_func_spec nms pres posts


let feature_specification_ast
    (info:info)
    (nms: int array)
    (idx: int)
    (bdy: feature_body option)
    (exp: info_expression option)
    (pc: Proof_context.t): Feature.Spec.t * (info*term) option =
  let nargs = Array.length nms in
  let adapt_term t =
    adapt_inner_function_term info t nargs pc in
  let adapt_list lst = List.map adapt_term lst in
  let feature_spec reqlst enslst =
    feature_specification info idx nms reqlst enslst pc, None in
  let context = PC.context pc in
  match bdy, exp with
    None, None ->
      Feature.Spec.make_empty nms, None
  | None, Some ie ->
      let term = Typer.result_term ie context in
      let term1 = adapt_term term in
      (Feature.Spec.make_func_def nms (Some term1) []), Some(ie.i,term)
  | Some (reqlst,_,enslst), None ->
      feature_spec reqlst enslst
  | Some (reqlst,None,[]), Some ie ->
      let term = Typer.result_term ie context in
      let term1 = adapt_term term in
      add_assumptions reqlst pc;
      let pres = PC.assumptions pc in
      if List.exists (fun t -> is_feature_term_recursive t idx pc) pres then
        error_info info "Recursive calls not allowed in preconditions";
      let pres = adapt_list pres in
      (Feature.Spec.make_func_def nms (Some term1) pres), Some(ie.i,term)
  | Some bdy, Some exp ->
      assert false (* cannot happen *)



let implementation_status
    (info:info)
    (bdy: feature_body option)
    (pc: Proof_context.t): Feature.implementation =
  match bdy with
    None
  | Some (_,None,_) -> Feature.Empty
  | Some (_,Some Impbuiltin,_) -> Feature.Builtin
  | Some (_,Some Impdeferred,_) -> Feature.Deferred
  | Some (_,Some Impevent,_) ->
      not_yet_implemented info "events"
  | Some (_,Some Impdefined(_,_,_),_) ->
      not_yet_implemented info "features with locals"


let check_function_term (idx:int) (opt:(info*term)option) (pc:PC.t): unit =
  match opt with
    None -> ()
  | Some (info,term) ->
      check_recursion info idx term pc;
      verify_preconditions term info pc


let analyze_feature
    (fn: feature_name withinfo)
    (entlst: entities list withinfo)
    (rt: return_type)
    (is_func: bool)
    (bdy: feature_body option)
    (exp: info_expression option)
    (pc: Proof_context.t): unit =
  (*  - Analyze the signature and push into the context
      - Find the index, check if it is a new feature or it is the exportation of an
        already available feature.
      - Add a new feature or export an already available feature.
      - Get the specification of the feature and update the feature.
      - Check the validity of a potential recursion
      - Verify the preconditions of the definition term. (What about precondition
        terms and postconditions).
   *)
  if rt = None then
    not_yet_implemented fn.i "Features without result type";
  let pc1 =
    let rvar = is_func || Option.has rt in
    PC.push entlst rt false is_func rvar pc in
  let nms, sign, tvs =
    let c = Proof_context.context pc1 in
    Context.local_argnames c,
    Context.signature c,
    Context.tvars c
  in
  if Tvars.count tvs > 0 then
    not_yet_implemented entlst.i "Type inference for named functions";
  let ft = Proof_context.feature_table pc in
  let imp  = implementation_status fn.i bdy pc in
  let idx, is_new, is_export =
    try
      let idx = Feature_table.find_with_signature fn.v tvs sign ft in
      let is_export =
        PC.is_interface_check pc && not (Feature_table.is_feature_public idx ft) in
      if is_export && not (Sign.is_ghost sign) &&
        Feature_table.is_ghost_function idx ft
      then
        error_info fn.i "Must be a ghost function";
      if is_export then
        Feature_table.export_feature idx false ft
      else if PC.is_interface_use pc &&
        not (Feature_table.is_feature_public idx ft)
      then
        Feature_table.export_feature idx true ft;
      idx, false, is_export
    with Not_found ->
      let cnt = Feature_table.count ft in
      Feature_table.add_feature fn tvs nms sign imp ft;
      cnt, true, false
  in
  if PC.is_interface_check pc && is_new then
    error_info fn.i "Feature not declared in implementation file";
  let spec,opt = feature_specification_ast fn.i nms idx bdy exp pc1 in
  update_feature fn.i idx is_new is_export spec imp pc;
  check_function_term idx opt pc1;
  if is_new then
    add_property_assertion idx pc




let add_case_axiom (t:term) (pc:Proof_context.t): int =
  Proof_context.add_proved false (-1) t (Proof.Axiom t) pc



let add_case_inversion_equal (idx1:int) (idx2:int) (cls:int) (pc:PC.t): unit =
  (* Add case inversions

     all(args) c1(..) = c2(..)  ==>  false
   *)
  assert (idx1 <> idx2);
  let ft = PC.feature_table pc in
  let tvs1,s1 = Feature_table.signature idx1 ft
  and tvs2,s2 = Feature_table.signature idx2 ft in
  assert (tvs1 = tvs2);
  let n1,n2 = Sign.arity s1, Sign.arity s2 in
  let args1 = Array.init n1 (fun i -> Variable i)
  and args2 = Array.init n2 (fun i -> Variable (n1+i))
  and fgnms,fgcon = Tvars.fgnames tvs1, Tvars.fgconcepts tvs1
  and tps = Array.append (Sign.arguments s1) (Sign.arguments s2) in
  let ags = Array.init (Array.length fgcon) (fun i -> Variable i) in
  let appl idx args = VAppl(n1+n2+idx,args,ags) in
  let t1 = appl idx1 args1
  and t2 = appl idx2 args2
  and eq_id    = n1 + n2 + Feature_table.equality_index cls ft
  and imp_id   = n1 + n2 + Feature_table.implication_index
  in
  let t = Term.binary imp_id
      (VAppl(eq_id, [|t1;t2|], [|Sign.result s1|]))
      (Feature_table.false_constant (n1+n2)) in
  let t = Term.all_quantified
      (n1+n2)
      (standard_argnames (n1+n2),tps)
      (fgnms,fgcon)
      t in
  printf "inversion %s\n" (Proof_context.string_of_term t pc);
  ignore(add_case_axiom t pc)




let add_case_inversion_as (idx1:int) (idx2:int) (cls:int) (pc:PC.t): unit =
  (* Add case inversions

     all(a:T) a as pat1  ==>  a as pat2  ==>  false
   *)
  assert (idx1 <> idx2);
  assert false (* nyi *)
  (*let ft = PC.feature_table pc in
  let make_pattern idx =
    let n = Feature_table.arity idx ft in
    let args = Array.init n (fun i -> Variable i)
    and nms  = standard_argnames n in
    let t    = VAppl(1+n+idx, args) in
    Term.quantified false n nms t
  in
  let pat1 = make_pattern idx1
  and pat2 = make_pattern idx2
  and imp_id   = 1 + Feature_table.implication_index
  and false_const = Feature_table.false_constant 1 in
  let pat1 = Flow(Asexp, [|Variable 0; pat1|])
  and pat2 = Flow(Asexp, [|Variable 0; pat2|]) in
  let t = Term.binary imp_id pat1 (Term.binary imp_id pat2 false_const) in
  let q = Term.all_quantified 1 (standard_argnames 1) t in
  (*printf "inversion %s\n" (PC.string_of_term q pc);*)
  ignore(add_case_axiom q pc)*)




let add_case_inversions
    (cls:  int)
    (clst: int list)
    (pc:   Proof_context.t): unit =
  List.iter
    (fun idx1 ->
      List.iter
        (fun idx2 ->
          if idx1 = idx2 then
            ()
          else begin
            add_case_inversion_equal idx1 idx2 cls pc;
            if idx1 < idx2 then
              add_case_inversion_as idx1 idx2 cls pc
          end)
        clst)
    clst



let add_case_injections
    (clst: int list)
    (pc:Proof_context.t): unit =
  (* Add the injection laws for the constructors [clst]. For each constructor and
     each argument of the constructor there is an injection law of the form:

     all(a1,..,b1,..) c(a1,..) = c(b1,..) ==> ai = bi
   *)
  let ft   = Proof_context.feature_table pc in
  List.iter
    (fun idx ->
      let tvs,s = Feature_table.signature idx ft in
      let fgnms,fgcon = Tvars.fgnames tvs, Tvars.fgconcepts tvs
      and tps = Sign.arguments s
      and rtp = Sign.result s in
      let tps = Array.append tps tps in
      let n = Sign.arity s in
      if n = 0 then
        ()
      else
        let args1 = Array.init n (fun i -> Variable i)
        and args2 = Array.init n (fun i -> Variable (n+i))
        and nms   = standard_argnames (2*n)
        and idx   = 2*n + idx
        and eq_id0 = 2*n  +
            Feature_table.equality_index_of_type rtp tvs ft
        and imp_id = 2*n + Feature_table.implication_index in
        let teq0 =
          let ags   = Array.init (Array.length fgcon) (fun i -> Variable i) in
          let a1,a2 = VAppl(idx,args1,ags), VAppl(idx,args2,ags) in
          VAppl(eq_id0, [|a1;a2|], [|rtp|]) in
        for i = 0 to n - 1 do
          let itp = tps.(i) in
          let eq_id1 = 2*n +
              Feature_table.equality_index_of_type itp tvs ft in
          let teq1 = VAppl(eq_id1, [|Variable i;Variable (n+i)|], [|itp|]) in
          let t = Term.binary imp_id teq0 teq1 in
          let t = Term.all_quantified (2*n) (nms,tps) (fgnms,fgcon) t in
          printf "injection %s\n" (Proof_context.string_of_term t pc);
          ignore(add_case_axiom t pc)
        done)
    clst


let can_be_constructed_without (cls:int) (posset:IntSet.t) (pc:PC.t): bool =
  (* Can the case class [cls] be constructed without actual generics at the
     positions [posset]?  *)
  assert false (* nyi *)
  (*let ct = PC.class_table pc
  and ft = PC.feature_table pc in
  assert (Class_table.is_case_class cls ct);
  let cset = Class_table.constructors cls ct in
  IntSet.exists
    (fun c ->
      let tvs,sign = Feature_table.signature c ft in
      assert (Tvars.count tvs = 0);
      let nfgs = Tvars.count_fgs tvs in
      let fgs =
        match Sign.result sign with
          VAppl(cls2,fgs) ->
            assert (cls2 = cls + nfgs);
            fgs
        | _ ->
            assert false (* cannot happen *) in
      assert (IntSet.cardinal posset = Array.length fgs);
      let fgenset:IntSet.t =
        IntSet.fold
          (fun pos set ->
            assert (pos < Array.length fgs);
            assert (Term.is_variable fgs.(pos));
            IntSet.add (Term.variable fgs.(pos)) set)
          posset
          IntSet.empty in
      List.for_all
        (fun tp ->
            let set = Term.bound_variables tp nfgs in
            IntSet.inter set fgenset = IntSet.empty)
          (Array.to_list (Sign.arguments sign)))
    cset*)



let is_base_constructor (idx:int) (cls:int) (pc:PC.t): bool =
  let ct = PC.class_table pc
  and ft = PC.feature_table pc in
  let tvs,sign = Feature_table.signature idx ft in
  let ntvs     = Tvars.count_all tvs in
  let is_class_involved tp = Tvars.is_class_involved cls tp tvs
  in
  List.for_all
    (fun tp ->
      match tp with
        Variable i when i = cls + ntvs ->
          false
      | VAppl(i,ags,_) when i = cls + ntvs ->
          false
      | VAppl(i,ags,_) ->
          assert (ntvs <= i);
          Class_table.is_case_class (i-ntvs) ct &&
          begin
            let nags = Array.length ags in
            let rec get_posset_from k posset =
              if k = nags then
                posset
              else
                let posset =
                  if is_class_involved ags.(k) then
                    IntSet.add k posset
                  else
                    posset in
                get_posset_from (k+1) posset
            in
            let posset = get_posset_from 0 IntSet.empty in
            can_be_constructed_without (i-ntvs) posset pc
          end
      | _ ->
          true)
    (Array.to_list (Sign.arguments sign))


let creators_check_formal_generics
    (info:info) (clst:int list) (tvs:Tvars.t) (ft:Feature_table.t): unit =
  assert (Tvars.count tvs = 0);
  for i = 0 to (Tvars.count_fgs tvs) - 1 do
    if List.for_all
        (fun cidx ->
          let _,sign = Feature_table.signature cidx ft in
          let argtps = Sign.arguments sign in
          interval_for_all
            (fun j ->
              argtps.(j) <> Variable i)
            0 (Array.length argtps))
        clst then
          let nme = (Tvars.fgnames tvs).(i) in
          error_info info ("Formal generic " ^ (ST.string nme) ^
                           " does not occur in any constructor")
  done



let put_creators
    (cls: int)
    (cls_is_new:bool)
    (tvs: Tvars.t)
    (cls_tp: type_t)
    (creators: (feature_name withinfo * entities list) list withinfo)
    (pc: Proof_context.t)
    : unit =
  let rt = Some (withinfo UNKNOWN (cls_tp,false,false))
  and c    = Proof_context.context pc
  and info = creators.i in
  let ft   = Context.feature_table c in
  let ct   = Feature_table.class_table ft in
  let c0lst, c1lst =
    List.fold_left
      (fun (c0lst,c1lst) (fn,ents) ->
        let formals,res =
          Class_table.analyze_signature (withinfo fn.i ents) rt
            false true false tvs ct in
        let nms, argtps = Myarray.split formals in
        let sign = Sign.make argtps res in
        let cnt = Feature_table.count ft in
        let spec = Feature.Spec.make_func_def nms None []
        and imp  = Feature.Empty in
        let idx, is_new, is_export =
          try
            let idx = Feature_table.find_with_signature fn.v tvs sign ft in
            let is_export =
              PC.is_public pc &&
              not (Feature_table.is_feature_public idx ft) in
            idx, false, is_export
          with Not_found ->
            cnt, true, false
        in
        assert (not cls_is_new || is_new);
        for i = 0 to Sign.arity sign - 1 do
          let arg = Sign.arg_type i sign in
          if not (Class_table.type_descends_from_any arg tvs ct)
          then
            error_info fn.i
              ("Type " ^
               (Class_table.string_of_type arg tvs ct) ^
               " does not inherit ANY")
        done;
        if is_new then
          Feature_table.add_feature fn tvs nms sign imp ft
        else if is_export then
          Feature_table.export_feature idx false ft;
        Feature_table.set_owner_class idx cls ft;
        update_feature fn.i idx is_new is_export spec imp pc;
        let is_base = is_base_constructor idx cls pc in
        if is_base && c1lst <> [] then
          error_info fn.i "Base constructors must be defined before other constructors"
        else if not is_base && c0lst = [] then
          error_info fn.i "No base constructors available";
        if is_base then idx::c0lst, c1lst else c0lst, idx::c1lst)
      ([],[])
      creators.v in
  let clst_rev = c1lst @ c0lst in
  let clst = List.rev clst_rev in
  add_case_inversions cls clst pc;
  add_case_injections clst pc;
  let cset = IntSet.of_list clst in
  if Class_table.is_interface_check ct &&
     Class_table.constructors_priv cls ct <> cset then
    error_info info "Different constructors in implementation file";
  Class_table.set_constructors cset cls ct;
  PC.add_induction_law0 cls pc;
  creators_check_formal_generics creators.i clst tvs ft



let inherit_case_any (cls:int) (cls_tp:type_t) (pc:Proof_context.t): unit =
  let simple_type (str:string): type_t =
    Normal_type ([], ST.symbol str,[])
  in
  begin (* add equality *)
    let argnames = Array.to_list (standard_argnames 2) in
    let fn     = withinfo UNKNOWN (FNoperator Eqop)
    and entlst = withinfo UNKNOWN [Typed_entities (argnames,cls_tp)]
    and rt     =
      Some (withinfo UNKNOWN (simple_type "BOOLEAN",false,false))
    and imp    = if PC.is_public pc then None else Some Impbuiltin
    in
    analyze_feature fn entlst rt true (Some ([],imp,[])) None pc
  end;
  begin (* add reflexivity of equality *)
    let arga     = ST.symbol "a"
    and kind     = PAxiom in
    let entlst = withinfo UNKNOWN [Typed_entities ([arga],cls_tp)]
    and elst   = [withinfo UNKNOWN (Binexp (Eqop,Identifier arga,Identifier arga))]
    in
    make_proof 0 entlst kind [] [] elst pc
  end;
  begin (* inherit ANY *)
    let parent = false, withinfo UNKNOWN (simple_type "ANY"), [] in
    Inherit.inherit_parents cls [parent] pc
  end





let put_class
    (hm:       header_mark withinfo)
    (cn:       classname)
    (fgs:      formal_generics)
    (creators: (feature_name withinfo * entities list) list withinfo)
    (inherits: inherit_clause)
    (pc: Proof_context.t)
    : unit =
  (** Analyze the class declaration [hm,cn,fgs,inherits] and add or update the
      corresponding class.  *)
  assert (Proof_context.is_global pc);
  let ft = Proof_context.feature_table pc in
  let ct = Feature_table.class_table ft in
  let idx,is_new =
    try
      let idx = Class_table.find_for_declaration cn.v ct in
      Class_table.update idx hm fgs  ct;
      idx, false
    with Not_found ->
      let path, cn0 = cn.v in
      if path <> [] then
        error_info cn.i
          ("Class \"" ^ (string_of_classname path cn0) ^ "\" cannot be found");
      let idx = Class_table.count ct in
      Class_table.add hm cn0 fgs ct;
      idx, true
  in
  let cls_tp =
    let lib,cls = cn.v in
    let fgtps   = List.map (fun nme -> Normal_type([],nme,[])) fgs.v in
    Normal_type (lib, cls, fgtps) in
  begin match hm.v with
    Case_hmark ->
      if not (Class_table.has_any ct) then
        error_info hm.i "A case class needs the module \"any\"";
      if not (Class_table.has_predicate ct) then
        error_info hm.i "A case class needs the module \"predicate\"";
      inherit_case_any idx cls_tp pc
  | _ ->
      ()
  end;
  if creators.v <> [] then begin
    match hm.v with
      Case_hmark ->
        let _,tvs = Class_table.class_type idx ct in
        put_creators idx is_new tvs cls_tp creators pc
    | _ ->
        error_info creators.i "Only case classes can have constructors"
  end;
  Inherit.inherit_parents idx inherits pc




let analyze (ast: declaration list) (pc:Proof_context.t): unit =
  let context = Proof_context.context pc in
  let rec analyz (ast: declaration list): unit =
    let one_decl (d:declaration) =
      match d with
        Class_declaration (hm, cname, fgens, creators, inherits) ->
          put_class hm cname fgens creators inherits pc
      | Named_feature (fn, entlst, rt, is_func, body, expr) ->
          analyze_feature fn entlst rt is_func body expr pc
      | Assertion_feature (label, entlst, body) ->
          prove_and_store entlst body pc
      | Formal_generic (name, concept) ->
          Context.put_formal_generic name concept context
      | Class_list lst ->
          not_yet_implemented lst.i "Mutually recursive types"
      | Feature_list lst ->
          not_yet_implemented lst.i "Mutually recursive features"
    in
    match ast with
      [] -> ()
      | f::t -> one_decl f; analyz t
  in
  analyz ast;
  if Proof_context.is_interface_check pc then
    Proof_context.check_interface pc
