(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term
open Signature
open Proof
open Container
open Printf

module PC = Proof_context

type info_term  = term withinfo
type info_terms = info_term list


let term_preconditions (it:info_term) (pc:PC.t): term list =
  let c = PC.context pc in
  try
    Context.term_preconditions it.v c
  with NYI ->
    not_yet_implemented it.i ("Calculation of the preconditions of " ^
                              (PC.string_of_term it.v pc))


let verify_preconditions (it:info_term) (pc:PC.t): unit =
  if PC.is_private pc then begin
    let pres = term_preconditions it pc in
    List.iter
      (fun p ->
        try
          ignore (Prover.prove_and_insert p pc)
        with Proof.Proof_failed msg ->
          error_info it.i ("Cannot prove precondition \"" ^
                           (PC.string_of_term p pc) ^
                           "\"\n  of term \"" ^
                           (PC.string_of_term it.v pc) ^ "\"" ^
                           msg))
      pres
  end


let get_boolean_term (ie: info_expression) (pc:Proof_context.t): info_term =
  let c = PC.context pc in
  let t = Typer.boolean_term ie c in
  withinfo ie.i t


let get_boolean_term_verified
    (ie: info_expression) (pc:Proof_context.t): info_term =
  let it = get_boolean_term ie pc in
  verify_preconditions it pc;
  it




let push
    (entlst: entities list withinfo)
    (rlst: compound)
    (elst: compound)
    (pc:PC.t)
    :  info_terms * info_terms * PC.t =
  let pc1 = PC.push entlst None false false false pc
  in
  let nvars = PC.count_last_arguments pc1
  and nms   = PC.local_argnames pc1
  in
  let get_bool ie = get_boolean_term ie pc1
  in
  let rlst = List.map get_bool rlst
  and elst = List.map get_bool elst
  in
  let used_vars t lst = Term.used_variables_0 t nvars lst
  in
  let used = List.fold_left (fun lst it -> used_vars it.v lst) [] rlst
  in
  let used = List.fold_left (fun lst it -> used_vars it.v lst) used elst
  in
  Array.iteri
    (fun i nme ->
      if not (List.mem i used) then
        error_info entlst.i ("Variable \"" ^ (ST.string nme) ^
                             "\" is not used, neither in assumptions nor in goals")
    )
    nms;
  rlst, elst, pc1


let add_assumptions (rlst:info_terms) (pc:PC.t): unit =
  List.iter
    (fun it ->
      verify_preconditions it pc;
      ignore (PC.add_assumption it.v pc)
    )
    rlst


let add_axiom (it:info_term) (pc:PC.t): int =
  verify_preconditions it pc;
  PC.add_axiom it.v pc


let prove_insert_report (goal:info_term) (pc:PC.t): int =
  try
    Prover.prove_and_insert goal.v pc
  with Proof.Proof_failed msg ->
    error_info goal.i ("Cannot prove" ^ msg)


let prove_insert_close (goal:info_term) (pc:PC.t): int =
  let idx = prove_insert_report goal pc in
  PC.close pc;
  idx




let store_unproved
    (is_defer:bool)
    (elst: info_terms)
    (pc:PC.t)
    : unit =
  assert (PC.is_toplevel pc);
  let idx_lst = List.map (fun it -> add_axiom it pc) elst in
  let pair_lst = List.map (fun idx -> PC.discharged idx pc) idx_lst in
  let anchor =
    if is_defer then
      PC.owner pc
    else
      -1
  in
  let pc0 = PC.pop pc in
  PC.add_proved_list is_defer anchor pair_lst pc0



let one_goal (elst: info_terms): info_term =
  match elst with
    [] ->
      assert false (* cannot happen *)
  | [goal] ->
      goal
  | _ :: tgt2 :: _ ->
      error_info tgt2.i "Only one goal allowed here"




let prove_goal (goal: info_term) (pc:PC.t): unit =
  verify_preconditions goal pc;
  let idx = prove_insert_report goal pc in
  let t,pt = PC.discharged idx pc in
  let pc0 = PC.pop pc in
  ignore (PC.add_proved false (-1) t pt pc0)


let prove_goals (elst: info_terms) (pc:PC.t): unit =
  let idx_list = List.map (fun it -> prove_insert_report it pc) elst in
  let pair_list = List.map (fun idx -> PC.discharged idx pc) idx_list in
  let pc0 = PC.pop pc in
  PC.add_proved_list false (-1) pair_list pc0





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
  let ivar,tvs,s =
    try Context.variable id c
    with Not_found ->
      error_info info ("Unknown variable \"" ^ (ST.string id) ^ "\"") in
  assert (ivar < nvars);
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
  let ind_idx = PC.add_induction_law tp ivar goal pc in
  cons_set,ind_idx,ivar,tp


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
  let c1  = PC.context pc1
  and tp  = Term.up n tp
  in
  let pat = Typer.typed_term (withinfo ie.i pat) tp c1 in
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




let beta_reduced (t:term) (pc:PC.t): term =
  match t with
    Application(Lam(n,_,_,t0,_,tp),args,_) ->
      assert (Array.length args = 1);
      PC.beta_reduce n t0 tp args 0 pc
  | _ ->
      t

type inductive_set_data =
    {pc:    PC.t;
     goal:  term;
     goal_predicate: term; (* [element in goal_predicate] reduces to [goal] *)
     element: term;
     set:     term;        (* as written in the inpect expression *)
     set_expanded: term;   (* the inductive set '{(p): r0, r1, ... }' *)
     rules:  term array;   (* the rules *)
     induction_rule: int;  (* index of the assertion of the induction rule *)
     element_in_set: int   (* assertion which proves [element in set] *)
   }


let analyze_inductive_set
    (info: info)
    (p_nme: int)
    (elem: expression)
    (set:  expression)
    (goal: term)
    (pc:PC.t)
    : inductive_set_data =
  (* Analyzes the outer part of an inductive set proof.

        ensure
            ens
        inspect
            p(elem):  set
        ...

     Introduces an inner context for the varialbe [p] and returns all terms
     within this context.
   *)
  assert (not (PC.is_global pc));
  let pc0   = PC.push_untyped [|p_nme|] pc in
  let c0    = PC.context pc0 in
  let nvars = Context.count_variables c0 in
  let bexp  = Typer.boolean_term (withinfo info (Funapp (Expparen set,elem))) c0
  and goal  = Term.shift 1 1 goal
  in
  verify_preconditions (withinfo info bexp) pc0;
  ignore (Typer.boolean_term (* with that [p] gets a type *)
            (withinfo info
               (Binexp(Eqop,(Identifier p_nme),set))) c0
         );
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
      let tup_tp = Context.type_of_term elem c0
      and args   = Feature_table.args_of_tuple elem nvars ft in
      let args = Array.map
          (fun arg ->
            match arg with
              Variable i when 1 <= i && i < nvars ->
                i
            | _ ->
                error_info info ("\"" ^ (PC.string_of_term arg pc0) ^
                                 "\" is not a variable")
          )
          args
      in
      if np <> Array.length args then
        error_info info ("Must be " ^ (string_of_int np) ^ " arguments");
      let t0 =
        let _,map =
          Array.fold_left
            (fun (j,map) i ->
              assert (i < nvars);
              j+1, IntMap.add i j map
            )
            (0,IntMap.empty)
            args
        in
        Term.lambda_inner_map goal map
      in
      Feature_table.add_tuple_accessors t0 np tup_tp nvars ft
    in
    assert (np = Array.length nms);
    let q = Lam (np, nms, [], t0, true,tp) in
    verify_preconditions (withinfo info (Application(q,[|elem|],true))) pc0;
    PC.close pc0;
    q
  in
  let set2 =
    try Context.inductive_set set1 c0
    with Not_found ->
      error_info info ("\"" ^ (PC.string_of_term set1 pc0) ^
                       "\" does not evaluate to an inductive set") in
  begin match set2 with
    Indset (nme,tp,rs) ->
      let pa = Application(set1,[|elem|],true) in
      let pa_idx =
        try PC.find pa pc0
        with Not_found ->
          error_info info ("\"" ^ (PC.string_of_term elem pc0) ^
                           "\" is not in the inductive set") in
      let rs = Array.map (fun t -> Term.down_from 1 1 t) rs in
      let ind_idx = PC.add_set_induction_law set1 q elem pc0 in
      if PC.is_tracing pc0 then begin
        let prefix = PC.trace_prefix pc0 in
        printf "\n\n";
        printf "%sProof with inductively defined set\n\n" prefix;
        printf "%sensure\n" prefix;
        printf "%s    %s\n" prefix (PC.string_long_of_term goal pc0);
        printf "%sinspect\n" prefix;
        printf "%s    %s(%s): %s\n\n"
          prefix
          (ST.string p_nme)
          (PC.string_of_term elem pc0)
          (PC.string_long_of_term set1 pc0)
      end;
      {pc             = pc0;
       goal           = goal;
       goal_predicate = q;
       set            = set1;
       set_expanded   = set2;
       element        = elem;
       rules          = rs;
       induction_rule = ind_idx;
       element_in_set = pa_idx;
     }
  | _ ->
      error_info info ("\"" ^ (PC.string_of_term set1 pc0) ^
                       "\" does not evaluate to an inductive set")
  end


type inductive_set_case_data =
    {pc:    PC.t;
     goal:  term;
     premises: term list;
   }



let analyze_inductive_set_case
    (case_exp: info_expression)
    (data: inductive_set_data)
    : int * term * term list * term * PC.t =
  (* Analyze the case expression of an inductive set proof.

         case
            all(x,y,..) e0 ==> e1 ==> ... ==> (x,y,...) in p
         require
            p0; p1; ...
         ensure
            target

     - Analyze case expression and find the appropriate rule of the inductive
       set.
     - Push the variables of the case expression into a new context.
     - Compute the case specific induction hypotheses and the goal in the
       new context.

     Return the index of the rule and the rule in the outer context and
     the induction hypotheses and the goal in the new context.
   *)
  let c = PC.context data.pc in
  let rule = Typer.boolean_term case_exp c in
  let irule =
    try
      interval_find
        (fun i -> Term.equivalent data.rules.(i) rule)
        0
        (Array.length data.rules)
    with Not_found ->
      error_info case_exp.i "Invalid case"
  in
  let pc1 =
    let n, args, fgs, t0 =
      try
        Term.all_quantifier_split rule
      with Not_found ->
        0, empty_formals, empty_formals, rule
    in
    assert (fgs = empty_formals);
    PC.push_typed args fgs data.pc
  in
  let imp_id = PC.count_variables data.pc + Feature_table.implication_index in
  let _,_,ps,tgt =
    Term.induction_rule
      imp_id
      irule
      data.set_expanded
      data.set
      data.goal_predicate
  in
  irule, rule, ps, tgt, pc1


let error_string_case (ps_rev:term list) (goal:term) (pc:PC.t): string =
  let psstr = String.concat "\n"
      (List.rev_map
         (fun ass -> (PC.string_of_term (beta_reduced ass pc) pc))
         ps_rev)
  and tgtstr = PC.string_of_term (beta_reduced goal pc) pc in
  "\n" ^ psstr ^ "\n--------------------------\n" ^ tgtstr









let rec prove_and_store
    (entlst: entities list withinfo)
    (rlst: compound)
    (elst: compound)
    (prf:  proof_support_option)
    (pc:PC.t)
    : unit =
  if PC.is_public pc then begin
    match prf with
      None -> ()
    | Some prf when prf.v = PS_Deferred -> ()
    | Some prf ->
        error_info prf.i "Proof not allowed in interface file"
  end;
  let rlst, elst, pc1 = push entlst rlst elst pc in
  add_assumptions rlst pc1;
  let prove_goal () =
    PC.close pc1;
    let goal = one_goal elst in
    verify_preconditions goal pc1;
    let idx =
      try
        prove_one goal.v prf pc1
      with  Proof.Proof_failed msg ->
        error_info goal.i ("Cannot prove" ^ msg)
    in
    let t,pt = PC.discharged idx pc1 in
    ignore (PC.add_proved false (-1) t pt pc)
  in
  match prf with
    None when PC.is_interface_use pc1 ->
      store_unproved false elst pc1
  | None when PC.is_interface_check pc1 ->
      PC.close pc1;
      prove_goals elst pc1
  | None ->
      prove_goal ()
  | Some prf1 ->
      match prf1.v with
        PS_Axiom ->
          store_unproved false elst pc1
      | PS_Deferred ->
          store_unproved true elst pc1
      | _ ->
          prove_goal ()


and prove_one
    (goal:term) (prf:proof_support_option) (pc:PC.t)
    : int =
  (* Prove [goal] with the proof support [prf]. Assume that the preconditions
     of the goal are already verified. *)
  assert (PC.is_private pc);
  match prf with
    None ->
      Prover.prove_and_insert goal pc
  | Some prf ->
      try
        begin
          match prf.v with
            PS_Axiom | PS_Deferred ->
              assert false (* cannot happen *)
          | PS_Sequence lst ->
              prove_sequence lst goal pc
          | PS_If (cond, prf1, prf2) ->
              prove_if prf.i goal cond prf1 prf2 pc
          | PS_Guarded_If (cond1, prf1, cond2, prf2) ->
              prove_guarded_if prf.i goal cond1 prf1 cond2 prf2  pc
          | PS_Inspect (insp, cases) ->
              prove_inspect prf.i goal insp cases pc
        end
      with Proof.Proof_failed msg ->
        error_info prf.i ("Does not prove \"" ^
                          (PC.string_of_term goal pc) ^
                          "\"" ^ msg)


and prove_sequence
    (lst: proof_step list)
    (goal: term)
    (pc: PC.t): int =
  List.iter
    (fun step ->
      begin match step with
        PS_Simple ie ->
          let it = get_boolean_term_verified ie pc in
          ignore (prove_insert_report it pc)
      | PS_Structured (entlst,rlst,tgt,prf) ->
          let rlst, elst, pc1 = push entlst rlst [tgt] pc in
          add_assumptions rlst pc1;
          PC.close pc1;
          let goal = List.hd elst in
          verify_preconditions goal pc1;
          let idx =
            try
              prove_one goal.v prf pc1
            with Proof.Proof_failed msg ->
              error_info goal.i ("Cannot prove" ^ msg)
          in
          let t,pt = PC.discharged idx pc1 in
          ignore(PC.add_proved false (-1) t pt pc)
      end;
      PC.close pc
    )
    lst;
  Prover.prove_and_insert goal pc


and prove_guarded_if
    (info: info)
    (goal: term)
    (c1:info_expression) (prf1:proof_support_option)
    (c2:info_expression) (prf2:proof_support_option)
    (pc:PC.t)
    : int =
  let c1 = get_boolean_term_verified c1 pc
  and c2 = get_boolean_term_verified c2 pc
  in
  let or_exp = PC.disjunction c1.v c2.v pc in
  let or_exp_idx =
    prove_insert_report (withinfo info or_exp) pc
  and or_elim_idx =
    try
      PC.or_elimination pc
    with Not_found ->
      error_info info "Or elimination law not available"
  in
  let result_idx =
    PC.specialized or_elim_idx [|c1.v;c2.v;goal|] [||] 0 pc in
  let result_idx =
    PC.add_mp or_exp_idx result_idx false pc in
  let result_idx =
    let branch1_idx = prove_branch c1 goal prf1 pc in
    PC.add_mp branch1_idx result_idx false pc in
  let branch2_idx = prove_branch c2 goal prf2 pc in
  PC.add_mp branch2_idx result_idx false pc


and prove_if
    (info: info)
    (goal: term)
    (c1:info_expression)
    (prf1:proof_support_option)
    (prf2:proof_support_option)
    (pc:PC.t)
    : int =
  let c1 = get_boolean_term_verified c1 pc
  in
  let c1neg = PC.negation c1.v pc
  in
  let em_idx =
    try
      PC.excluded_middle pc
    with Not_found ->
      error_info info "Excluded middle law not available"
  and or_elim_idx =
    try
      PC.or_elimination pc
    with Not_found ->
      error_info info "Or elimination law not available"
  in
  let spec_em_idx =
    PC.specialized em_idx [|c1.v|] [||] 0 pc
  and spec_or_elim_idx =
    PC.specialized or_elim_idx [|c1.v;c1neg;goal|] [||] 0 pc
  in
  let result_idx =
    PC.add_mp spec_em_idx spec_or_elim_idx false pc in
  let result_idx =
    let branch1_idx = prove_branch c1 goal prf1 pc in
    PC.add_mp branch1_idx result_idx false pc in
  let branch2_idx = prove_branch (withinfo c1.i c1neg) goal prf2 pc in
  PC.add_mp branch2_idx result_idx false pc


and prove_branch
    (cond:info_term) (goal:term) (prf:proof_support_option) (pc:PC.t)
    : int =
  let pc1 = PC.push_empty pc in
  ignore (PC.add_assumption cond.v pc1);
  PC.close pc1;
  let idx = prove_one goal prf pc1 in
  let t,pt = PC.discharged idx pc1 in
  PC.add_proved_term t pt false pc


and prove_inspect
    (info:info)
    (goal:term)
    (insp:info_expression) (cases:one_case list) (pc:PC.t): int =
  match insp.v with
    Identifier id ->
      prove_inductive_type info goal id cases pc
  | Expcolon (Funapp(Identifier p_nme,elem),set) ->
      prove_inductive_set info goal p_nme elem set cases pc
  | _ ->
      error_info info "Illegal induction proof"


and prove_inductive_type
    (info:info)
    (goal:term)
    (nme: int)
    (cases: one_case list)
    (pc:PC.t)
    : int =
  let cons_set, ind_idx, ivar, tp =
    analyze_type_inspect info nme goal pc
  in
  let _,ags = Class_table.split_type_term tp in
  if PC.is_tracing pc then begin
    let prefix = PC.trace_prefix pc in
    printf "\n\n%sInduction Proof\n\n" prefix;
    printf "%sensure\n" prefix;
    printf "%s    %s\n" prefix (PC.string_long_of_term goal pc);
    printf "%sinspect\n" prefix;
    printf "%s    %s\n\n"
      prefix
      (ST.string (Context.argnames (PC.context pc)).(ivar))
  end;
  let pc_outer = pc in
  let pc = PC.push_untyped [||] pc_outer in
  let c  = PC.context pc in
  let nvars = Context.count_variables c
  and ft  = Context.feature_table c in
  let proved_cases =
    (* explicitly given cases *)
    List.fold_left
      (fun map (ie,prf) ->
        let cons_idx, pat, pc1 =
          analyze_type_case_pattern ie cons_set tp pc in
        let idx = prove_type_case cons_idx tp pat prf ivar goal pc1 pc in
        IntMap.add cons_idx idx map
      )
      IntMap.empty
      cases
  in
  let ind_idx =
    (* rest of the cases *)
    IntSet.fold
      (fun cons_idx ind_idx ->
        let idx =
          try
            IntMap.find cons_idx proved_cases
          with Not_found ->
            let n   = Feature_table.arity cons_idx ft
            and ntvs = PC.count_all_type_variables pc
            in
            let nms = anon_argnames n
            and tps = Feature_table.argument_types cons_idx ags ntvs ft
            in
            let pc1 = PC.push_typed (nms,tps) empty_formals pc in
            let pat =
              let args = standard_substitution n in
              Feature_table.feature_call cons_idx (nvars+n) args ags ft
            in
            prove_type_case cons_idx tp pat None ivar goal pc1 pc
        in
        PC.add_mp idx ind_idx false pc
      )
      cons_set
      ind_idx
  in
  let t,pt = PC.discharged ind_idx pc in
  let idx = PC.add_proved_term t pt false pc_outer in
  PC.add_beta_reduced idx false pc_outer



and prove_type_case
    (cons_idx:int)
    (tp:type_term)  (* inductive type in the outer context *)
    (pat:term)      (* in the inner context *)
    (prf:proof_support_option)
    (ivar:int)
    (goal:term)     (* in the outer context *)
    (pc1:PC.t)      (* inner context *)
    (pc:PC.t)       (* outer context *)
    : int =
  (* Prove one case of an inductive type
   *)
  let nvars = PC.count_variables pc
  and ft    = PC.feature_table pc
  and c1    = PC.context pc1
  in
  (* The inner context might have type variables, therefore we adapt only the
     type part to the inner context. *)
  let ntvs_delta = Context.count_local_type_variables c1 in
  let tp1 = Term.up_type ntvs_delta tp
  and goal1 = Term.shift 0 ntvs_delta goal
  in
  let n,_,_,ps_rev,case_goal =
    let t0 = Term.lambda_inner goal1 ivar
    and p_tp = PC.predicate_of_type tp1 pc1 in
    let p   = Lam(1, anon_argnames 1, [], t0, true, p_tp)
    and _, ags = Class_table.split_type_term tp1 in
    Feature_table.constructor_rule cons_idx p ags nvars ft in
  assert (n = PC.count_last_arguments pc1);
  if PC.is_tracing pc then begin
    let prefix = PC.trace_prefix pc1 in
    printf "\n\n%scase\n" prefix;
    printf "%s    %s\n"   prefix (PC.string_long_of_term pat pc1);
    if List.length ps_rev <> 0 then begin
      printf "%srequire\n" prefix;
      List.iter
        (fun t ->
          let t = PC.beta_reduce_term t pc1 in
          printf "%s    %s\n" prefix (PC.string_long_of_term t pc1))
        (List.rev ps_rev)
    end;
    printf "%sensure\n" prefix;
    let t = PC.beta_reduce_term case_goal pc1 in
    printf "%s    %s\n\n" prefix (PC.string_long_of_term t pc1)
  end;
  List.iter
    (fun ass ->
      ignore (PC.add_assumption ass pc1))
    (List.rev ps_rev);
  PC.close pc1;
  let case_goal_idx =
    prove_one case_goal prf pc1
  in
  let t,pt = PC.discharged case_goal_idx pc1 in
  PC.add_proved_term t pt false pc




and prove_inductive_set
    (info:info)
    (goal:term)
    (p_id:int) (elem:expression) (set:expression)  (* p(a): exp *)
    (cases: one_case list)
    (pc:PC.t)
    : int =
  (* Execute a proof with an inductive set:

         ensure
             ens
         inspect
             p(elem): set      -- 'elem in set' must be valid

         case         -- List of zero of more cases, each case represents a
             ...      -- rule for 'p(elem)' to be valid
         proof
             ...

         ...
         end
   *)
  assert (not (PC.is_global pc));
  let data = analyze_inductive_set info p_id elem set goal pc
  in
  let nvars  = PC.count_variables data.pc
  and nrules = Array.length data.rules
  in
  let imp_id = nvars + Feature_table.implication_index in
  let proved =
    List.fold_left
      (fun proved (ie,prf) ->
        let irule, rule, ps,tgt,pc1 =
          analyze_inductive_set_case ie data in
        let idx =
          prove_inductive_set_case ie.i rule ps tgt prf pc1 data.pc
        in
        IntMap.add irule idx proved)
      IntMap.empty
      cases
  in
  let ind_idx =
    interval_fold
      (fun ind_idx irule ->
        let rule_idx =
          try
            IntMap.find irule proved
          with Not_found ->
            let n,(nms,tps),ps,tgt =
              Term.induction_rule
                imp_id
                irule
                data.set_expanded
                data.set
                data.goal_predicate in
            let nms = Context.unique_names nms (PC.context data.pc) in
            let pc1 = PC.push_typed (nms,tps) empty_formals data.pc in
            prove_inductive_set_case
              info data.rules.(irule) ps tgt None pc1 data.pc
        in
        PC.add_mp rule_idx ind_idx false data.pc
      ) data.induction_rule 0 nrules in
  let gidx = PC.add_mp data.element_in_set ind_idx false data.pc in
  let t,pt = PC.discharged gidx data.pc in
  let idx = PC.add_proved_term t pt false pc in
  PC.add_beta_reduced idx false pc


and prove_inductive_set_case
    (info:info)
    (rule:term)                   (* in the outer context *)
    (ps: term list) (tgt: term)   (* in the inner context *)
    (prf: proof_support_option)
    (pc1:PC.t)                    (* inner context *)
    (pc0:PC.t)                    (* outer context *)
    : int =
  if PC.is_tracing pc1 then begin
    let prefix = PC.trace_prefix pc0 in
    printf "\n\n%scase\n" prefix;
    printf "%s    %s\n" prefix (PC.string_long_of_term rule pc0);
    printf "%srequire\n" prefix;
    List.iter
      (fun t -> printf "%s    %s\n" prefix (PC.string_long_of_term t pc1))
      ps;
    printf"%sensure\n" prefix;
    printf"%s    %s\n\n" prefix (PC.string_long_of_term tgt pc1);
  end;
  List.iter (fun t -> ignore (PC.add_assumption t pc1)) ps;
  PC.close pc1;
  let gidx =
    try
      prove_one tgt prf pc1
    with Proof.Proof_failed msg ->
      let errstr = error_string_case (List.rev ps) tgt pc1 in
      error_info info ("Cannot prove case \"" ^
                       (PC.string_of_term rule pc0) ^ "\"" ^ msg ^ errstr)
  in
  let t,pt = PC.discharged gidx pc1 in
  PC.add_proved_term t pt false pc0
  (*
  List.iter (fun ie -> prove_check_expression rcnt ie pc1) cmp;
  let gidx =
    try Prover.prove_and_insert tgt pc1
    with Proof.Proof_failed msg ->
      let errstr = error_string_case (List.rev ps) tgt pc1 in
      error_info info ("Cannot prove case \"" ^
                       (PC.string_of_term rule pc0) ^ "\"" ^ msg ^ errstr)
  in
  let t,pt = PC.discharged gidx pc1 in
  PC.add_proved_term t pt false pc0*)
