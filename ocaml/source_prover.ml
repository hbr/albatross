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
          Prover.prove p pc
        with Proof.Proof_failed msg ->
          error_info it.i ("Cannot prove precondition \"" ^
                           (PC.string_of_term p pc) ^
                           "\"\n  of term \"" ^
                           (PC.string_of_term it.v pc) ^ "\"" ^
                           msg))
      pres
  end


let get_boolean_term (e: expression) (pc:Proof_context.t): info_term =
  let c = PC.context pc in
  Typer.boolean_term e c


let get_boolean_term_verified
    (e: expression) (pc:Proof_context.t): info_term =
  let it = get_boolean_term e pc in
  verify_preconditions it pc;
  it


let get_term (e:expression) (pc:PC.t): info_term =
  let c = PC.context pc in
  Typer.untyped_term e c


let get_term_verified
    (e: expression) (pc:Proof_context.t): info_term =
  let it = get_term e pc in
  verify_preconditions it pc;
  it





let push
    (entlst: entities list withinfo)
    (rlst: compound)
    (elst: compound)
    (pc:PC.t)
    :  info_terms * info_terms * PC.t =
  assert (PC.count_type_variables pc = 0);
  let tps,fgs,rlst,elst =
    Typer.structured_assertion entlst rlst elst (PC.context pc)
  in
  rlst, elst, PC.push_typed0 tps fgs pc



(*
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
 *)

let add_assumptions (rlst:info_terms) (pc:PC.t): unit =
  List.iter
    (fun it ->
      verify_preconditions it pc;
      ignore (PC.add_assumption it.v true pc)
    )
    rlst


let add_axiom (it:info_term) (pc:PC.t): int =
  verify_preconditions it pc;
  PC.add_axiom it.v pc



let prove_insert_report_base
    (info:info) (goal:term) (search:bool) (pc:PC.t): int =
  try
    let t,pt = Prover.proof_term goal pc in
    PC.add_proved_term t pt search pc
  with Proof.Proof_failed msg ->
    error_info info ("Cannot prove \"" ^ (PC.string_of_term goal pc)
                     ^ "\"" ^ msg)


let prove_insert_report (goal:info_term) (search:bool) (pc:PC.t): int =
  prove_insert_report_base goal.i goal.v search pc


let prove_insert_close (goal:info_term) (pc:PC.t): int =
  let idx = prove_insert_report goal true pc in
  PC.close pc;
  idx


let store_unproved
    (is_defer:bool)
    (elst: info_terms)
    (pc:PC.t)
    : unit =
  assert (PC.is_toplevel pc);
  let idx_lst = List.map (fun it -> add_axiom it pc) elst in
  let pair_lst = List.map (fun idx -> PC.discharged_bubbled idx pc) idx_lst in
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
  let idx = prove_insert_report goal false pc in
  let t,pt = PC.discharged_bubbled idx pc in
  let pc0 = PC.pop pc in
  ignore (PC.add_proved false (-1) t pt pc0)



let find_goals (elst: info_terms) (pc:PC.t): unit =
  assert (PC.is_toplevel pc);
  List.iter
    (fun e ->
      let chn = PC.assumptions_chain e.v pc
      and tps = PC.local_formals pc
      and fgs = PC.local_fgs pc
      and n   = PC.count_last_arguments pc
      in
      let t1 = Term.all_quantified n tps fgs chn in
      let pc0 = PC.pop pc in
      let t2 = PC.prenex_term t1 pc0 in
      try
        ignore(PC.find t2 pc0)
      with Not_found ->
        error_info e.i "Not proved in the implementation file"
    )
    elst


let beta_reduced (t:term) (pc:PC.t): term =
  match t with
    Application(Lam(n,_,_,t0,_,tp), args, _) ->
      assert (Array.length args = 1);
      PC.beta_reduce n t0 tp args 0 pc
  | _ ->
      t


(* Support functions for induction proofs *)


type inductive_set_data =
    {pc:      PC.t;
     goal:    term;
     goal_predicate: term; (* [element in goal_predicate] reduces to [goal] *)
     other_vars: int array;
     ass_lst: int list;
     element: term;
     set:     term;        (* as written in the inpect expression *)
     set_expanded: term;   (* the inductive set '{(p): r0, r1, ... }' *)
     rules:  term array;   (* the rules *)
     induction_rule: int;  (* index of the assertion of the induction rule *)
     element_in_set: int   (* assertion which proves [element in set] *)
   }




let inner_case_context
    (ass_lst_rev: int list) (* List of assumptions already in the middle context *)
    (case_goal_pred: term)  (* case goal predicate *)
    (nass:int)              (* additional assumptions in the goal predicate *)
    (pc:PC.t)
    : int list * term * PC.t (* assumptions, goal, inner context *)
    =
  let stren_goal = PC.beta_reduce_term case_goal_pred pc in
  let n1,fargs1,fgs1,chn = Term.all_quantifier_split_1 stren_goal in
  let pc1 = PC.push_typed0 fargs1 fgs1 pc in
  let ass_lst_rev, goal =
    interval_fold
      (fun (alst,chn) _ ->
        let a,chn =
          try
            PC.split_implication chn pc1
          with Not_found ->
            assert false (* cannot happen *)
        in
        PC.add_assumption a true pc1 :: alst,
        chn
      )
      (ass_lst_rev, chn)
      0
      nass
  in
  (* Now we have context [all(other_vars) require a1; a2; ...] *)
  PC.close pc1;
  ass_lst_rev, goal, pc1




let analyze_type_inspect
    (info:info)
    (ivar:int) (* induction variable *)
    (goal:term)
    (pc:PC.t)
    : IntSet.t * int * type_term =
  (* constructor set, induction law, inductive type *)
  let c     = PC.context pc in
  let nvars = Context.count_variables c
  and ct    = Context.class_table c
  in
  assert (ivar < nvars);
  let tvs,s = Context.variable_data ivar c
  in
  assert (ivar < nvars);
  assert (Sign.is_constant s);
  let cons_set, cls, tp =
    let tp = Sign.result s in
    let cls =
      try
        Class_table.inductive_class_of_type tvs tp ct
      with Not_found ->
        let str = ST.string (Context.variable_name ivar c) in
        error_info info ("Type of \"" ^ str ^ "\" is not inductive")
    in
    (Class_table.constructors cls ct),
    cls,
    tp
  in
  let ind_idx = PC.add_specialized_induction_law tp ivar goal pc in
  cons_set,ind_idx,tp


let analyze_type_case_pattern
    (e:expression)
    (cons_set:IntSet.t)
    (tp:type_term)
    (pc:PC.t)
    : int * names =
  (* cons_idx, names *)
  let nms,pat =  Typer.case_pattern e tp (PC.context pc) in
  let nvars = PC.count_variables pc
  and n = Array.length nms
  in
  let invalid_pat () =
    error_info e.i
      ("Invalid pattern \"" ^ (string_of_expression e) ^ "\"") in
  let cons_idx =
    match pat with
      VAppl(i,args,_,_) ->
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
  in cons_idx, nms


let inductive_type_case_context
    (cons_idx: int)     (* constructor *)
    (nms: names)        (* argument names of the constructor *)
    (tp:  type_term)    (* type of the induction variable *)
    (goal_pred:term)
    (nass: int)         (* number of assumptions in the goal predicate *)
    (pc:PC.t)
    : int list * term * term * term * PC.t
      (* assumptions, goal, (inner context,
         pattern, case_goal_pred (middle context),
         inner context *)
    =
  (* Prepare the inner context and return the reversed list of assumptions,
     the goal and the inner context (2 levels deeper than the inspect context).

     goal_pred: p = {x: all(y,...) r1 ==> r2 ==> ... ==> goal}

         case cons_i(...)
            all(cvars)
                require
                    p(ra1)   -- induction hypothesis ra1: recursive argument 1
                    p(ra2)
                    ...
                ensure
                    p(cons_i(...))
                    assert
                        'p(ra1) beta reduced'
                        'p(ra2) beta reduced'
                        ...
                        all(y,...)
                            require
                                r1
                                r2
                                ...
                            ensure
                                goal[x:=cons_i(...)]
                                assert
                                   ...  -- <- user proof
                            end

                end
   *)
  let nvars = PC.count_variables pc
  and ntvs = PC.count_all_type_variables pc
  and ft    = PC.feature_table pc
  in
  let ags =
    let open Type_substitution in
    let tvs1,sign = Feature_table.signature0 cons_idx ft in
    let sub =
      make (Tvars.count_fgs tvs1) tvs1 (PC.tvars pc) (PC.class_table pc)
    in
    begin
      try
        unify (Sign.result sign) tp sub
      with Reject ->
        assert false (* cannot happen *)
    end;
    assert (greatest_plus1 sub = Tvars.count_fgs tvs1);
    array (Tvars.count_fgs tvs1) sub
  in
  let n = Array.length nms
  in
  let tps = Feature_table.argument_types cons_idx ags ntvs ft
  in
  let pc1 = PC.push_typed0 (nms,tps) empty_formals pc
  in
  let n1,_,_,ps_rev,case_goal_pred =
    Feature_table.constructor_rule cons_idx goal_pred ags nvars ft
  and pat =
    Feature_table.feature_call
      cons_idx (nvars+n) (standard_substitution n) ags ft
  in
  assert (n1 = n);
  let ind_hyp_idx_lst =
    List.fold_left
      (fun lst hypo ->
        let idx = PC.add_assumption hypo false pc1 in
        idx :: lst
      )
      []
      (List.rev ps_rev)
  in
  let ass_lst_rev =
    List.fold_left
      (fun lst idx -> (PC.add_beta_reduced idx true pc1) :: lst)
      []
      (List.rev ind_hyp_idx_lst)
  in
  PC.close pc1;
  let ass_lst_rev, goal, pc2 =
    inner_case_context ass_lst_rev case_goal_pred nass pc1 in
  ass_lst_rev, goal, pat, case_goal_pred, pc2





let induction_goal_predicate
    (vars:int array)              (* induction variables *)
    (others:int list)             (* other variables *)
    (ass_lst:int list)            (* list of assumptions *)
    (goal: term)
    (pc:PC.t)
    : term =
  (* Generate the goal predicate:

        {vars: all(others) a1 ==> a2 ==> ... ==> goal}

   *)
  assert (ass_lst <> [] || others = []);
  let c = PC.context pc in
  let nvars = PC.count_variables pc
  and argnames = Context.argnames c
  and argtypes = Context.argtypes c
  in
  let ass_rev =
    List.fold_left
      (fun lst idx ->
        let p = PC.term idx pc in
        p :: lst
      )
      ([])
      ass_lst
  and n_ind_vars = Array.length vars
  and all_vars = Array.append (Array.of_list others) vars
  in
  let n_all_vars = Array.length all_vars
  in
  let imp_id = n_all_vars + nvars + Constants.implication_index
  and n_other_vars = n_all_vars - n_ind_vars
  in
  let map,_ =
    Array.fold_left
      (fun (map,i) ivar -> IntMap.add ivar i map, i+1)
      (IntMap.empty,0)
      all_vars in
  let subst t = Term.lambda_inner_map t map in
  let nms_inner = Array.init n_other_vars (fun i -> argnames.(all_vars.(i)))
  and tps_inner = Array.init n_other_vars (fun i -> argtypes.(all_vars.(i)))
  and nms_outer =
    Array.init n_ind_vars (fun i -> argnames.(all_vars.(i+n_other_vars)))
  and tps_outer =
    Array.init n_ind_vars (fun i -> argtypes.(all_vars.(i+n_other_vars)))
  in
  let chn =
    List.fold_left
      (fun chn p ->
        let p = subst p in
        Term.binary imp_id p chn
      )
      (subst goal)
      ass_rev
  in
  let t =
    Term.all_quantified n_other_vars (nms_inner,tps_inner) empty_formals chn
  in
  let tp = Context.predicate_of_type (Context.tuple_of_types tps_outer c) c in
  let t = Context.make_lambda n_ind_vars nms_outer  [] t true 0 tp c in
  t





let inductive_set
    (info:info) (set:term) (c:Context.t)
    : term * type_term * term array =
  try
    let set_exp = Context.inductive_set set c in
    begin
      match set_exp with
        Indset (nme,tp,rs) ->
          let rs = Array.map (fun r -> Term.apply r [|set|]) rs in
          set_exp, tp, rs
      | _ ->
          assert false (* cannot happen *)
    end
  with Not_found ->
    error_info info ("\"" ^ (Context.string_of_term set c) ^
                     "\" does not evaluate to an inductive set")






let inductive_set_context
    (info: info)
    (elem: term)
    (set:  term)
    (user_goal: term)
    (pc:PC.t)
    : inductive_set_data =
  (* Analyzes the outer part of an inductive set proof.

        inspect
            elem in set  -- elem must be either a variable or a tuple of variables
                         -- The variables in 'elem' must not appear in 'set'.
        ...
   *)
  assert (not (PC.is_global pc));
  let c    = PC.context pc in
  let set_expanded, set_tp, rules = inductive_set info set c
  in
  let nvars = Context.count_variables c in
  let goal_pred, other_vars, ass_lst =
    let ft = Context.feature_table c in
    let set_vars = Term.used_variables set nvars in
    let vars   = Feature_table.args_of_tuple elem nvars ft in
    let vars = Array.map
        (fun arg ->
          match arg with
            Variable i when i < nvars ->
              if List.mem i set_vars then
                error_info
                  info
                  ("Induction variable \"" ^ (PC.string_of_term arg pc) ^
                   "\" must not occur in the set/relation \"" ^
                   (PC.string_of_term set pc) ^ "\"");
              i
          | _ ->
              error_info info ("\"" ^ (PC.string_of_term arg pc) ^
                               "\" is not a variable")
        )
        vars
    in
    let ass_lst, other_var_lst =
      let insp_vars = Term.used_variables elem nvars in
      let insp_vars = Term.used_variables_0 set nvars insp_vars in
      PC.assumptions_for_variables vars insp_vars pc in
    let goal_pred =
      induction_goal_predicate
        vars
        other_var_lst
        ass_lst
        user_goal
        pc
    in
    goal_pred, Array.of_list other_var_lst, ass_lst
  in
  let pa = Application(set,[|elem|],false) in
  let pa_idx = prove_insert_report_base info pa false pc in
  let ind_idx = PC.add_set_induction_law set goal_pred elem pc in
  if PC.is_tracing pc then begin
    let prefix = PC.trace_prefix pc in
    printf "\n\n";
    printf "%sProof with inductively defined set\n\n" prefix;
    printf "%sensure\n" prefix;
    printf "%s    %s\n" prefix (PC.string_long_of_term user_goal pc);
    printf "%sinspect\n" prefix;
    printf "%s    %s\n\n"
      prefix
      (PC.string_long_of_term (Application(set,[|elem|],false)) pc)
  end;
  {pc             = pc;
   goal           = user_goal;
   goal_predicate = goal_pred;
   other_vars     = other_vars;
   ass_lst        = ass_lst;
   set            = set;
   set_expanded   = set_expanded;
   element        = elem;
   rules          = rules;
   induction_rule = ind_idx;
   element_in_set = pa_idx;
 }



let inductive_set_case
    (case_exp: expression)
    (data: inductive_set_data)
    : int * term =
  let c = PC.context data.pc in
  let rule = (Typer.boolean_term case_exp c).v in
  let irule =
    try
      interval_find
        (fun i -> Term.equivalent data.rules.(i) rule)
        0
        (Array.length data.rules)
    with Not_found ->
      error_info case_exp.i "Invalid case"
  in
  irule, rule





let error_string_case (ps_rev:term list) (goal:term) (pc:PC.t): string =
  let psstr = String.concat "\n"
      (List.rev_map
         (fun ass -> (PC.string_of_term (beta_reduced ass pc) pc))
         ps_rev)
  and tgtstr = PC.string_of_term (beta_reduced goal pc) pc in
  "\n" ^ psstr ^ "\n--------------------------\n" ^ tgtstr




let add_set_induction_hypothesis
    (hypo_idx:int)
    (pc:PC.t)
    : int =
  (* The induction hypothesis has the form

         all(hypo_vars) d1 ==> ... ==>
                {ind_vars: all(other_vars) a1 ==> ... ==> user_goal}(ind_vars)

     and has been added to the context of the case at [hypo_idx].

     We have to add the following assertion to the context and return its index:

         all(hypo_vars, other_vars) a1 ==> a2 ==> ... ==> d1 ==> ... ==> goal
    *)
  let hypo = PC.term hypo_idx pc
  in
  let n1,fargs1,fgs1,ps_rev1,goal_redex1 =
    PC.split_general_implication_chain hypo pc
  in
  assert (fgs1 = empty_formals);
  let pc1 = PC.push_typed0 fargs1 empty_formals pc
  in
  match goal_redex1 with
    Application(Lam(_),_,_) ->
      let outer_goal = PC.beta_reduce_term goal_redex1 pc1
      in
      let n2,fargs2,fgs2,ps_rev2,user_goal =
        PC.split_general_implication_chain outer_goal pc1
      in
      assert (fgs2 = empty_formals);
      let pc2 = PC.push_typed0 fargs2 empty_formals pc1
      in
      assert (fgs2 = empty_formals);
      (* Now we have two contexts: all(hypo_vars)  all(other_vars *)
      let alst_rev =
        List.rev_map
          (fun a -> PC.add_assumption a false pc2)
          (List.rev ps_rev2)
      in
      let dlst_rev =
        List.rev_map
          (fun d -> PC.add_assumption (Term.up n2 d) false pc2)
          (List.rev ps_rev1)
      in
      (* Now we have a1; a2; ... ; d1; d2, ... as assumptions in the context and
         can specialize the induction hypothesis hypo_idx.*)
      let gen_goalpred_idx =
        let spec_hypo_idx =
          let args = Array.init n1 (fun i -> Variable (i + n2)) in
          PC.specialized hypo_idx args [||] 0 pc2
        in
        List.fold_left
          (fun idx d_idx ->
            PC.add_mp d_idx idx false pc2)
          spec_hypo_idx
          (List.rev dlst_rev)
      in
      let gen_goal_idx = PC.add_beta_reduced gen_goalpred_idx false pc2 in
      let chn_goal_idx =
        let args = standard_substitution n2 in
        PC.specialized gen_goal_idx args [||] 0 pc2
      in
      let goal_idx =
        List.fold_left
          (fun idx a_idx -> PC.add_mp a_idx idx false pc2)
          chn_goal_idx
          (List.rev alst_rev)
      in
      let t,pt = PC.discharged_bubbled goal_idx pc2 in
      let idx = PC.add_proved_term t pt false pc1 in
      let t,pt = PC.discharged_bubbled idx pc1 in
      PC.add_proved_term t pt true pc
  | _ ->
      hypo_idx



let string_of_case_context
    (prefix: string)
    (ass_lst_rev: int list)
    (goal: term)
    (pc:PC.t)
    : string =
  let ass_str =
    String.concat
      ("\n" ^ prefix)
      (List.rev_map
         (fun a_idx -> PC.string_long_of_term_i a_idx pc)
         ass_lst_rev)
  and goal_str =
    PC.string_long_of_term goal pc
  in
  prefix ^ ass_str ^ "\n"
  ^ prefix ^ "---------------------\n"
  ^ prefix ^ goal_str ^ "\n"



let inductive_set_case_context
    (set:  term)
    (set_expanded: term)
    (rule:term)
    (irule:int)
    (nass: int)
    (goal_pred:term)
    (pc: PC.t):
    int list * term * term * PC.t  (* assumptions, goal, inner context *)
    =
  (*
    Prepare the inner context and return the reversed list of assumptions,
    the goal and the inner context (2 levels deeper than the inspect context).

    The rule has the form

        all(rule vars) c1 ==> c2 ==> ... ==> p(e)

    The goal predicate has the form

       {ind vars: all(other vars) a1 ==> a2 ==> ... ==> user_goal}

    with [nass] assumptions before the user goal.

    The new context has the form

        all(rule vars)
            require
                c1(set)
                c1(goal_pred)    -- ind hypo 1
                c2(set)
                c2(goal_pred)    -- ind hypo 2
                ...
                e in set
            proof
                all(other vars)
                    require
                        a1
                        a2
                        ...
                    proof
                        ind hypo 1 in user terms
                        ind hypo 2 in user terms
                        ...
                        ...  -- <-- here the user proof starts to prove the
                             --     goal

    where

         ci:
             all(hypo vars) d1i ==> d2i ==> ... ==> p(ei)

         ind hypo i:
             all(hypo vars) d1i ==> ... ==> goal_pred(ei)
   *)
  let n1,fargs1,ps,goal_pred1 =
    let nvars = PC.count_variables pc in
    let imp_id = nvars + Constants.implication_index in
    let n,(_,tps), ps, goal_pred1 =
      Term.induction_rule imp_id irule set_expanded set goal_pred
    in
    let m,(nms,_),_,_ = Term.all_quantifier_split_1 rule in
    assert (n = m);
    n,(nms,tps), ps, goal_pred1
  in
  let pc1 = PC.push_typed0 fargs1 empty_formals pc in
  (* add induction hypotheses *)
  let ass_lst_rev, hlst_rev, _ =
    List.fold_left
      (fun (alst, hlst, is_hypo) p ->
        if is_hypo then
          let idx = PC.add_assumption p false pc1 in
          alst, idx::hlst, false
        else begin
          let idx = PC.add_assumption p true pc1 in
          idx::alst, hlst, true
        end
      )
      ([],[],false)
      ps
  in
  (* add induction hypotheses in usable form *)
  let ass_lst_rev =
    List.fold_left
      (fun alst idx ->
        let hidx = add_set_induction_hypothesis idx pc1 in
        hidx::alst
      )
      ass_lst_rev
      (List.rev hlst_rev)
  in
  PC.close pc1;
  (* Now we have context [all(rule_vars) require c1(set); c1(q); ... set(e)] *)
  let ass_lst_rev, goal, pc2 =
    inner_case_context ass_lst_rev goal_pred1 nass pc1
  in
  ass_lst_rev, goal, goal_pred1, pc2


(* Support functions for transitivity proofs *)

let get_transitivity_data
    (info:info)
    (goal:term)
    (pc:PC.t)
    : int * term * term * type_term * agens * (term -> term -> term) =
  (* Analyze the goal which should have the form 'r(a,b)' (if not report an error)
     and return

     Index of the transitivity law 'all(a,b,c:G) r(a,b) ==> r(b,c) ==> r(a,c)

     The terms 'a' and 'b' and the type of the terms

     The actual generics (0 or 1) which are needed to substitute the formal
     generics (0 or 1) of the transitivity law.

     A function which maps two terms 'x' and 'y' to 'r(x,y)'
   *)
  let error str =
    error_info info ("The goal \"" ^ (PC.string_of_term goal pc) ^
                     "\" " ^ str)
  in
  let error_not_proper () =
    error "is not a proper binary boolean expression"
  in
  let c = PC.context pc in
  let nvars = Context.count_variables c
  in
  let find_law (rel:int -> term -> term -> term) (tp:type_term): int*agens =
      let a = Variable 0
      and b = Variable 1
      and c = Variable 2
      and imp_id = 3 + nvars
      and nms = standard_argnames 3
      and tps = [|tp;tp;tp|]
      in
      let pc1 = PC.push_typed0 (nms,tps) empty_formals pc in
      let t =
        let ab = rel 3 a b
        and bc = rel 3 b c
        and ac = rel 3 a c in
        Term.binary imp_id ab (Term.binary imp_id bc ac)
      in
      let idx_law,ags =
        try
          PC.find_schematic t 3 pc1
        with Not_found ->
          let law = Term.all_quantified
              3 (standard_argnames 3,[|tp;tp;tp|]) empty_formals t
          in
          error_info info ("Cannot find the transitivity law\n\t\"" ^
                           (PC.string_long_of_term law pc) ^
                           "\"")
      in
      idx_law, ags
  in
  match goal with
    Application (p, [|arg|], _) ->
      let p_tp = Context.type_of_term p c in
      let cls,ags = split_type p_tp in
      if cls = Context.predicate_class c then begin
        assert (Array.length ags = 1);
        let ft = Context.feature_table c in
        let tup_tp = Class_table.domain_type p_tp in
        let args = Feature_table.args_of_tuple arg nvars ft in
        if Array.length args <> 2 then
          error_not_proper ();
        let tp = Context.type_of_term args.(0) c in
        if not (Term.equivalent tp (Context.type_of_term args.(1) c)) then
          error_not_proper ();
        let rel nb a b =
          let p = Term.up nb p in
          let arg = Feature_table.tuple_of_args [|a;b|] tup_tp (nb+nvars) ft in
          Application (p, [|arg|],false)
        in
        let idx_law,ags = find_law rel tp in
        idx_law, args.(0), args.(1), tp, ags, rel 0
      end else
        error_not_proper ()
  | VAppl (idx, [|a1;a2|], ags,oo)
    when Term.equivalent
        (Context.type_of_term a1 c)
        (Context.type_of_term a2 c)
    ->
      let tp = Context.type_of_term a1 c in
      let mkterm nb a b = VAppl (nb+idx,[|a;b|],ags,oo) in
      let idx_law,ags = find_law mkterm tp in
      idx_law, a1, a2, tp, ags, mkterm 0
  | _ ->
      error_not_proper ()


let prove_transitivity_step
    (info:info)
    (idx_law:int) (* index of 'all(a,b,c:T) r(a,b) ==> r(b,c) ==> r(a,c)' *)
    (idx_rab:int) (* index of 'r(a,b)' *)
    (a: term)
    (b: term)
    (c: term)
    (ags:agens)
    (r: term -> term -> term)
    (pc:PC.t)
    : int =
  (* It is assumed that 'r(a,b)' has been proved. The function proves 'r(b,c)'
     and uses the transitivity law to prove 'r(a,c)'.
   *)
  let rbc = r b c in
  let idx_rbc = prove_insert_report_base info rbc false pc
  in
  let spec_law = PC.specialized idx_law [|a;b;c|] ags 0 pc
  in
  let idx = PC.add_mp idx_rab spec_law false pc
  in
  PC.add_mp idx_rbc idx false pc




(* Mutually recursive prover functions *)

let rec prove_and_store
    (entlst: entities list withinfo)
    (rlst: compound)
    (elst: compound)
    (prf:  source_proof)
    (pc:PC.t)
    : unit =
  if PC.is_public pc then begin
    match prf with
      SP_Deferred | SP_Proof ([],None) ->
        ()
    | SP_Axiom ->
        error_info entlst.i "Axiom not allowed in interface file"
    | _ ->
        error_info entlst.i "Proof not allowed in interface file"
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
    let t,pt = PC.discharged_bubbled idx pc1 in
    ignore (PC.add_proved false (-1) t pt pc)
  in
  match prf with
    SP_Axiom | SP_Deferred ->
      store_unproved false elst pc1
  | SP_Proof([],None) ->
      if PC.is_interface_use pc1 then
        store_unproved false elst pc1
      else if PC.is_interface_check pc1 then begin
        find_goals elst pc1
      end else
        prove_goal ()
  | _ ->
        prove_goal ()


and prove_one
    (goal:term) (prf:source_proof) (pc:PC.t)
    : int =
  (* Prove [goal] with the proof expression [prf]. Assume that the preconditions
     of the goal are already verified. *)
  assert (PC.is_private pc);
  let result idx =
    let ok = Term.equivalent goal (PC.term idx pc) in
    if not ok then
      begin
        printf "proved %s  %s\n"
               (PC.string_long_of_term (PC.term idx pc) pc)
               (Term.to_string (PC.term idx pc));
        assert (PC.is_well_typed (PC.term idx pc) pc);
        printf "goal   %s  %s\n"
               (PC.string_long_of_term goal pc)
               (Term.to_string goal);
        assert (PC.is_well_typed goal pc);
      end;
    assert (Term.equivalent goal (PC.term idx pc));
    idx
  in
  match prf with
    SP_Axiom | SP_Deferred -> assert false (* cannot happen here *)
  | SP_Proof (lst, pexp) ->
      prove_sequence lst pc;
      begin match pexp with
        None ->
          result (Prover.prove_and_insert goal pc)
      | Some prf ->
          try
            result (
              match prf.v with
                PE_If (cond, sprf1, sprf2) ->
                  prove_if prf.i goal cond sprf1 sprf2 pc
              | PE_Guarded_If (cond1, sprf1, cond2, sprf2) ->
                  prove_guarded_if prf.i goal cond1 sprf1 cond2 sprf2  pc
              | PE_Inspect (insp, cases) ->
                  prove_inspect prf.i goal insp cases pc
              | PE_Existential (entlst, reqs, prf1) ->
                  prove_exist_elim prf.i goal entlst reqs prf1 pc
              | PE_Contradiction (exp,prf1) ->
                  prove_contradiction prf.i goal exp prf1 pc
              | PE_Transitivity lst ->
                  prove_by_transitivity prf.i goal lst pc
            )
          with Proof.Proof_failed msg ->
            error_info prf.i ("Does not prove \"" ^
                              (PC.string_of_term goal pc) ^
                              "\"" ^ msg)
      end


and prove_sequence
    (lst: proof_step list)
    (pc: PC.t): unit =
  assert (PC.count_type_variables pc = 0);
  let expand (i:int): unit =
    PC.expand_variable_definitions i pc
  in
  List.iter
    (fun step ->
      begin match step with
        PS_Simple ie ->
          let it = get_boolean_term_verified ie pc in
          expand (prove_insert_report it true pc)
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
          let t,pt = PC.discharged_bubbled idx pc1 in
          expand (PC.add_proved false (-1) t pt pc)
      end;
      PC.close pc
    )
    lst


and prove_guarded_if
    (info: info)
    (goal: term)
    (c1:expression) (prf1:source_proof)
    (c2:expression) (prf2:source_proof)
    (pc:PC.t)
    : int =
  let c1 = get_boolean_term_verified c1 pc
  and c2 = get_boolean_term_verified c2 pc
  in
  let or_exp = PC.disjunction c1.v c2.v pc in
  let or_exp_idx =
    prove_insert_report (withinfo info or_exp) false pc
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
    (c1:expression)
    (prf1:source_proof)
    (prf2:source_proof)
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
    (cond:info_term) (goal:term) (prf:source_proof) (pc:PC.t)
    : int =
  let pc1 = PC.push_empty pc in
  ignore (PC.add_assumption cond.v true pc1);
  PC.close pc1;
  let idx =
    try
      prove_one goal prf pc1
    with Proof.Proof_failed msg ->
      error_info
        cond.i
        ("Cannot prove the goal\n\t\"" ^ (PC.string_of_term goal pc) ^
         "\"\nassuming\n\t\"" ^ (PC.string_of_term cond.v pc) ^ "\"")
  in
  let t,pt = PC.discharged_bubbled idx pc1 in
  PC.add_proved_term t pt false pc


and prove_inspect
    (info:info)
    (goal:term)
    (insp:expression) (cases:one_case list) (pc:PC.t): int =
  let insp = get_term insp pc in
  match insp.v with
    Variable var_idx ->
      prove_inductive_type info goal var_idx cases pc
  | Application (set,args,_) ->
      assert (Array.length args = 1);
      prove_inductive_set info goal args.(0) set cases pc
  | _ ->
      error_info info "Illegal induction proof"


and prove_inductive_type
    (info:info)
    (goal:term)
    (ivar: int) (* induction variable *)
    (cases: one_case list)
    (pc:PC.t)
    : int =
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
  let ass_idx_lst, other_vars =
    PC.assumptions_for_variables [|ivar|] [ivar] pc in
  let goal_pred =
    induction_goal_predicate [|ivar|] other_vars ass_idx_lst goal pc
  and nass = List.length ass_idx_lst
  in
  let goal =
    beta_reduced (Application(goal_pred,[|Variable ivar|],false)) pc in
  let cons_set, ind_idx, tp =
    analyze_type_inspect info ivar goal pc
  in
  let c  = PC.context pc in
  let ft  = Context.feature_table c in
  let proved_cases =
    (* explicitly given cases *)
    List.fold_left
      (fun map (ie,prf) ->
        let cons_idx, nms =
          analyze_type_case_pattern ie cons_set tp pc in
        (*let idx = prove_type_case cons_idx nms tp prf ivar goal pc in*)
        let idx =
          prove_type_case ie.i cons_idx nms tp prf ivar goal_pred nass pc in
        IntMap.add cons_idx idx map
      )
      IntMap.empty
      cases
  in
  let idx_goal_redex =
    (* rest of the cases *)
    IntSet.fold
      (fun cons_idx ind_idx ->
        let idx =
          try
            IntMap.find cons_idx proved_cases
          with Not_found ->
            let n   = Feature_table.arity cons_idx ft in
            let nms = anon_argnames n in
            (*prove_type_case
              cons_idx nms tp (SP_Proof([],None)) ivar goal pc*)
            prove_type_case
              info cons_idx nms tp (SP_Proof([],None)) ivar goal_pred nass pc
        in
        PC.add_mp idx ind_idx false pc
      )
      cons_set
      ind_idx
  in
  let res =
    let idx  = PC.add_beta_reduced idx_goal_redex false pc in
    let vars = Array.map (fun i -> Variable i) (Array.of_list other_vars) in
    PC.specialized idx vars [||] 0 pc
  in
  let res =
    List.fold_left
      (fun res ass_idx ->
        PC.add_mp ass_idx res false pc
      )
      res
      ass_idx_lst
  in
  res



and prove_type_case
    (info:info)
    (cons_idx:int)
    (nms: names)     (* The names of the arguments of the constructor *)
    (tp:type_term)   (* inductive type in the outer context *)
    (prf:source_proof)
    (ivar:int)       (* induction variable *)
    (goal_pred:term) (* in the outer context *)
    (nass:int)       (* number of assumptions in the goal predicate *)
    (pc:PC.t)        (* outer context *)
    : int =
  (* Prove one case of an inductive type
   *)
  let ass_lst_rev, goal, pat, case_goal_pred, pc2 =
    inductive_type_case_context cons_idx nms tp goal_pred nass pc
  in
  let pc1 = PC.pop pc2 in
  if PC.is_tracing pc then begin
    let prefix = PC.trace_prefix pc in
    printf "\n\n";
    printf "%scase %s\n" prefix (PC.string_of_term pat pc1);
    printf "%sgoal\n" prefix;
    printf "%s\n"
      (string_of_case_context (prefix ^ "    ") ass_lst_rev goal pc2);
  end;
  let gidx =
    try
      prove_one goal prf pc2
    with Proof.Proof_failed msg ->
      let casestr = string_of_case_context "" ass_lst_rev goal pc2
      and patstr  = PC.string_of_term pat pc1 in
      error_info info ("Cannot prove case \"" ^ patstr ^ "\""
                       ^ msg ^ "\n" ^ casestr)
  in
  let t,pt = PC.discharged gidx pc2 in
  let idx = PC.add_proved_term t pt false pc1 in
  let idx = PC.add_beta_redex case_goal_pred idx false pc1 in
  let t,pt = PC.discharged idx pc1 in
  let res = PC.add_proved_term t pt false pc in
  if PC.is_tracing pc then
    printf "\n%scase succeeded\n\n" (PC.trace_prefix pc);
  res



and prove_inductive_set
    (info:info)
    (goal:term)
    (elem:term)
    (set: term)
    (cases: one_case list)
    (pc:PC.t)
    : int =
  (* Execute a proof with an inductive set:

         ensure
             ens
         inspect
             elem in set      -- 'elem in set' must be valid

         case         -- List of zero of more cases, each case represents a
             ...      -- rule for 'elem in set' to be valid
         proof
             ...

         ...
         end
   *)
  assert (not (PC.is_global pc));
  let data = inductive_set_context info elem set goal pc
  in
  let nrules = Array.length data.rules
  in
  let proved =
    List.fold_left
      (fun proved (ie,prf) ->
        let irule, rule = inductive_set_case ie data in
        let ass_lst_rev, goal, goal_pred, pc_inner =
          inductive_set_case_context
            data.set
            data.set_expanded
            rule
            irule
            (List.length data.ass_lst)
            data.goal_predicate
            pc in
        let idx =
          prove_inductive_set_case
            ie.i rule ass_lst_rev goal goal_pred prf pc_inner data.pc
        in
        IntMap.add irule idx proved
      )
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
            let ass_lst_rev, goal, goal_pred, pc_inner =
              inductive_set_case_context
                data.set
                data.set_expanded
                data.rules.(irule)
                irule
                (List.length data.ass_lst)
                data.goal_predicate
                pc
            in
            prove_inductive_set_case
              info data.rules.(irule) ass_lst_rev goal goal_pred
              (SP_Proof([],None)) pc_inner data.pc
        in
        PC.add_mp rule_idx ind_idx false data.pc
      )
      data.induction_rule 0 nrules
  in
  let gidx = PC.add_mp data.element_in_set ind_idx false data.pc
  in
  let res =
    let idx = PC.add_beta_reduced gidx false pc in
    let vars = Array.map (fun i -> Variable i) data.other_vars in
    PC.specialized idx vars [||] 0 pc
  in
  let res =
    List.fold_left
      (fun res ass_idx ->
        PC.add_mp ass_idx res false pc
      )
      res
      data.ass_lst
  in
  res


and prove_inductive_set_case
    (info:info)
    (rule:term)                   (* in the outer context *)
    (ass_lst_rev: int list)
    (goal: term)                  (* in the inner context *)
    (goal_pred: term)             (* in the middle context *)
    (prf: source_proof)
    (pc1:PC.t)                    (* inner context *)
    (pc0:PC.t)                    (* outer context *)
    : int =
  if PC.is_tracing pc0 then begin
    let prefix = PC.trace_prefix pc0 in
    printf "\n\n";
    printf "%scase\n" prefix;
    printf "%s    %s\n" prefix (PC.string_long_of_term rule pc0);
    printf "%sgoal\n" prefix;
    printf "%s\n"
      (string_of_case_context (prefix ^ "    ") ass_lst_rev goal pc1);
  end;
  let gidx =
    try
      prove_one goal prf pc1
    with Proof.Proof_failed msg ->
      let casestr = string_of_case_context "" ass_lst_rev goal pc1
      and rulestr = PC.string_of_term rule pc0 in
      error_info info ("Cannot prove case \"" ^ rulestr ^ "\""
                       ^ msg ^ "\n" ^ casestr)
  in
  let t,pt = PC.discharged gidx pc1 in
  let pc01 = PC.pop pc1 in
  let idx = PC.add_proved_term t pt false pc01 in
  let idx = PC.add_beta_redex goal_pred idx false pc01 in
  let t,pt = PC.discharged idx pc01 in
  let res = PC.add_proved_term t pt false pc0 in
  if PC.is_tracing pc0 then
    printf "\n%scase succeeded\n\n" (PC.trace_prefix pc0);
  res




and prove_exist_elim
    (info: info)
    (goal: term)
    (entlst: entities list withinfo)
    (req: expression)
    (prf: source_proof)
    (pc:PC.t)
    : int =
  PC.close pc;
  let someexp = (withinfo info (Expquantified (Existential,entlst,req))) in
  let someexp = get_boolean_term_verified someexp pc in
  let someexp_idx =
    try
      let t,pt = Prover.proof_term someexp.v pc in
      PC.add_proved_term t pt false pc
    with Proof.Proof_failed msg ->
      error_info
        someexp.i
        ("Cannot prove \"" ^ (PC.string_of_term someexp.v pc) ^
         "\"" ^ msg)
  in
  let elim_idx = PC.add_some_elim_specialized someexp_idx goal false pc in
  let n,fargs,t0 = Term.some_quantifier_split someexp.v in
  let pc1 = PC.push_typed0 fargs empty_formals pc in
  ignore (PC.add_assumption t0 true pc1);
  PC.close pc1;
  let goal = Term.up n goal in
  let goal_idx = prove_one goal prf pc1 in
  let t,pt = PC.discharged goal_idx pc1 in
  let all_idx = PC.add_proved_term t pt false pc in
  PC.add_mp all_idx elim_idx false pc





and prove_contradiction
    (info: info)
    (goal: term)
    (exp:  expression)
    (prf:  source_proof)
    (pc:PC.t)
    : int =
  let exp = get_boolean_term exp pc in
  let pc1 = PC.push_empty pc in
  ignore (PC.add_assumption exp.v true pc1);
  PC.close pc1;
  let false_idx =
    try
      prove_one (PC.false_constant pc1) prf pc1
    with Proof.Proof_failed msg ->
      error_info
        info
        ("Cannot derive \"false\" from \"" ^
         (PC.string_of_term exp.v pc1) ^ "\"")
  in
  let t,pt = PC.discharged false_idx pc1 in
  ignore(PC.add_proved_term t pt true pc);
  PC.close pc;
  try
    prove_one goal (SP_Proof([],None)) pc
  with Proof.Proof_failed msg ->
    error_info
      info
      ("Cannot prove\n\t\"" ^
       (PC.string_of_term goal pc) ^
      "\"\nby assuming\n\t\"" ^
       (PC.string_of_term t pc) ^
       "\"")



and prove_by_transitivity
    (info:info)
    (goal:term)
    (lst: expression list)
    (pc:PC.t)
    : int =
  assert (lst <> []);
  let c = PC.context pc in
  let idx_law, first, last, tp, ags, rel =
    get_transitivity_data info goal pc
  in
  let lst = List.map (fun ie -> Typer.typed_term ie tp c) lst
  in
  match lst with
    b :: tail ->
      let rab = rel first b.v in
      let idx_rab = prove_insert_report_base b.i rab false pc in
      let idx_rax, x =
        List.fold_left
          (fun (idx_rab,b) c ->
            let idx_rac =
              prove_transitivity_step
                c.i idx_law idx_rab first b c.v ags rel pc
            in
            idx_rac, c.v
          )
          (idx_rab,b.v)
          tail
      in
      prove_transitivity_step
        info idx_law idx_rax first x last ags rel pc
  | _ ->
      assert false (* cannot happen *)
