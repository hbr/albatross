(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term
open Proof
open Support
open Printf

module RD = Rule_data

type slot_data = {ndown:int;
                  sprvd: int TermMap.t}



type entry = {mutable prvd:  Term_table.t;  (* all proved terms *)
              mutable prvd2: Term_table.t;  (* as schematic terms *)
              mutable bwd:   Term_table.t;
              mutable fwd:   Term_table.t;
              mutable left:  Term_table.t;
              mutable slots: slot_data array}

type gdesc = {mutable pub: bool;
              inh: bool;
              cls: int;
              anchor_cls: int;
              mdl: int;
              mutable defer: bool}

type t = {base:   Proof_table.t;
          terms:  RD.t Ass_seq.t;
          gseq:   gdesc Seq.t;
          depth:  int;
          mutable work:   int list;
          count0: int;
          entry:  entry;
          prev:   t option;
          trace:  bool;
          verbosity: int}

let verbosity (pc:t): int = pc.verbosity

let is_tracing (pc:t): bool = pc.verbosity >= 3

let context (pc:t): Context.t = Proof_table.context pc.base

let module_table (pc:t): Module_table.t =
  let c = context pc in
  Context.module_table c

let feature_table (pc:t): Feature_table.t =
  let c = context pc in
  Context.feature_table c

let class_table (pc:t): Class_table.t =
  let c = context pc in
  Context.class_table c

let is_private (pc:t): bool = Proof_table.is_private pc.base
let is_public  (pc:t): bool = Proof_table.is_public  pc.base
let is_interface_use   (pc:t): bool = Proof_table.is_interface_use  pc.base
let is_interface_check (pc:t): bool = Proof_table.is_interface_check  pc.base

let add_used_module (name:int*int list) (used:IntSet.t) (pc:t): unit =
  Proof_table.add_used_module name used pc.base

let add_current_module (name:int) (used:IntSet.t) (pc:t): unit =
  Proof_table.add_current_module name used pc.base

let set_interface_check (pub_used:IntSet.t) (pc:t): unit =
  Proof_table.set_interface_check pub_used pc.base



let make_entry () =
  let e = Term_table.empty in
    {prvd=e; prvd2=e; bwd=e; fwd=e; left=e;
     slots = Array.make 1 {ndown = 0; sprvd = TermMap.empty}}

let copied_entry (e:entry): entry =
  {prvd     = e.prvd;
   prvd2    = e.prvd2;
   bwd      = e.bwd;
   fwd      = e.fwd;
   left     = e.left;
   slots    = Array.copy e.slots}




let make (verbosity:int): t  =
  let res =
    {base     = Proof_table.make verbosity;
     terms    = Ass_seq.empty ();
     gseq     = Seq.empty ();
     depth    = 0;
     prev     = None;
     work     = [];
     count0   = 0;
     entry    = make_entry ();
     trace    = verbosity >= 3;
     verbosity= verbosity}
  in
  res


let is_global (at:t): bool =
  Proof_table.is_global at.base

let is_local (at:t): bool =
  Proof_table.is_local at.base

let is_toplevel (at:t): bool =
  Proof_table.is_toplevel at.base

let nbenv (at:t): int = Proof_table.count_variables at.base

let count_base (pc:t): int = Proof_table.count pc.base

let count (pc:t): int = Ass_seq.count pc.terms

let is_consistent (pc:t): bool =
  count_base pc = count pc

let count_previous (pc:t): int = Proof_table.count_previous pc.base
let count_global(pc:t): int = Proof_table.count_global pc.base

let imp_id(at:t): int = Proof_table.imp_id at.base

let term_orig (i:int) (pc:t): term * int =
  (** The [i]th proved term with the number of variables of its environment.
   *)
  assert (i < count_base pc);
  Proof_table.term i pc.base

let term (i:int) (pc:t): term =
  (** The [i]th proved term in the current environment.
   *)
  assert (is_consistent pc);
  assert (i < count pc);
  Proof_table.local_term i pc.base

let term_up (i:int) (n:int) (pc:t): term =
  assert (0 <= n);
  Term.up n (term i pc)

let depth (pc:t): int = pc.depth


let rule_data (idx:int) (pc:t): RD.t =
  assert (idx < count pc);
  Ass_seq.elem idx pc.terms

let is_fully_specialized (idx:int) (pc:t): bool =
  RD.is_fully_specialized (rule_data idx pc)


let is_assumption (i:int) (pc:t): bool =
  assert (i < count pc);
  Proof_table.is_assumption i pc.base


let is_available (i:int) (pc:t): bool =
  assert (i < count pc);
  is_private pc ||
  count_global pc <= i ||
  let gdesc = Seq.elem i pc.gseq in
  not gdesc.inh ||
  gdesc.pub


let is_visible (i:int) (pc:t): bool =
  not (is_interface_check pc) ||
  let ft = feature_table pc
  and nb = nbenv pc
  and t  = term i pc in
  Feature_table.is_term_public t nb ft


let split_implication (t:term) (pc:t): term * term =
  Proof_table.split_implication t pc.base

let split_all_quantified (t:term) (pc:t): int * int array * term =
  Proof_table.split_all_quantified t pc.base

let split_some_quantified (t:term) (pc:t): int * int array * term =
  Proof_table.split_some_quantified t pc.base

let implication (a:term) (b:term) (pc:t): term =
  Proof_table.implication a b pc.base

let negation (a:term) (pc:t): term =
  let nb = nbenv pc in
  Term.unary (nb + Feature_table.not_index) a

let all_quantified (nargs:int) (names:int array) (t:term) (pc:t): term =
  Proof_table.all_quantified nargs names t pc.base

let implication_chain (ps:term list) (tgt:term) (pc:t): term  =
  Proof_table.implication_chain ps tgt pc.base


let work (pc:t): int list = pc.work

let has_work (pc:t): bool = pc.work <> []

let clear_work (pc:t): unit =
  pc.work <- []


let has_result (pc:t): bool = Proof_table.has_result pc.base

let has_result_variable (pc:t): bool = Proof_table.has_result_variable pc.base

let string_of_term (t:term) (pc:t): string =
  Context.string_of_term t true 0 (context pc)


let string_of_term_anon (t:term) (nb:int) (pc:t): string =
  Context.string_of_term t true nb (context pc)


let string_of_term_i (i:int) (pc:t): string =
  assert (i < count pc);
  string_of_term (term i pc) pc


let string_of_term_array (args: term array) (pc:t): string =
  "[" ^
  (String.concat ","
     (List.map (fun t -> string_of_term t pc) (Array.to_list args)))
  ^
  "]"


let unify
    (t:term) (nbenv:int) (tab:Term_table.t) (pc:t): (int * Term_sub.t) list =
  Term_table.unify t nbenv tab

let unify_with
    (t:term) (nargs:int) (nbenv:int) (tab:Term_table.t) (pc:t)
    : (int * Term_sub.t) list =
  Term_table.unify_with t nargs nbenv tab


let trace_prefix_0 (pc:t): string =
  assert (not (is_global pc));
  String.make (3 + 2*(pc.depth-1)) ' '


let trace_prefix (pc:t): string =
  String.make (3 + 2*pc.depth) ' '

let is_trace_extended (pc:t): bool = 3 < pc.verbosity

let trace_term (t:term) (rd:RD.t) (search:bool) (dup:bool) (pc:t): unit =
  let str    = string_of_term t pc
  and cnt    = count pc
  and prefix = trace_prefix pc in
  assert (cnt + 1 = count_base pc);
  let ext =
    if is_trace_extended pc then
      let pt = Proof_table.proof_term cnt pc.base in
      let ptstr = Proof_term.short_string pt
      and rdstr = RD.short_string rd
      and cntstr =
        (string_of_int cnt) ^
        (if is_global pc then "global" else "")
      in
      let str =
        (if search then "" else "n") ^
        (if dup then "d" else "") in
      let rstr = str ^ rdstr in
      cntstr ^ "'" ^
      ptstr ^
      (if rstr <> "" then "," else "") ^
      rstr ^
      "' "
    else
      ""
  in
  printf "%s%s%s\n" prefix ext str;
  if is_trace_extended pc then
    printf "%s\t%s\n" prefix (Term.to_string t);
  if is_global pc then printf "\n"




let find_slot (t:term) (pc:t): int * term =
  let least_free = Term.least_free t
  and nslots = Array.length pc.entry.slots in
  let i = ref 0 in
  while !i < nslots
      && least_free < pc.entry.slots.(!i).ndown
  do i:=!i+1 done;
  assert (!i<nslots);
  !i,
  Term.down pc.entry.slots.(!i).ndown t


let find_in_slot (t:term) (pc:t): int =
  let i, ti = find_slot t pc in
  TermMap.find ti pc.entry.slots.(i).sprvd


let find_in_tab (t:term) (nbenv:int) (pc:t): int =
  (** The index of the assertion [t].
   *)
  let sublst = unify_with t 0 nbenv pc.entry.prvd pc in
  match sublst with
    []          -> raise Not_found
  | [(idx,sub)] -> idx
  | _ -> assert false  (* cannot happen, all entries in [prvd] are unique *)


let find (t:term) (pc:t): int = find_in_tab t (nbenv pc) pc



let has (t:term) (pc:t): bool =
  (** Is the term [t] already in the proof context [pc]?
   *)
  try
    let _ = find t pc in
    true
  with Not_found ->
    false


let has_in_view (t:term) (pc:t): bool =
  assert (is_global pc);
  try
    let i = find t pc in
    assert (i < count_global pc);
    if is_private pc then
      true
    else
      let gdesc = Seq.elem i pc.gseq in
      gdesc.pub
  with Not_found ->
    false



let split_equality (t:term) (pc:t): int * term * term =
  Proof_table.split_equality t 0 pc.base


let expand_term (t:term) (pc:t): term =
  Proof_table.expand_term t pc.base


let add_to_equalities (t:term) (idx:int) (pc:t): unit =
  let nbenv = nbenv pc in
  try
    let nargs, left,right = split_equality t pc in
    let is_simpl =
      if 0 < nargs then false (*Term.nodes right < Term.nodes left*)
      else
        let left, right = expand_term left pc, expand_term right pc in
        Term.nodes right < Term.nodes left
    in
    if is_simpl then begin
      (*printf "add_to_equalities %d %s   <%s>\n"
        idx (string_of_term t pc) (Term.to_string t);*)
      pc.entry.left <- Term_table.add left nargs nbenv idx pc.entry.left
    end
  with Not_found ->
    ()


let add_to_proved (t:term) (rd:RD.t) (idx:int) (pc:t): unit =
  pc.entry.prvd  <- Term_table.add t 0 (nbenv pc) idx pc.entry.prvd;
  let nargs,nbenv,t = RD.schematic_term rd in
  pc.entry.prvd2 <- Term_table.add t nargs nbenv idx pc.entry.prvd2



let add_to_forward (rd:RD.t) (idx:int) (pc:t): unit =
  if not (RD.is_forward rd) then
    ()
  else begin
    let nargs,nbenv,t = RD.schematic_premise rd in
    pc.entry.fwd <- Term_table.add t nargs nbenv idx pc.entry.fwd
  end


let add_to_backward (rd:RD.t) (idx:int) (pc:t): unit =
  if not (RD.is_backward rd) then begin
    ()
  end else begin
    let nargs,nbenv,t = RD.schematic_target rd in
    pc.entry.bwd <- Term_table.add t nargs nbenv idx pc.entry.bwd
  end




let add_last_to_tables (pc:t): unit =
  assert (0 < count pc);
  let idx = count pc - 1 in
  let t = term idx pc
  and rd = rule_data idx pc in
  assert (not (has t pc));
  add_to_proved   t rd idx pc;
  add_to_forward  rd idx pc;
  add_to_backward rd idx pc;
  add_to_equalities t idx pc;
  assert (has t pc)


let add_last_to_work (pc:t): unit =
  assert (0 < count pc);
  if not (is_global pc || is_interface_use pc) then
    let idx = count pc - 1 in
    pc.work <- idx :: pc.work



let get_rule_data (t:term) (pc:t): RD.t =
  RD.make t (context pc)


let raw_add0 (t:term) (rd:RD.t) (search:bool) (pc:t): int =
  assert (count pc + 1 = count_base pc);
  let cnt = count pc in
  let res = try find t pc with Not_found -> cnt in
  let dup = res <> cnt in
  if pc.trace then trace_term t rd search dup pc;
  Ass_seq.push rd pc.terms;
  if search && not dup then
    add_last_to_tables pc;
  res


let raw_add (t:term) (search:bool) (pc:t): int =
  raw_add0 t (get_rule_data t pc) search pc






let arguments_of_sub (sub:Term_sub.t) (n_up:int): term array =
  let nargs = Term_sub.count sub in
  let args = Term_sub.arguments nargs sub in
  Array.iteri (fun i t -> args.(i) <- Term.up n_up t) args;
  args



let specialized
    (idx:int) (sub:Term_sub.t) (nbenv_sub:int) (search:bool) (pc:t): int =
  (* The schematic rule [idx] specialized by [sub]. *)
  assert (is_consistent pc);
  assert (idx < count pc);
  let nbenv = nbenv pc in
  assert (nbenv_sub <= nbenv);
  let rd    = rule_data idx pc in
  if RD.is_specialized rd then
    begin assert (Term_sub.count sub = 0); idx end
  else
    let args  = arguments_of_sub sub (nbenv-nbenv_sub) in
    let rd    = RD.specialize rd args idx (context pc) in
    let t     = RD.term rd nbenv in
    try
      find t pc
    with Not_found ->
      Proof_table.add_specialize t idx args pc.base;
      raw_add0 t rd search pc



let find_match (g:term) (pc:t): int =
  let nbenv = nbenv pc in
  let sublst = unify g nbenv pc.entry.prvd2 pc in
  if sublst = [] then raise Not_found;
  try
    let idx,_ = List.find (fun (_,sub) -> Term_sub.is_empty sub) sublst in
    idx
  with Not_found ->
    let idx,sub = List.hd sublst in
    try specialized idx sub nbenv false pc
    with Not_found -> assert false (* specialization not type safe ? *)


let simplified_term (t:term) (below_idx:int) (pc:t): term * Eval.t * bool =
  (* Simplify the term [t] and return the simplified term, the corresponding Eval
     structure and a flag which tells if the term [t] and its simplification are
     different.

     [below_idx]: consider only rules below [below_idx] for equality. *)
  let nbenv = nbenv pc in
  let rec simp t nb =
    let do_subterms t nb =
      let simpl_args args modi =
        let arglst, modi =
          Array.fold_left
            (fun (arglst,modi) a ->
              let asimp,ae,amodi = simp a nb in
              (asimp,ae)::arglst, modi || amodi)
            ([],modi)
            args
        in
        let args, argse = Myarray.split (Array.of_list (List.rev arglst)) in
        args, argse, modi
      in
      match t with
        Variable _ ->
          t, Eval.Term t, false
      | VAppl (i,args) ->
          let args, argse, modi = simpl_args args false in
          VAppl(i,args),
          Eval.VApply(i,argse),
          modi
      | Application(f,args,pr) ->
          let fsimp,fe,fmodi = simp f nb in
          let args, argse, modi = simpl_args args fmodi in
          Application(fsimp, args, pr),
          Eval.Apply(fe,argse,pr),
          modi
      | Lam(n,nms,pres,t0,pr) ->
          let tsimp,te,tmodi = simp t0 (1+nb) in
          Lam(n,nms,pres,tsimp,pr), Eval.Lam(n,nms,pres,te,pr), tmodi
      | QExp(n,nms,t0,is_all) ->
          let tsimp,te,tmodi = simp t0 (n+nb) in
          QExp(n,nms,tsimp,is_all), Eval.QExp(n,nms,te,is_all), tmodi
      | Flow (ctrl,args) ->
          let args, argse, modi = simpl_args args false in
          Flow (ctrl,args),
          Eval.Flow(ctrl,argse),
          modi
    in
    let sublst = unify t (nb+nbenv) pc.entry.left pc in
    let sublst =
      List.filter (fun (idx,sub) -> idx < below_idx && Term_sub.is_empty sub) sublst
    in
    match sublst with
      (idx,_) :: _ ->
        (* Note: This is a workaround. Only single entries in the equality table
                 should be accepted. But multiple entries are possible as long we
                 do not make specializations type safe. *)
        let eq = term_up idx nb pc in
        let nargs, left, right = Proof_table.split_equality eq nb pc.base in
        assert (nargs = 0);
        assert (Term.equivalent t left);
        right, Eval.Simpl(Eval.Term t,idx,[||]), true
    | _ ->
        do_subterms t nb
  in
  let tsimp, te, modi = simp t 0 in
  let ta, tb = Proof_table.reconstruct_evaluation te pc.base in
  assert (ta = t);
  assert (tb = tsimp);
  assert (modi = (tsimp <> t));
  (*if modi then begin
    printf "simplification found\n";
    printf "  term    %s\n" (string_of_term t pc);
    printf "  simpl   %s\n" (string_of_term tsimp pc);
  end;*)
  tsimp, te, modi




let triggers_eval (i:int) (nb:int) (pc:t): bool =
  (* Does the term [Variable i] trigger a full evaluation when used as a top
     level function term, i.e. is it a variable which describes a function
     which has no expansion and is not owned by BOOLEAN? *)
  let nbenv = nb + nbenv pc
  and ft    = feature_table pc in
  i < nbenv ||
  let idx = i - nbenv in
  idx = Feature_table.or_index ||
  Feature_table.owner idx ft <> Class_table.boolean_index



let beta_reduce (n:int) (t:term) (args:term array) (nb:int) (pc:t): term =
  Proof_table.beta_reduce n t args nb pc.base


let evaluated_term (t:term) (below_idx:int) (pc:t): term * Eval.t * bool =
  (* Evaluate the term [t] and return the evaluated term, the corresponding Eval
     structure and a flag which tells if the term [t] and its evaluation are
     different.

     [below_idx]: consider only rules below [below_idx] for equality. *)
  let nbenv = nbenv pc in
  let rec eval (t:term) (nb:int) (full:bool): term * Eval.t * bool =
    let eval_args modi args full =
      let modi_ref = ref modi in
      let args = Array.map
          (fun a ->
            if full then
              let a,e,modi_a = eval a nb full in
              modi_ref := (modi_a || !modi_ref);
              a,e
            else a, Eval.Term a)
          args in
      let args,argse = Myarray.split args in
      args, argse, !modi_ref
    in
    let vapply i args full =
      let args, argse, modi = eval_args false args full in
      let e = Eval.VApply (i,argse) in
      VAppl(i,args), e, modi
    in
    let apply f fe modi args is_pred full =
      let args, argse, modi = eval_args modi args full in
      let e = Eval.Apply (fe,argse,is_pred) in
      match f with
        Lam (n,nms,_,t0,_) ->
          beta_reduce  n t0 args nb pc, Eval.Beta e, true
      | _ ->
          Application (f,args,is_pred), e, modi
    in
    let expand t =
      let domain_id = nb + nbenv + Feature_table.domain_index in
      match t with
        Variable i when i < nb -> t, Eval.Term t, false
      | Variable i ->
          begin try
            let n,nms,t0 = Proof_table.definition i nb pc.base in
            assert (n = 0);
            let res,rese,_ = eval t0 nb full in
            res, Eval.Exp(i,[||],rese), true
          with Not_found ->
            t, Eval.Term t, false
          end
      | VAppl (i,[|Lam(n,nms,pres,t0,pr)|]) when i = domain_id ->
          assert (not pr);
          let args = [|Eval.Term (Lam(n,nms,pres,t0,pr))|]
          and dom = Context.domain_lambda n nms pres nb (context pc) in
          dom, Eval.Exp(i, args, Eval.Term dom), true
      | VAppl (i,args) ->
          begin
            try
              let n,nms,t0 = Proof_table.definition i nb pc.base in
              assert (n = Array.length args);
              let args,argse,_ =
                if full then
                  eval_args true args full
                else
                  args, Array.map (fun t -> Eval.Term t) args, false
              in
              let exp = Proof_table.apply_term t0 args nb pc.base in
              let res,rese,_ =
                if full then
                  eval exp nb full
                else
                  exp, Eval.Term exp, false
              in
              res, Eval.Exp(i,argse,rese), true
            with Not_found ->
              let full = full || triggers_eval i nb pc in
              vapply i args full
          end
      | Application (Variable i,args,pr) when i < nb + nbenv ->
          let f  = Variable i in
          let fe = Eval.Term f in
          apply f fe false args pr true
      | Application (f,args,pr) ->
          let f,fe,fmodi = eval f nb full in
          apply f fe fmodi args pr full
      | Lam (n,nms,pres,t0,pred) ->
          if full then
            let t0,e,tmodi = eval t0 (1+nb) full in
            Lam (n,nms,pres,t0,pred), Eval.Lam (n,nms,pres,e,pred), tmodi
          else
            t, Eval.Term t, false
      | QExp (n,nms,t,is_all) ->
          let full = full || not is_all in
          let t,e,tmodi = eval t (n+nb) full in
          QExp (n,nms,t,is_all), Eval.QExp (n,nms,e,is_all), tmodi
      | Flow (ctrl,args) ->
          let len = Array.length args in
          begin
            match ctrl with
              Ifexp ->
                assert (len = 2 || len = 3);
                if len = 2 then
                  assert false (* nyi *)
                else
                  begin try
                    let idx = find_match args.(0) pc in
                    let fst,fste,_ = eval args.(1) nb full
                    and conde,snde = Eval.Term args.(0), Eval.Term args.(2) in
                    fst, Eval.If(true,idx,[|conde;fste;snde|]), true
                  with Not_found ->
                    begin try
                      let idx = find_match (negation args.(0) pc) pc in
                      let snd,snde,_ = eval args.(2) nb full
                      and conde,fste = Eval.Term args.(0), Eval.Term args.(1) in
                    snd, Eval.If(false,idx,[|conde;fste;snde|]), true
                    with Not_found ->
                      t,
                      Eval.Flow(Ifexp,
                                [|Eval.Term args.(0);
                                  Eval.Term args.(1);
                                  Eval.Term args.(2)|]),
                      false
                    end
                  end
            | Inspect ->
                assert (3 <= len);
                assert (len mod 2 = 1);
                let ncases       = len / 2
                and ft           = feature_table pc
                and nvars        = nb + nbenv
                and insp,inspe,inspmodi = eval args.(0) nb full in
                let rec cases_from (i:int) =
                  if i = ncases then begin (* no match found *)
                    if inspmodi then begin
                      let argse = Array.map (fun t -> Eval.Term t) args
                      and args  = Array.copy args in
                      argse.(0) <- inspe;
                      args.(0)  <- insp;
                      Flow(Inspect,args), Eval.Flow(ctrl,argse), true
                    end else begin
                      t, Eval.Term t, false
                    end
                  end else
                    let n1,_,mtch,_ = Term.qlambda_split_0 args.(2*i+1)
                    and n2,_,res,_  = Term.qlambda_split_0 args.(2*i+2) in
                    assert (n1 = n2);
                    try
                      let sub =
                        Feature_table.case_substitution 0 insp n1 mtch nvars ft in
                      match sub with
                        None ->
                          cases_from (i+1)
                      | Some args ->
                          assert (Array.length args = n2);
                          let res = Term.apply res args in
                          let res1,rese,_ = eval res nb full in
                          res1, Eval.Inspect(t,inspe,i,n1,rese), true
                    with Not_found ->
                      cases_from (i+1)
                in
                cases_from 0
            | Asexp ->
                assert (len = 2);
                let c = context pc
                and n,nms,mtch,_ = Term.qlambda_split_0 args.(1) in
                try
                  let eargs = [|Eval.Term args.(0); Eval.Term args.(1)|] in
                  if Context.is_case_matching args.(0) n mtch nb c then begin
                    Variable (nbenv+Feature_table.true_index),
                    Eval.As(true,eargs),
                    true
                  end else begin
                    Variable (nbenv+Feature_table.false_index),
                    Eval.As(false,eargs),
                    true
                  end
                with Not_found ->
                  t, Eval.Term t, false
          end
    in
    expand t
  in
  let tred,ered,modi = eval t 0 false in
  let ta,tb = Proof_table.reconstruct_evaluation ered pc.base in
  if ta <> t then begin
    printf "t   %s  %s\n" (string_of_term t pc) (Term.to_string t);
    printf "ta  %s  %s\n" (string_of_term ta pc) (Term.to_string ta)
  end;
  assert (ta = t);
  if tb <> tred then begin
    printf "tb   %s\n" (string_of_term tb pc);
    printf "tred %s\n" (string_of_term tred pc)
  end;
  (*if modi then begin
    printf "\nevaluation found\n";
    printf "  term: %s\n" (string_of_term t pc);
    printf "  eval: %s\n\n" (string_of_term tred pc);
  end;*)
  assert (tb = tred);
  assert (modi = (tred <> t));
  tred, ered, modi




let add_mp0 (t:term) (i:int) (j:int) (search:bool) (pc:t): int =
  (* Add the term [t] by applying the modus ponens rule with [i] as the premise
     and [j] as the implication. *)
  let cnt = count pc
  and rd  = RD.drop (rule_data j pc) (context pc)
  in
  Proof_table.add_mp t i j pc.base;
  (if RD.is_implication rd then
    let _ = raw_add0 t rd search pc in ()
  else
    let _ = raw_add t search pc in ());
  cnt



let add_mp (i:int) (j:int) (search:bool) (pc:t): int =
  (* Apply the modus ponens rule with [i] as the premise and [j] as the
     implication. *)
  assert (i < count pc);
  assert (j < count pc);
  let rdj = rule_data j pc
  and nbenv = nbenv pc
  in
  assert (RD.is_specialized rdj);
  assert (RD.is_implication rdj);
  let t = RD.term_b rdj nbenv in
  if not (Proof_table.equivalent (term i pc) (RD.term_a rdj nbenv) pc.base)
  then begin
    printf "add_mp premise     %d %s\n" i (string_of_term_i i pc);
    printf "       implication %d %s\n" j (string_of_term_i j pc);
    printf "       term_a         %s\n" (string_of_term (RD.term_a rdj nbenv) pc)
  end;
  assert (Proof_table.equivalent (term i pc) (RD.term_a rdj nbenv) pc.base);
  try
    find t pc
  with Not_found ->
    add_mp0 t i j search pc


let add_mp_fwd (i:int) (j:int) (pc:t): unit =
  let rdj = rule_data j pc in
  if RD.is_forward rdj then begin
    let cnt = count pc in
    let res = add_mp i j true pc in
    if res = cnt then
      add_last_to_work pc
  end


let is_nbenv_current (i:int) (pc:t): bool =
  assert (i < count pc);
  let nbenv_i = RD.nbenv (rule_data i pc) in
  nbenv_i = nbenv pc


let add_consequence
    (i:int ) (j:int) (sub:Term_sub.t) (pc:t): unit =
  (* Add the consequence of [i] and the implication [j]. The term [j] might
     be a schematic implication which has to be converted into a specific
     implication by using the substitution [sub].

     Note: The substitution [sub] is valid in the environment of the term [i]!
         *)
  assert (is_consistent pc);
  assert (i < count pc);
  assert (j < count pc);
  let nbenv_sub = Proof_table.nbenv_term i pc.base in
  assert (nbenv_sub <= nbenv pc);
  try
    let j = specialized j sub nbenv_sub false pc
    in
    add_mp_fwd i j pc
  with Not_found ->
    ()



let add_consequences_premise (i:int) (pc:t): unit =
  (** Add the consequences of the term [i] by using the term as a premise for
      already available implications.
   *)
  assert (i < count pc);
  assert (is_nbenv_current i pc);
  assert (not (RD.is_intermediate (rule_data i pc)));
  let nbenv = nbenv pc in
  let t,nbenv_t = Proof_table.term i pc.base in
  assert (nbenv = nbenv_t);
  let sublst = unify t nbenv_t pc.entry.fwd pc in
  let sublst = List.rev sublst in
  List.iter
    (fun (idx,sub) ->
      assert (is_consistent pc);
      assert (idx < count pc);
      if is_available idx pc && is_visible idx pc then
        add_consequence i idx sub pc)
    sublst





let add_consequences_implication (i:int) (rd:RD.t) (pc:t): unit =
  (* Add the consequences of the term [i] by using the term as an
     implication and searching for matching premises.
   *)
  assert (i < count pc);
  assert (is_nbenv_current i pc);
  let rd = rule_data i pc
  and nbenv = nbenv pc
  in
  assert (RD.is_implication rd);
  let gp1,nbenv_a,a = RD.schematic_premise rd in
  assert (nbenv_a = nbenv);
  if RD.is_schematic rd then (* the implication is schematic *)
    let sublst = unify_with a gp1 nbenv_a pc.entry.prvd pc
    in
    let sublst = List.rev sublst in
    List.iter
      (fun (idx,sub) ->
        if is_available idx pc && not (RD.is_intermediate (rule_data idx pc)) then
          add_consequence idx i sub pc)
      sublst
  else (* the implication is not schematic *)
    try
      let idx = find a pc in   (* check for exact match *)
      add_mp_fwd idx i pc
    with Not_found -> (* no exact match *)
      let sublst = unify a nbenv_a pc.entry.prvd2 pc
      in
      match sublst with
        [] -> ()
      | (idx,sub)::_ ->
          (* the schematic rule [idx] matches the premise of [i]*)
          begin
            try
              let idx_premise = specialized idx sub nbenv_a false pc in
              add_mp_fwd idx_premise i pc
            with Not_found ->
              ()
          end



let add_fwd_evaluation (t:term) (i:int) (e:Eval.t) (full:bool) (pc:t): int =
  (* Add the term [t] which is an evaluation of the term [i] to the proof context
     if it is not yet in and return the index  *)
  try
    find t pc
  with Not_found ->
    let rd = get_rule_data t pc in
    Proof_table.add_eval t i e pc.base;
    let res = raw_add0 t rd full pc in ();
    if full then add_last_to_work pc;
    res



let add_consequences_evaluation (i:int) (pc:t): unit =
  (* Add the evaluation of the term [i] in case that there is one if
     it is not yet in the proof context [pc] to the proof context and to the
     work items.  *)
  let t = term i pc in
  let add_eval t e =
    try
      let _ = add_fwd_evaluation t i e true pc in ()
    with Not_found ->
      ()
  in
  let t1,e,modi = simplified_term t i pc in
  if modi then
    add_eval t1 e;
  let t1,e,modi = evaluated_term t i pc in
  if modi then
    add_eval t1 e



let add_consequences_someelim (i:int) (pc:t): unit =
  try
    let some_cons = Proof_table.someelim i pc.base in
    if has some_cons pc then
      ()
    else begin
      Proof_table.add_someelim i some_cons pc.base;
      let _ = raw_add some_cons true pc in ();
      add_last_to_work pc
    end
  with Not_found ->
    ()


let add_consequences (i:int) (pc:t): unit =
  (** Add the consequences of the term [i] which are not yet in the proof
      context [pc] to the proof context and to the work items.
   *)
  let rd = rule_data i pc in
  if not (RD.is_intermediate rd) then
    add_consequences_premise i pc;
  if RD.is_implication rd then
    add_consequences_implication i rd pc;
  add_consequences_evaluation i pc;
  add_consequences_someelim  i pc


let clear_work (pc:t): unit =
  pc.work <- []


let close_step (pc:t): unit =
  assert (has_work pc);
  let i = List.hd pc.work in
  pc.work <- List.tl pc.work;
  add_consequences i pc


let prefix (pc:t): string = String.make (2*(depth pc)+2) ' '

(*
let close (pc:t): unit =
  let rec cls (n:int): unit =
    if n > 500 then assert false;  (* 'infinite' loop detection *)
    if has_work pc then begin
      close_step pc;
      cls (n+1)
    end else
      ()
  in
  cls 0;
  assert (not (has_work pc))
*)


let close (pc:t): unit =
  if is_global pc then
    ()
  else
    let cnt0 = count pc in
    let rec cls (round:int): unit =
      if count pc - cnt0 > 500 then assert false; (* 'infinite' loop detection *)
      if has_work pc then begin
        let lst = List.rev pc.work in
      pc.work <- [];
        List.iter (fun i -> add_consequences i pc) lst;
        if is_interface_check pc then
          pc.work <- []
        else
          cls (1+round)
      end
    in
    cls 0


let close_assumptions (pc:t): unit =
  (*pc.work <- List.rev pc.work;*)
  if pc.trace then
    printf "%sproof\n" (trace_prefix_0 pc);
  close pc



let add_assumption_or_axiom (t:term) (is_axiom: bool) (pc:t): int =
  (** Add the term [t] as an assumption or an axiom to the context [pc].
   *)
  assert (is_consistent pc);
  let cnt = count pc in
  let t = Proof_table.prenex_term t pc.base in
  if is_axiom then
    Proof_table.add_axiom t pc.base
  else
    Proof_table.add_assumption t pc.base;
  let _ = raw_add t true pc in ();
  if not is_axiom then
    add_last_to_work pc;
  cnt





let add_assumption (t:term) (pc:t): int =
  (** Add the term [t] as an assumption to the context [pc].
   *)
  add_assumption_or_axiom t false pc



let add_axiom (t:term) (pc:t): int =
  (** Add the term [t] as an axiom to the context [pc].
   *)
  add_assumption_or_axiom t true pc




let push_slots (nbenv:int) (pc:t): unit =
  pc.entry.slots <-
    if nbenv=0 then
      Array.copy pc.entry.slots
    else
      let len = Array.length pc.entry.slots in
      Array.init
        (len+1)
        (fun i ->
          if i<len then
            let sd = pc.entry.slots.(i) in
            {sd with ndown = sd.ndown+nbenv}
          else
            {ndown=0; sprvd=TermMap.empty})


let trace_push (pc:t): unit =
  let str = Proof_table.last_arguments_string pc.base in
  let prefix = trace_prefix_0 pc in
  if str <> "" then printf "%sall%s\n" prefix str;
  printf "%srequire\n" prefix


let trace_pop (pc:t): unit =
  printf "%send\n" (trace_prefix_0 pc)

let trying_goal (g:term) (pc:t): unit =
  if pc.trace then begin
    let prefix = trace_prefix pc in
    printf "%strying to prove: %s\n"
      prefix (string_of_term g pc);
    if is_trace_extended pc then
      printf "%s\t%s\n" prefix (Term.to_string g);
  end


let failed_goal (g:term) (pc:t): unit =
  if pc.trace then
    printf "%sfailure: %s\n"
      (trace_prefix pc) (string_of_term g pc)


let proved_goal (g:term) (pc:t): unit =
  if pc.trace then
    printf "%ssuccess: %s\n"
      (trace_prefix pc) (string_of_term g pc)


let push0 (base:Proof_table.t) (pc:t): t =
  let nbenv = Proof_table.count_variables base in
  let res = {pc with
             base  = base;
             terms = Ass_seq.clone pc.terms;
             work  = pc.work;
             depth = 1 + pc.depth;
             count0 = count pc;
             entry  = copied_entry pc.entry;
             prev   = Some pc} in
  push_slots nbenv res;
  if res.trace then
    trace_push res;
  res


let print_work (pc:t): unit =
  if has_work pc then begin
    printf "open work to close\n";
    List.iter
      (fun i -> printf "  %d %s\n" i (string_of_term_i i pc))
      pc.work
  end


let push
    (entlst:entities list withinfo)
    (rt:return_type)
    (is_pred:bool)
    (is_func:bool)
    (rvar: bool)
    (pc:t): t =
  let base = Proof_table.push entlst rt is_pred is_func rvar pc.base in
  push0 base pc


let push_untyped (names:int array) (pc:t): t =
  let base = Proof_table.push_untyped names pc.base in
  push0 base pc


let pop (pc:t): t =
  assert (is_local pc);
  if pc.trace then
    trace_pop pc;
  match pc.prev with
    None -> assert false
  | Some x -> x


let check_deferred (pc:t): unit = Context.check_deferred (context pc)

let owner (pc:t): int = Context.owner (context pc)

let anchor_class (pc:t): int = Context.anchor_class (context pc)

let variant (i:int) (bcls:int) (cls:int) (pc:t): term =
  Proof_table.variant i bcls cls pc.base


let add_global (defer:bool) (inh:bool) (cls:int) (anchor_cls:int) (pc:t): unit =
  assert (is_global pc);
  if count pc <> Seq.count pc.gseq + 1 then
    printf "add_global count pc = %d, Seq.count pc.gseq = %d\n"
      (count pc) (Seq.count pc.gseq);
  assert (count pc = Seq.count pc.gseq + 1);
  let mt = module_table pc in
  let mdl = Module_table.current mt in
  Seq.push {pub = is_public pc;
            defer = defer;
            inh   = inh;
            cls = cls; anchor_cls = anchor_cls;
            mdl = mdl} pc.gseq;
  assert (count pc = Seq.count pc.gseq)




let inherit_deferred (i:int) (base_cls:int) (cls:int) (info:info) (pc:t): unit =
  (* Inherit the deferred assertion [i] in the class [cls] *)
  assert (i < count_global pc);
  let t = variant i base_cls cls pc in
  let ct = class_table pc in
  if 1 < pc.verbosity then
    printf "   inherit deferred \"%s\" in %s\n"
      (string_of_term t pc)
      (Class_table.class_name cls ct);
  if not (has_in_view t pc) then
    error_info info ("The deferred assertion \""  ^
                     (string_of_term t pc) ^
                     "\" is missing in " ^
                     (Class_table.class_name cls (class_table pc)))



let rec inherit_effective
    (i:int) (base_cls:int) (cls:int) (to_descs:bool) (pc:t): unit =
  (* Inherit the effective assertion [i] in the class [cls] *)
  assert (is_global pc);
  assert (i < count_global pc);
  let t = variant i base_cls cls pc in
  let ct = class_table pc in
  if 1 < pc.verbosity then
    printf "   inherit \"%s\" of \"%s\" in %s\n"
      (string_of_term t pc)
      (Class_table.class_name base_cls ct)
      (Class_table.class_name cls ct);
  if not (has t pc) then begin
    Proof_table.add_inherited t i base_cls cls pc.base;
    let idx = raw_add t true pc in ();
    add_global false true cls cls pc;
    Class_table.add_assertion idx cls false ct;
    if to_descs then
      inherit_to_descendants idx false cls pc
  end

and inherit_to_descendants (i:int) (defer:bool) (owner:int) (pc:t): unit =
  assert (is_global pc);
  assert (owner <> -1);
  let ct = class_table pc in
  let descendants = Class_table.descendants owner ct in
  IntSet.iter
    (fun descendant ->
      assert (not defer); (* deferred assertion cannot be added to class
                             with descendants *)
      inherit_effective i owner descendant false pc)
   descendants






let add_potential_equalities (cls:int) (pc:t): unit =
  let ct = class_table pc in
  let cls_lst1 = Class_table.deferred_assertions cls ct in
  let cls_lst2 = Class_table.effective_assertions cls ct in
  let add_equalities lst =
    let lst = List.rev lst in
    List.iter (fun i -> add_to_equalities (term i pc) i pc) lst in
  add_equalities cls_lst1;
  add_equalities cls_lst2



let inherit_parent
    (cls:int) (par:int) (par_args:type_term array) (info:info) (pc:t): unit =
  let ct = class_table pc in
  let deflst = Class_table.deferred_assertions par ct in
  List.iter (fun i -> inherit_deferred i par cls info pc) (List.rev deflst);
  let efflst = Class_table.effective_assertions par ct in
  List.iter (fun i -> inherit_effective i par cls true pc) (List.rev efflst)



let eval_backward (tgt:term) (imp:term) (e:Eval.t) (pc:t): int =
  (* Add [imp] as an evaluation where [imp] has the form [teval ==> tgt] and
     [teval] is the term [tgt] evaluation with [e]. *)
  Proof_table.add_eval_backward tgt imp e pc.base;
  raw_add imp false pc


let make_lambda (n:int) (nms:int array) (ps: term list) (t:term) (pr:bool) (pc:t)
    : term =
  let c = context pc in
  Context.make_lambda n nms ps t pr c

let tuple_of_args (args: term array) (nb:int) (pc:t): term =
  let c = context pc in
  Context.tuple_of_args args nb c

let make_application (f:term) (args:term array) (nb:int) (pr:bool) (pc:t): term =
  let c = context pc in
  Context.make_application f args nb pr c





(* Subterm equality:

      The goal has the form             lhs  = rhs
      which we can get into the form    f(a1,a2,..) = f(b1,b2,..)
      as a lambda term [f]
      and two argument arrays [a1,a2,..], [b1,b2,..]

      and we have found the leibniz rules  all(p) p(ai) ==> p(bi) for all
      arguments

   start:   f(a1,a2,..) = f(a1,a2,..)                        reflexivity

   step i:  f(a1,a2,..) = f(b1,b2,..,ai,ai+1,..)             start point

            {x: f(a1,a2,..) = f(b1,b2,..,x,ai+1,..)}(ai)     Eval_bwd

            {x:..}(ai) ==> {x:..}(bi)                        specialize leibniz

            {x:..}(bi)                                       modus ponens

            f(a1,a2,..) = f(b1,b2,..,bi,ai+1,..)             Eval

   last:    f(a1,a2,..) = f(b1,b2,..)

   result:  lhs = rhs                                        Eval

*)
let prove_equality (g:term) (pc:t): int =
  let nargs, eq_id, left, right = Context.split_equality g 0 (context pc) in
  let eq_id = nbenv pc + eq_id in
  if 0 < nargs then raise Not_found;
  assert (nargs = 0);
  let imp_id = 1 + imp_id pc in
  let find_leibniz t1 t2 =
    let p t = Application(Variable 0, [|Term.up 1 t|], true) in
    let imp = Term.binary imp_id (p t1) (p t2) in
    let t  = Term.all_quantified 1 [||] imp in
    find t pc
  in
  let tlam, leibniz, args1, args2 =
    Term_algo.compare left right find_leibniz in
  let nargs = Array.length args1 in
  let lam = make_lambda nargs [||] [] tlam false pc in
  assert (nargs = Array.length args2);
  assert (0 < nargs);
  let lam_1up = Term.up 1 lam
  and args1_up1 = Term.array_up 1 args1
  and args2_up1 = Term.array_up 1 args2 in
  try
    let flhs_1up = make_application lam_1up args1_up1 1 false pc
    and frhs_x i =
      let args =
        Array.init nargs
          (fun j ->
            if j < i then args2_up1.(j)
            else if j = i then Variable 0
            else args1_up1.(j)) in
      make_application lam_1up args 1 false pc in
    let pred_inner i = Term.binary (eq_id+1) flhs_1up (frhs_x i)
    in
    let start_term =
      Term.binary eq_id
        (make_application lam args1 0 true pc)
        (make_application lam args1 0 true pc) in
    let start_idx  = find_match start_term pc in
    let result = ref start_idx in
    for i = 0 to nargs - 1 do
      let pred_inner_i = pred_inner i in
      let pred_i = Lam(1,[||],[],pred_inner_i,true) in
      let ai_abstracted =
        make_application pred_i [|args1.(i)|] 0 true pc in
      let imp = implication (term !result pc) ai_abstracted pc in
      let idx2 = eval_backward ai_abstracted imp
          (Eval.Beta (Eval.Term ai_abstracted)) pc in
      let idx = add_mp !result idx2 false pc in
      let sub = Term_sub.singleton 0 pred_i in
      let idx2 = specialized leibniz.(i) sub (nbenv pc) false pc in
      let idx = add_mp idx idx2 false pc in
      let t = Term.apply pred_inner_i [|args2.(i)|]
      and e = Eval.Beta (Eval.Term (term idx pc)) in
      Proof_table.add_eval t idx e pc.base;
      result := raw_add t false pc
    done;
    let e =
      let ev args =
        Eval.Beta (Eval.Term (make_application lam args 0 true pc)) in
      Eval.VApply(eq_id, [|ev args1; ev args2|])
    in
    result := add_fwd_evaluation g !result e false pc;
    !result
  with Not_found ->
    assert false (* cannot happen *)




let backward_witness (t:term) (pc:t): int =
    let nargs,nms,tt = split_some_quantified t pc in
    let sublst  = unify_with tt nargs (nbenv pc) pc.entry.prvd pc in
    let idx,sub = List.find (fun (idx,sub) -> Term_sub.count sub = nargs) sublst
    in
    let witness = term idx pc in
    let impl    = implication witness t pc in
    let args    = Term_sub.arguments nargs sub in
    Proof_table.add_witness impl idx nms tt args pc.base;
    let idx_impl = raw_add impl false pc in
    add_mp0 t idx idx_impl false pc



let find_goal (g:term) (pc:t): int =
  (* Find either an exact match of the goal or a schematic assertion which can
     be fully specialized to match the goal. *)
  try
    find_match g pc
  with Not_found ->
    try backward_witness g pc
    with Not_found ->
      prove_equality g pc




let backward_in_table (g:term) (blacklst: IntSet.t) (pc:t): int list =
  let nbenv = nbenv pc in
  let sublst = unify g nbenv pc.entry.bwd pc in
  let lst =
    List.fold_left
      (fun lst (idx,sub) ->
        if IntSet.mem idx blacklst || not (is_visible idx pc) then
          lst
        else if Term_sub.is_empty sub then
          idx :: lst
        else begin
          let cnt = count pc in
          let idx = specialized idx sub nbenv true pc in
          if idx = cnt then begin
            cnt :: lst
          end else begin
            lst
          end
        end)
      []
      sublst
  in
  List.sort
    (fun i j ->
      let rdi = rule_data i pc
      and rdj = rule_data j pc in
      compare (RD.count_premises rdi) (RD.count_premises rdj))
    lst


let eval_reduce (g:term) (lst:int list) (pc:t): int list =
  let add_eval t e lst =
    let impl = implication t g pc in
    if has impl pc then
      lst
    else
      (eval_backward g impl e pc) :: lst
  in
  let t1,e,modi = simplified_term g (count pc) pc in
  let lst = if modi then add_eval t1 e lst else lst in
  let t1,e,modi = evaluated_term g (count pc) pc in
  if modi then add_eval t1 e lst else lst



let find_backward_goal (g:term) (blacklst:IntSet.t) (pc:t): int list =
  let lst = backward_in_table g blacklst pc in
  let lst = eval_reduce g lst pc in
  if pc.trace && is_trace_extended pc then begin
    let prefix = trace_prefix pc
    and str = intlist_to_string lst in
    printf "%salternatives %s\n" prefix str;
    if not (IntSet.is_empty blacklst) then
      printf "%s   blacklist %s\n" prefix (intset_to_string blacklst) end;
  lst


let assumptions (pc:t): term list =
  Proof_table.assumptions pc.base


let discharged (i:int) (pc:t): term * proof_term =
  (** The [i]th term of the current environment with all local variables and
      assumptions discharged together with its proof term and its base index.
   *)
  Proof_table.discharged i pc.base



let is_proof_pair (t:term) (pt:proof_term) (pc:t): bool =
  Proof_table.is_proof_pair t pt pc.base


let add_proved_0
    (defer:bool) (owner:int)
    (t:term) (pterm:proof_term) (delta:int) (pc:t)
    : int =
  let cnt = count pc
  and ct = class_table pc in
  Proof_table.add_proved t pterm delta pc.base;
  let idx = raw_add t true pc in
  let dup = idx < cnt
  and is_glob = idx < count_global pc
  in
  if not dup || is_glob then (* duplicates of globals must be added to work,
                                because globals are not closed *)
    add_last_to_work pc;
  let anchor_cls = RD.anchor_class (rule_data idx pc) in
  if is_global pc then
    add_global defer false owner anchor_cls pc;
  if is_global pc && owner <> -1 then begin
    let add_assertion idx =
      Class_table.add_assertion idx owner defer ct;
      inherit_to_descendants idx defer owner pc;
      if anchor_cls <> -1 && anchor_cls <> owner then begin
        Class_table.add_assertion idx anchor_cls defer ct;
        inherit_to_descendants idx defer anchor_cls pc
      end
    in
    if dup && is_public pc && not (Seq.elem idx pc.gseq).pub then begin
      (* export the original assertion *)
      add_assertion idx;
      (Seq.elem idx pc.gseq).pub <- true
    end else if not dup then begin
      assert (idx = cnt);
      add_assertion cnt
    end
  end;
  cnt



let add_proved
    (defer:bool)
    (owner:int)
    (t:term)
    (pterm:proof_term)
    (pc:t)
    : int =
  add_proved_0 defer owner t pterm 0 pc




let add_proved_list
    (defer:bool)
    (owner:int)
    (lst: (term*proof_term) list)
    (pc:t)
    : unit =
  let cnt = count pc in
  List.iter
    (fun (t,pt) ->
      let delta = count pc - cnt in
      let _ = add_proved_0 defer owner t pt delta pc in ())
    lst



let previous_schematic (idx:int) (pc:t): int option =
  assert (idx < count pc);
  let rd = rule_data idx pc in
  RD.previous_schematic rd


let premises (idx:int) (pc:t): (term*bool) list =
  assert (idx < count pc);
  let rd    = rule_data idx pc
  and nbenv = nbenv pc in
  assert (RD.is_fully_specialized rd);
  assert (RD.is_implication rd);
  RD.premises rd nbenv



let check_interface (pc:t): unit =
  assert (is_interface_check pc);
  let ft = feature_table pc in
  Feature_table.check_interface ft;
  assert (count pc = Seq.count pc.gseq);
  for i = 0 to count pc - 1 do
    let gdesc = Seq.elem i pc.gseq in
    if gdesc.defer
        && not gdesc.pub
        && Class_table.is_class_public gdesc.cls (class_table pc)
    then
      error_info (FINFO (1,0))
        ("deferred assertion `" ^ (string_of_term (term i pc) pc) ^
         "' is not public")
  done
