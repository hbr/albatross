(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Proof
open Printf

module PC = Proof_context


type context = {pc:PC.t; mutable map: int TermMap.t}

type alternative = {
    premises: (int*int) array;   (* subgoal,idx *)
    mutable npremises: int;      (* number of premises still to prove *)
    bwd_idx: int                 (* index of the backward rule *)
  }



type goal = {
    goal: term;
    ctxt: context;
    black:  IntSet.t;
    mutable target:   term;
    mutable tgt_ctxt: context;
    mutable visited:  bool;
    mutable parent:  (int*int*int) option;  (* parent, alternative, subgoal *)
    mutable alternatives: alternative array;
    mutable nfailed: int;  (* number of failed alternatives *)
    mutable pos: int;
    mutable obsolete: bool
  }


type t = {
    goals: goal Seq.t;
    verbosity: int;
    trace:     bool;
  }



let goal_limit_ref = ref 200

let goal_limit () = !goal_limit_ref


let goal (g:term) (black:IntSet.t) (par:(int*int*int) option) (pc: PC.t): goal =
  (*assert (PC.is_well_typed g pc);*)
  let c = {pc=pc; map = TermMap.empty} in
  {goal      = g;
   ctxt      = c;
   black     = black;
   target    = g;
   tgt_ctxt  = c;
   visited   = false;
   parent    = par;
   alternatives = [||];
   nfailed   = 0;
   pos       = -1;
   obsolete = false
 }



let root_goal (g:term) (pc: PC.t): goal =
  goal g IntSet.empty None pc


exception Root_succeeded



let count (gs:t): int = Seq.count gs.goals


let item (i:int) (gs:t): goal =
  assert (i < count gs);
  Seq.elem i gs.goals


let has_succeeded (i:int) (gs:t): bool =
  (item i gs).pos <> -1


let is_visitable (i:int) (gs:t): bool =
  let g = item i gs in
  not (g.visited || g.obsolete)



let init (g:term) (pc:PC.t): t =
  {goals = Seq.singleton (root_goal g pc);
   verbosity = PC.verbosity pc;
   trace     = PC.is_tracing pc}




let rec set_obsolete (i:int) (gs:t): unit =
  let g = item i gs in
  g.obsolete <- true;
  for ialt = g.nfailed to Array.length g.alternatives - 1 do
    set_obsolete_alternative ialt i gs
  done

and set_obsolete_alternative (ialt:int) (i:int) (gs:t): unit =
  let g   = item i gs in
  let alt = g.alternatives.(ialt) in
  Array.iter (fun (p,pos) -> if pos = -1 then set_obsolete p gs) alt.premises



let rec set_failed (i:int) (gs:t): unit =
  (* The goal [i] has failed. If the goal is the root goal then the whole proof is
     failed.

     If the goal is not the root goal then it belongs to an alternative of its parent.
     The alternative is failed. All other subgoals of the parent become obsolete. If
     the alternative is the last alternative then the parent fails as well.
   *)
  let g = item i gs in
  if gs.trace then begin
    let prefix = PC.trace_prefix g.ctxt.pc in
    printf "%sfailed  goal %d: %s\n" prefix i (PC.string_of_term g.goal g.ctxt.pc);
  end;
  match g.parent with
    None ->
      assert (i = 0);
      raise (Proof_failed "")
  | Some (ipar,ialt,isub) ->
      let par = item ipar gs in
      par.nfailed <- 1 + par.nfailed;
      set_obsolete_alternative ialt ipar gs;
      if par.nfailed = Array.length par.alternatives then
        set_failed ipar gs

let pc_discharged (pos:int) (pc:PC.t): term * proof_term =
  try
    PC.discharged pos pc
  with Not_found ->
    assert false (* cannot happen in generated proof *)

let discharged (pos:int) (pc:PC.t): int * PC.t =
  let t,pt = pc_discharged pos pc
  and cnt0 = PC.count_previous pc
  and pc = PC.pop pc in
  assert (cnt0 <= PC.count pc);
  let delta = PC.count pc - cnt0 in
  let pos = PC.add_proved_0 false (-1) t pt delta pc in
  PC.clear_work pc;
  pos, pc



let discharge_target (pos:int) (g:goal): unit =
  (* The target of the goal [g] has succeeded and it is at [pos] in the target
     context. The target has to be discharged with all variables and assumptions and
     the discharged term and proof term has to be inserted into the goal context *)
  let depth = PC.depth g.ctxt.pc in
  let rec discharge pos pc =
    if PC.depth pc = depth then
      pos
    else
      let pos, pc = discharged pos pc in
      discharge pos pc
  in
  let pos = discharge pos g.tgt_ctxt.pc in
  g.pos <- pos


let succeed_alternative (ialt:int) (g:goal): int =
  let alt = g.alternatives.(ialt) in
  let n   = Array.length alt.premises in
  let rec premise (i:int) (a_idx:int): int =
    if i = n then
      a_idx
    else begin
      let _,pos = alt.premises.(i) in
      assert (0 <= pos);
      let a_idx = PC.add_mp pos a_idx false g.tgt_ctxt.pc in
      premise (i+1) a_idx
    end
  in
  premise 0 alt.bwd_idx


let rec set_succeeded (i:int) (gs:t): unit =
  (* The goal [i] has succeeded. If the goal is the root goal then the proof is done.
     If the goal is not the root goal then it belongs to an alternative of its parent.
   *)
  let g = item i gs in
  if gs.trace then begin
    let prefix = PC.trace_prefix g.ctxt.pc in
    printf "%ssuccess goal %d: %s\n"
      prefix i (PC.string_long_of_term g.goal g.ctxt.pc);
  end;
  assert (0 <= g.pos);
  assert (g.pos < PC.count g.ctxt.pc);
  match g.parent with
    None ->
      assert (i = 0);
      raise Root_succeeded
  | Some (ipar,ialt,isub) ->
      let par = item ipar gs in
      assert (ialt < Array.length par.alternatives);
      let alt = par.alternatives.(ialt) in
      assert (isub < Array.length alt.premises);
      let p,pos = alt.premises.(isub) in
      assert (p = i);
      assert (pos = -1);
      assert (0 < alt.npremises);
      alt.premises.(isub) <- p,g.pos;
      alt.npremises <- alt.npremises - 1;
      if alt.npremises = 0 then begin
        let pos = succeed_alternative ialt par in
        discharge_target pos par;
        set_succeeded ipar gs;
        for jalt = 0 to Array.length par.alternatives - 1 do
          if jalt <> ialt then
            set_obsolete_alternative jalt ipar gs
        done
      end





let push_premise (shared:bool) (g:goal): unit =
  let pc = g.tgt_ctxt.pc in
  let a,b = PC.split_implication g.target pc in
  let pc =
    if shared then begin
      let pc = PC.push_untyped [||] pc in
      g.tgt_ctxt <- {pc=pc; map = TermMap.empty};
      pc
    end else
      pc
  in
  let _ = PC.add_assumption a true pc in
  g.target <- b





let push_variables (g:goal): unit =
  let pc = g.tgt_ctxt.pc in
  let n,tps,fgs,t = Term.all_quantifier_split g.target in
  let pc = PC.push_typed tps fgs pc in
  g.tgt_ctxt <- {pc = pc; map = TermMap.empty};
  g.target   <- t





let enter (i:int) (gs:t): unit =
  let g = Seq.elem i gs.goals in
  let rec do_implication (shared:bool): unit =
    try
      push_premise shared g;
      do_implication false
    with Not_found ->
      if not shared then
        PC.close_assumptions g.tgt_ctxt.pc;
      do_all_quantified ()
  and do_all_quantified (): unit =
    try
      push_variables g;
      do_implication false
    with Not_found ->
      ()
  in
  do_implication true




let prove_trivially (g:goal): unit =
  let idx = PC.find_goal g.target g.tgt_ctxt.pc in
  discharge_target idx g




let calc_blacklist (cons:bool) (idx:int) (used:IntSet.t) (pc:PC.t): IntSet.t =
  let used =
    if cons then used
    else
      match PC.previous_schematic idx pc with
        None -> used
      | Some prev ->
          IntSet.add prev used
  in
  IntSet.add idx used




let trace_target_subgoals (i:int) (gs:t): unit =
  let g = item i gs in
  let pc = g.tgt_ctxt.pc in
  let prefix = PC.trace_prefix pc in
  printf "%starget %d: %s\n" prefix i (PC.string_of_term g.target pc);
  for ialt = 0 to Array.length g.alternatives - 1 do
    let alt = g.alternatives.(ialt) in
    Array.iter
      (fun (i,_) ->
        let sg = item i gs in
        printf "%s  %2d subgoal %d: %s\n"
          prefix ialt i (PC.string_of_term sg.goal sg.ctxt.pc))
      alt.premises
  done


let generate_subgoal
    (p:term) (cons:bool) (j:int) (j_idx:int) (jsub:int) (i:int) (gs:t): int =
  (* Generate a subgoal with the term [p] where [cons] indicates if the
     subgoal is conservative for the alternative [j] of the goal [i]. *)
  let cnt = count gs in
  let g   = item i gs in
  let black =
    calc_blacklist cons j_idx g.black g.tgt_ctxt.pc
  in
  let sub = goal p black (Some (i,j,jsub)) g.tgt_ctxt.pc in
  let ctxt = g.tgt_ctxt in
  begin try
    let isub = TermMap.find p ctxt.map in
    if gs.trace then
      printf "%sduplicate subgoal %d: %s at %d\n"
        (PC.trace_prefix ctxt.pc)
        isub (PC.string_of_term p ctxt.pc) cnt
  with Not_found ->
    ctxt.map <- TermMap.add p cnt ctxt.map
  end;
  Seq.push sub gs.goals;
  cnt



let generate_subgoals (i:int) (gs:t): unit =
  (* Generate the subgoals of all alternatives of the goal [i]. *)
  let g     = item i gs in
  let alts = PC.find_backward_goal g.target g.black g.tgt_ctxt.pc in
  let _, alts =
    List.fold_left (* all alternatives *)
      (fun (j,alts) bwd_idx ->
        let ps = PC.premises bwd_idx g.tgt_ctxt.pc in
        let ps,npremises =
          List.fold_left (* all premises i.e. subgoals *)
            (fun (ps,jsub) (p,cons) ->
              (generate_subgoal p cons j bwd_idx jsub i gs,-1) :: ps,
              jsub+1)
            ([],0)
            ps
        in
        let ps = List.rev ps in
        let ps = Array.of_list ps in
        (j+1), {premises = ps; bwd_idx = bwd_idx; npremises = npremises} :: alts)
      (0,[])
      alts
  in
  g.alternatives <- Array.of_list (List.rev alts);
  if Array.length g.alternatives = 0 then
    set_failed i gs;
  if gs.trace then trace_target_subgoals i gs



let ancestors (i:int) (gs:t): int list =
  let rec ancs i lst =
    let g = item i gs in
    match g.parent with
      None -> i :: lst
    | Some (ipar,_,_) ->
        ancs ipar (i::lst)
  in
  ancs i []


let trace_ancestors (i:int) (gs:t): unit =
  let g = item i gs in
  let ancs = ancestors i gs in
  let str = String.concat "," (List.map string_of_int ancs) in
  let prefix = PC.trace_prefix g.ctxt.pc in
  printf "%sancestors [%s]\n" prefix str


let trace_visit (i:int) (gs:t): unit =
  let g = item i gs in
  let prefix = PC.trace_prefix g.ctxt.pc in
  printf "\n%svisit goal %d: %s\n"
    prefix i
    (PC.string_long_of_term g.goal g.ctxt.pc);
  printf "                     %s\n" (Term.to_string g.goal);
  match g.parent with
    None -> ()
  | Some (ipar,ialt,isub) ->
      let par = item ipar gs in
      trace_ancestors i gs;
      printf "%s  parent %d %s\n" prefix ipar
        (PC.string_of_term par.goal par.ctxt.pc);
      if par.goal <> par.target then
        printf "%s  parent target %s\n"
          prefix (PC.string_of_term par.target par.tgt_ctxt.pc)(*;
      let alt = par.alternatives.(ialt) in
      printf "%salternative   %s\n"
        prefix (PC.string_of_term_i alt.a_idx par.tgt_ctxt)*)




let visit (i:int) (gs:t): unit =
  assert (i < count gs);
  assert (is_visitable i gs);
  assert (not (has_succeeded i gs));
  let g = item i gs in
  if gs.trace then trace_visit i gs;
  g.visited <- true;
  try
    prove_trivially g;
    set_succeeded i gs
  with Not_found ->
    enter i gs;
    try
      prove_trivially g;
      set_succeeded i gs
    with Not_found ->
      generate_subgoals i gs



let proof_term (g:term) (pc:PC.t): term * proof_term =
  let pc = PC.push_untyped [||] pc in
  PC.close_assumptions pc;
  let gs = init g pc in
  if gs.trace then begin
    printf "\n%strying to prove: %s\n"
      (PC.trace_prefix pc)
      (PC.string_long_of_term g pc);
    if PC.verbosity pc > 3 then
      printf "%s                 %s\n"
        (PC.trace_prefix pc)
        (Term.to_string g);
    printf "\n"
  end;
  if not (PC.is_global pc) then
    PC.close pc;
  let rec round (i:int) (start:int): unit =
    if PC.is_interface_check pc && 1 < i then
      raise (Proof_failed "");
    if goal_limit () <= start then
      raise (Proof_failed (", goal limit " ^ (string_of_int (goal_limit())) ^
                           " exceeded"));
    let cnt = count gs in
    if PC.is_tracing pc then
      printf "%s-- round %d with %d goals --\n" (PC.trace_prefix pc) i (cnt - start);
    for j = start to cnt - 1 do
      if is_visitable j gs then
        visit j gs
    done;
    assert (cnt < count gs);
    if PC.is_tracing pc then printf "\n";
    round (i+1) cnt
  in
  try
    round 0 0;
    assert false (* shall not happen, because either we succeed or we fail,
                    but we cannot fall through *)
  with Root_succeeded ->
    let g = item 0 gs in
    assert (0 <= g.pos);
    assert (g.pos < PC.count g.ctxt.pc);
    pc_discharged g.pos g.ctxt.pc




let is_provable (g:term) (pc:PC.t): bool =
  try
    let _ = proof_term g pc in true
  with Proof_failed _ ->
    false


let prove (g:term) (pc:PC.t): unit =
  let _ = proof_term g pc in ()


let prove_and_insert (g:term) (pc:PC.t): int =
  let t,pt = proof_term g pc in
  PC.add_proved_0 false (-1) t pt 0 pc
