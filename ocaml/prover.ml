open Container
open Support
open Term
open Proof
open Printf


module PC = Proof_context


let count_terms (pc:PC.t): int = PC.count pc


let add_assumption (t:term) (pc:PC.t): unit =
  let _ = PC.add_assumption t pc in ()

let close_assumptions (pc:PC.t): unit =
  PC.close_assumptions pc


let push (nms:int array) (pc:PC.t): unit =
  PC.push_untyped nms pc


let push_empty (pc:PC.t): unit =
  push [||] pc


let push_alternative (pc:PC.t): unit =
  push_empty pc;
  close_assumptions pc



let discharge (idx:int) (pc:PC.t): int =
  assert (not (PC.is_global pc));
  let t,pt = PC.discharged idx pc in
  PC.pop pc;
  PC.add_proved false (-1) t pt pc



let rec discharge_downto (i:int) (idx:int) (pc:PC.t): int =
  assert (0 <= i);
  assert (i <= PC.depth pc);
  if PC.depth pc = i then
    idx
  else begin
    let idx = discharge idx pc in
    discharge_downto i idx pc
  end


let rec pop_downto (i:int) (pc:PC.t): unit =
  assert (0 <= i);
  assert (i <= PC.depth pc);
  if PC.depth pc = i then
    ()
  else begin
    PC.pop pc;
    pop_downto i pc
  end



let enter (t:term) (pc:PC.t): term =
  (* Context has to be clean so that assumptions can be pushed. *)
  let rec do_implication (t:term): term =
    try
      let a,b = PC.split_implication t pc in
      add_assumption a pc;
      do_implication b
    with Not_found ->
      close_assumptions pc;
      do_all_quantified t
  and do_all_quantified (t:term): term =
    try
      let n,names,t = PC.split_all_quantified t pc in
      assert (n = Array.length names);
      push names pc;
      do_implication t
    with Not_found ->
      t
  in
  do_implication t






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




(* Todo: Catch all rules shall be used only in one sequence in backward direction.

   Note: A catch all rule is always possible
 *)

let prove (goal:term) (pc:PC.t): int =
  let rec prove0 (goal:term) (black:IntSet.t) (level:int): int =
    assert (level < 20); (* debug: infinite loop detection *)
    let rec alternatives (lst: int list) (goal:term): int =
      let alternative (a_idx:int): int =
        let rec premises (ps:(term*bool) list) (i:int): int =
          match ps with
            [] -> i
          | (p,cons)::ps ->
              let p_idx = prove0 p (calc_blacklist cons a_idx black pc) (level+1) in
              let i = PC.add_mp p_idx i false pc in
              premises ps i
        in
        push_alternative pc;
        let ps = PC.premises a_idx pc in
        let idx = premises ps a_idx in
        discharge idx pc
      in
      match lst with
        [] ->
          PC.failed_goal goal pc;
          raise Not_found
      | idx::lst ->
          let depth = PC.depth pc in
          try
            alternative idx
          with Not_found ->
            pop_downto depth pc;
            alternatives lst goal
    in
    let depth = PC.depth pc in
    push_empty pc;
    let goal = enter goal pc in
    PC.trying_goal goal pc;
    let res =
      try
        PC.find_goal goal pc
      with Not_found ->
        let lst = PC.find_backward_goal goal black pc in
        alternatives lst goal
    in
    PC.proved_goal goal pc;
    let res = discharge_downto depth res pc in
    assert (res < count_terms pc);
    res
  in
  let depth = PC.depth pc in
  try
    let res = prove0 goal IntSet.empty 0 in
    res
  with Not_found ->
    pop_downto depth pc;
    raise Not_found
