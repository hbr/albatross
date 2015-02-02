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


let count_terms (pc:PC.t): int = PC.count pc


let add_assumption (t:term) (pc:PC.t): unit =
  let _ = PC.add_assumption t pc in ()

let close_assumptions (pc:PC.t): unit =
  PC.close_assumptions pc


let push (nms:int array) (pc:PC.t): PC.t =
  PC.push_untyped nms pc


let push_empty (pc:PC.t): PC.t =
  push [||] pc


let discharge (idx:int) (pc:PC.t): int * PC.t =
  assert (not (PC.is_global pc));
  let t,pt = PC.discharged idx pc in
  let pc = PC.pop pc in
  let idx = PC.add_proved false (-1) t pt pc in
  idx, pc



let rec discharge_downto (i:int) (idx:int) (pc:PC.t): int * PC.t =
  assert (0 <= i);
  assert (i <= PC.depth pc);
  if PC.depth pc = i then
    idx, pc
  else begin
    let idx,pc = discharge idx pc in
    discharge_downto i idx pc
  end



let enter (t:term) (pc:PC.t): term * PC.t =
  (* Context has to be clean so that assumptions can be pushed. *)
  let rec do_implication (t:term) (pc:PC.t): term * PC.t =
    try
      let a,b = PC.split_implication t pc in
      add_assumption a pc;
      do_implication b pc
    with Not_found ->
      close_assumptions pc;
      do_all_quantified t pc
  and do_all_quantified (t:term) (pc:PC.t): term * PC.t =
    try
      let n,names,t = PC.split_all_quantified t pc in
      assert (n = Array.length names);
      let pc = push names pc in
      do_implication t pc
    with Not_found ->
      t, pc
  in
  do_implication t pc






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

let prove (goal:term) (strength:int) (pc:PC.t): int =
  let rec prove0 (goal:term) (black:IntSet.t) (level:int) (pc:PC.t): int =
    assert (level < 20); (* debug: infinite loop detection *)
    let rec alternatives (lst: int list) (goal:term) (pc:PC.t): int =
      let alternative (a_idx:int) (pc:PC.t): int =
        let rec premises (ps:(term*bool) list) (i:int) (pc:PC.t): int =
          match ps with
            [] -> i
          | (p,cons)::ps ->
              let p_idx =
                prove0 p (calc_blacklist cons a_idx black pc) (level+1) pc in
              let i = PC.add_mp p_idx i false pc in
              premises ps i pc
        in
        let pc = push_empty pc in
        let ps = PC.premises a_idx pc in
        let idx = premises ps a_idx pc in
        let idx,_ = discharge idx pc in
        idx
      in
      match lst with
        [] ->
          PC.failed_goal goal pc;
          raise Not_found
      | idx::lst ->
          try
            alternative idx pc
          with Not_found ->
            alternatives lst goal pc
    in
    let depth = PC.depth pc in
    let pc = push_empty pc in
    let goal,pc = enter goal pc in
    PC.trying_goal goal pc;
    let res =
      try
        PC.find_goal goal pc
      with Not_found ->
        if strength = 0 && 1 <= level then
          raise Not_found;
        let lst = PC.find_backward_goal goal black pc in
        alternatives lst goal pc
    in
    PC.proved_goal goal pc;
    let res,pc = discharge_downto depth res pc in
    assert (res < count_terms pc);
    res
  in
  prove0 goal IntSet.empty 0 pc
