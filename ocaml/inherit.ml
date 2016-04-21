(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term
open Container
open Signature
open Printf

module FT = Feature_table
module PC = Proof_context

type parent_descriptor = Class_table.parent_descriptor

let class_table (pc:PC.t):Class_table.t =
  PC.class_table pc


let inherit_deferred (i:int) (cls:int) (is_ghost:bool) (info:info) (pc:PC.t): unit =
  (* Inherit the deferred feature [i] in the class [cls]

     [is_ghost] flags if the inheritance is a ghost inheritance
   *)
  let ft = PC.feature_table pc in
  assert (cls <> Feature_table.class_of_feature i ft);
  let idx,ags =
    try
      Feature_table.find_variant_candidate i cls ft
    with Not_found ->
      let ct   = class_table pc  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " does not have a feature unifiable with \"" ^
        (Feature_table.string_of_signature i ft) ^
        "\" with proper substitutions of the type variables" in
      error_info info str
  in
  if 1 < Feature_table.verbosity ft then begin
    let ct   = class_table pc in
    let icls = Feature_table.class_of_feature i ft in
    printf "   inherit deferred \"%s %s (%d)\" in %s (%d)\n"
      (Class_table.class_name icls ct)
      (Feature_table.string_of_signature i ft)
      i
      (Class_table.class_name cls ct) idx end;
  let is_i_ghost   = Feature_table.is_ghost_function i ft
  and is_idx_ghost = Feature_table.is_ghost_function idx ft in
  if is_idx_ghost && not is_i_ghost && not is_ghost then
    error_info info "Must be ghost inheritance";
  Feature_table.inherit_feature i ags idx cls false ft





let prove (t:term) (pc:PC.t): unit =
  if PC.is_interface_use pc then
    ()
  else begin
    let _ = Prover.proof_term t pc in
    ()
  end



let check_validity (i:int) (idx:int) (cls:int) (info:info) (pc:PC.t): unit =
  (* Check the validity of the feature [i] with inherited inherited variant [idx] in
     the class [cls] *)
  let ft = PC.feature_table pc
  and ct = class_table pc in
  let class_name cls  = Class_table.class_name cls ct
  and feat_sign  i    = Feature_table.string_of_signature i ft
  and result_class i  =
    let tvs,sign = Feature_table.signature i ft in
    assert (Sign.has_result sign);
    Tvars.principal_class (Sign.result sign) tvs
  in
  let specs =
    try Feature_table.specification i ft
    with Not_found ->
      assert (Feature_table.has_definition i ft);
      let res_cls = result_class i  in
      assert (Class_table.descends_from_any res_cls ct);
      let str =
        "Cannot prove validity of \"" ^ (feat_sign i) ^
        " in class " ^ (class_name cls) ^
        " because class " ^ (class_name res_cls) ^
        "(" ^ (string_of_int res_cls) ^ ")" ^
        " does not inherit ANY" in
      error_info info str
  in
  let icls = Feature_table.class_of_feature i ft in
  let error_string spec_term =
    "The class " ^ (class_name cls) ^ " redefines the feature \"" ^
    (feat_sign i) ^ "\" of class " ^ (class_name icls) ^
    " but the validity of the specification\n   " ^
    (Feature_table.term_to_string spec_term true 0 [||] ft) ^
    "\ncannot be proven"
  in
  assert (specs <> [] );
  List.iter
    (fun spec ->
      let spec = Feature_table.variant_term spec 0 icls cls ft in
      try
        prove spec pc
      with Proof.Proof_failed msg ->
        error_info info ((error_string spec) ^ msg))
    specs



let rec inherit_effective
    (i:int) (cls:int) (ghost:bool) (to_descs:bool) (info:info) (pc:PC.t): unit =
  (* Inherit the effective feature [i] in the class [cls]

     [ghost]:    inheritance is a ghost inheritance
     [to_descs]: the feature has to be inherited to the descendants of [cls] as well.
   *)
  let ft = Proof_context.feature_table pc
  in
  assert (not (Feature_table.is_interface_check ft));
  if not (Feature_table.has_anchor i ft) || Feature_table.has_variant i cls ft
  then
    ()
  else begin
    if 1 < Feature_table.verbosity ft then begin
      let ct   = class_table pc in
      let icls = Feature_table.class_of_feature i ft in
      printf "   inherit effective \"%s %s\" in %s\n"
        (Class_table.class_name icls ct)
        (Feature_table.string_of_signature i ft)
        (Class_table.class_name cls ct)
    end;
    assert (not (Feature_table.has_variant i cls ft));
    begin try
      let idx,ags = Feature_table.find_variant_candidate i cls ft in
      Feature_table.inherit_feature i ags idx cls false ft;
      check_validity i idx cls info pc
    with Not_found ->
      ()
        (*let idx = Feature_table.inherit_new_effective i cls ghost ft in
          if to_descs then
          inherit_to_descendants idx info pc*)
    end
  end

and inherit_to_descendants (i:int) (info:info) (pc:PC.t): unit =
  let ft = PC.feature_table pc in
  if not (Feature_table.is_interface_check ft && Feature_table.has_anchor i ft)
  then
    let ct  = class_table pc in
    let cls = Feature_table.class_of_feature i ft in
    let descendants = Class_table.descendants cls ct in
    IntSet.iter
      (fun heir ->
        assert (not (Feature_table.is_deferred i ft)); (* no new deferred allowed
                                                          if class has descendants *)
        let ghost = Class_table.is_ghost_ancestor heir cls ct in
        inherit_effective i heir ghost false info pc)
      descendants






let inherit_features
    (cls:int)
    (par:int) (par_args:type_term array) (ghost:bool)
    (info:info) (pc:PC.t): unit =
  (* Inherit in the class [cls] the features from the parent [par[par_args]] where
     [ghost] indicates if the inheritance relation is a ghost inheritance. *)
  let ct = Proof_context.class_table pc
  in
  let defs = List.rev (Class_table.deferred_features par ct) in
  List.iter (fun i -> inherit_deferred i cls ghost info pc) defs;
  let effs = List.rev (Class_table.effective_features par ct) in
  List.iter (fun i -> inherit_effective i cls ghost true info pc) effs




let inherit_parent (cls:int) (parent:parent) (pc:PC.t): unit =
  let ct = PC.class_table pc
  and ft = PC.feature_table pc in
  let ghost,tp,renames = parent in
  if renames <> [] then
    not_yet_implemented tp.i "rename";
  assert (renames = [] ); (* nyi: feature adaption *)
  let par, par_args = Class_table.parent_type cls tp ct in
  if Class_table.has_ancestor cls par ct then
    ()
  else if Class_table.has_ancestor par cls ct then
    error_info tp.i "circular inheritance"
  else begin
    assert false
  end


let inherit_parents (cls:int) (clause:inherit_clause) (pc:PC.t): unit =
  let ct = PC.class_table pc
  and ft = PC.feature_table pc in
  let has_any =
    ref (PC.is_public pc || Class_table.inherits_any cls ct) in
  List.iter
    (fun (ghost,tp,renames) ->
      if renames <> [] then
        not_yet_implemented tp.i "rename";
      assert (renames = [] ); (* nyi: feature adaption *)
      let par, par_args = Class_table.parent_type cls tp ct in
      if Class_table.has_ancestor cls par ct then
        ()
      else if Class_table.has_ancestor par cls ct then
        error_info tp.i "circular inheritance"
      else begin
        if Class_table.is_interface_check ct &&
          not (Class_table.has_ancestor cls par ct) then
          error_info tp.i ("Class " ^ (Class_table.class_name cls ct) ^
                           " does not inherit "  ^
                           (Class_table.class_name par ct) ^
                           " in implementation file");
        if par <> Class_table.any_index &&
          not (Class_table.inherits_any par ct) then
          error_info tp.i ("Class " ^ (Class_table.class_name par ct) ^
                           " does not inherit ANY");
        if 1 < Feature_table.verbosity ft then
          printf "   inherit %s in %s\n"
            (Class_table.class_name par ct) (Class_table.class_name cls ct);
        if not (Class_table.is_interface_check ct) then
          Class_table.inherit_parent cls par par_args ghost tp.i ct;
        inherit_features cls par par_args ghost tp.i pc;
        PC.inherit_parent cls par par_args tp.i pc;
        if not !has_any && Class_table.inherits_any cls ct then begin
          has_any := true;
          PC.add_potential_equalities cls pc
        end
      end)
    clause
