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
  if 1 < Feature_table.verbosity ft then begin
    let ct   = class_table pc in
    let icls = Feature_table.class_of_feature i ft in
    printf "   inherit deferred \"%s %s\" in %s\n"
      (Class_table.class_name icls ct)
      (Feature_table.string_of_signature i ft)
      (Class_table.class_name cls ct) end;
  assert (cls <> Feature_table.class_of_feature i ft);
  let idx =
    try Feature_table.find_variant_candidate i cls ft
    with Not_found ->
      let ct   = class_table pc  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " does not have a feature unifiable with \"" ^
        (Feature_table.string_of_signature i ft) ^
        "\" with proper substitutions of the type variables" in
      error_info info str
  in
  let is_i_ghost   = Feature_table.is_ghost_function i ft
  and is_idx_ghost = Feature_table.is_ghost_function idx ft in
  if is_idx_ghost && not is_i_ghost && not is_ghost then
    error_info info "Must be ghost inheritance";
  Feature_table.inherit_feature i idx cls false ft





let prove (t:term) (pc:PC.t): unit =
  if PC.is_interface_use pc then
    ()
  else begin
    let ifc_check = PC.is_interface_check pc
    and strength  = PC.prover_strength pc
    in
    let push () =
      if ifc_check then PC.push_untyped [||] pc
    and pop () =
      if ifc_check then PC.pop pc
    in
    try
      push ();
      let _ = Prover.prove t strength pc in
      pop ()
    with Not_found ->
      pop ();
      raise Not_found
  end



let inherit_effective (i:int) (cls:int) (info:info) (pc:PC.t): unit =
  let ft = PC.feature_table pc in
  let ct = class_table pc in
  let class_name cls  = Class_table.class_name cls ct
  and feat_sign  i    = Feature_table.string_of_signature i ft
  and result_class i  =
    let tvs,sign = Feature_table.signature i ft in
    assert (Sign.has_result sign);
    Tvars.principal_class (Sign.result sign) tvs
  in
  if not (Feature_table.has_anchor i ft) then
    ()
  else begin
    if 1 < Feature_table.verbosity ft then begin
      let icls = Feature_table.class_of_feature i ft in
      printf "   inherit \"%s %s\" in %s\n"
        (class_name icls) (feat_sign i) (class_name cls) end;
    try
      let idx = Feature_table.find_variant_candidate i cls ft in
      Feature_table.inherit_feature i idx cls false ft;
      let eq_term =
        try Feature_table.definition_equality i ft
        with Not_found ->
          assert (Feature_table.has_definition i ft);
          let res_cls = result_class i  in
          assert (Class_table.has_ancestor res_cls Class_table.any_index ct);
          let str =
            "Cannot prove equivalence of \"" ^ (feat_sign idx) ^ "\" and \"" ^
            (feat_sign i) ^ " because class " ^ (class_name res_cls) ^
            "(" ^ (string_of_int res_cls) ^ ")" ^
            " does not inherit ANY" in
          error_info info str
      in
      let icls = Feature_table.class_of_feature i ft in
      let var_eq_term = Feature_table.variant_term eq_term 0 icls cls ft in
      begin try
        prove var_eq_term pc
      with Not_found ->
        let str =
          "The class " ^ (class_name cls) ^ " redefines the feature \"" ^
          (feat_sign i) ^ "\" of class " ^ (class_name icls) ^
          " but the equivalence of the definitions i.e.\n   " ^
          (Feature_table.term_to_string var_eq_term 0 [||] ft) ^
          "\ncannot be proven"
        in
        error_info info str
      end
    with Not_found ->
      Feature_table.inherit_effective i cls ft
  end






let inherit_to_descendants (i:int) (info:info) (pc:PC.t): unit =
  let ft = PC.feature_table pc in
  if not (Feature_table.is_deferred i ft) && Feature_table.has_anchor i ft then
    let ct = class_table pc in
    let cls = Feature_table.class_of_feature i ft in
    let descendants = Class_table.descendants cls ct in
    IntSet.iter
      (fun cls -> inherit_effective i cls info pc)
      descendants





let do_inherit
    (cls:int)
    (anc_lst: (int * parent_descriptor) list)
    (info:info)
    (pc:PC.t)
    : unit =
  (* For all ancestors in the list [anc_lst]:

     Go through all deferred features of the parent class [par_idx] and verify
     that the class [cls] has all these deferred features.

     Then inherit all effective features of the class [par_idx] into the class
     [cls_idx]
   *)
  let ct = class_table pc in
  List.iter
    (fun (par,(is_ghost,_)) ->
      let flst = Class_table.deferred_features par ct in
      List.iter (fun i -> inherit_deferred i cls is_ghost info pc) (List.rev flst);
      let flst = Class_table.effective_features par ct in
      List.iter (fun i -> inherit_effective i cls info pc) (List.rev flst)
    )
    anc_lst




let export_inherited_variant (i:int) (cls:int) (pc:PC.t): unit =
  (* Export the inherited variant of the feature [i] in the class [cls] *)
  let ft = PC.feature_table pc in
  assert (Feature_table.is_interface_check ft);
  if Feature_table.has_anchor i ft then
    try
      let idx = Feature_table.private_variant i cls ft in
      Feature_table.export_feature idx ft;
      Feature_table.inherit_feature i idx cls true ft
    with Not_found ->
      assert (not (Feature_table.is_deferred i ft));
      assert (not (Feature_table.has_variant i cls ft));
      inherit_effective i cls UNKNOWN pc



let export_inherited
    (cls:int)
    (anc_lst: (int * parent_descriptor) list)
    (pc:PC.t)
    : unit =
  (* Export all inherited features from all classes in the ancestor list [anc_lst]
     in the class [cls] *)
  let ct = class_table pc in
  List.iter
    (fun (par,par_args) ->
      let flst = Class_table.deferred_features par ct in
      List.iter (fun i -> export_inherited_variant i cls pc) (List.rev flst);
      let flst = Class_table.effective_features par ct in
      List.iter (fun i -> export_inherited_variant i cls pc) (List.rev flst))
    anc_lst


let inherit_to_descendants (i:int) (info:info) (pc:PC.t): unit =
  let ft = PC.feature_table pc in
  if not (Feature_table.is_deferred i ft) &&  Feature_table.has_anchor i ft then
    let ct  = class_table pc in
    let cls = Feature_table.class_of_feature i ft in
    let descendants = Class_table.descendants cls ct in
    IntSet.iter
      (fun cls -> inherit_effective i cls info pc)
      descendants




let check_base_features (cls:int) (pc:PC.t): unit =
  let ct  = class_table pc
  and ft  = PC.feature_table pc in
  let lst =
    if cls = Class_table.boolean_index then
      [Feature_table.implication_index]
    else
      Class_table.base_features cls ct
  in
  let fname i = Feature_table.feature_name i ft in
  let eq_index = Feature_table.variant Feature_table.eq_index cls ft in
  if Feature_table.is_deferred eq_index ft then
    ()
  else begin
    (*printf "check base features of class %d %s\n"
      cls (Class_table.class_name cls ct);
    List.iter (fun i -> printf "   %s\n" (fname i)) lst;*)
    ()
  end
