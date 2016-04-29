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




let prove (t:term) (pc:PC.t): unit =
  assert (PC.is_private pc);
  ignore(Prover.proof_term t pc)





let inherit_parent (cls:int) (parent:parent) (pc:PC.t): unit =
  let ct = PC.class_table pc in
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



let check_transform_valid
    (i:int) (ivar:int) (ags:agens) (info:info) (pc:PC.t)
    : unit =
  (* Check the validity of the specification of the feature [i] transformed
     into the environment of the feature [ivar] by using the actual generics
     [ags] to substitute the formal generics of [i]. *)
  let ft = PC.feature_table pc in
  let specs = Feature_table.transformed_specifications i ivar ags ft in
  List.iter
    (fun t ->
      try
        prove t pc
      with Proof.Proof_failed msg ->
        let sig1 = Feature_table.string_of_signature i ft
        and sig2 = Feature_table.string_of_signature ivar ft
        and tstr = PC.string_of_term t pc in
        let str =
          "The feature \"" ^ sig2 ^
          "\"\ncannot be a variant of the feature \"" ^ sig1 ^
          "\"\nbecause \"" ^ tstr ^
          "\" cannot be verified"
        in
        error_info info str
    )
    specs




let check_ghost_variant
    (i:int) (ivar:int) (is_ghost:bool) (info:info) (ft:Feature_table.t)
    : unit =
  (* Check if the variant is a ghost function then the basic function must be a
     ghost function as well or the inheritance relation is a ghost relation.
   *)
  let is_i_ghost    = Feature_table.is_ghost_function i ft
  and is_ivar_ghost = Feature_table.is_ghost_function ivar ft in
  if is_ivar_ghost && not is_i_ghost && not is_ghost then
    error_info info "Must be ghost inheritance"



let inherit_feature
    (idx:int)
    (cls:int)
    (lst:(int*int*agens) list)
    (ghost:bool)
    (info:info)
    (pc:PC.t)
    : (int*int*agens) list =
  (* Inherit the feature [idx] in the class [cls] and in case that there is a
     variant add the new seed/variant pair to the list of pairs. *)
  let ft = PC.feature_table pc in
  let defer = Feature_table.is_deferred idx ft in
  try
    let ivar,ags = Feature_table.find_variant_candidate idx ft in
    let sd,sdags = Feature_table.get_variant_seed idx ivar ags ft in
    if 1 < PC.verbosity pc then begin
      printf "    generic feature %2d \"%s\"\n"
        idx (Feature_table.string_of_signature idx ft);
      printf "      variant       %2d \"%s\"\n"
        ivar (Feature_table.string_of_signature ivar ft);
      if idx <> sd then
        printf "      seed          %2d \"%s\"\n"
          sd (Feature_table.string_of_signature sd ft)
    end;
    Feature_table.add_variant sd ivar sdags ft;
    check_ghost_variant idx ivar ghost info ft;
    if PC.is_private pc && not defer then
      check_transform_valid idx ivar ags info pc;
    (sd,ivar,sdags)::lst
  with Not_found ->
    if not defer then
      lst
    else
      let ct = class_table pc  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " does not have a feature unifiable with \"" ^
        (Feature_table.string_of_signature idx ft) ^
        "\" with proper substitutions of the type variables" in
      error_info info str



let inherit_assertion (i:int) (cls:int) (info:info) (pc:PC.t): unit =
  (* Inherit the deferred assertion [i] in the class [cls].

     Find the proper variant of the assertion. If not found, flag an error.
   *)
  assert (PC.is_global pc);
  let t = PC.term i pc in
  match t with
    QExp(n,(nms,tps),(fgnms,fgcon),t0,true) ->
      let nfgs = Array.length fgnms in
      assert (nfgs = 1); (* Deferred assertion must have one formal generic. *)
      let ft = PC.feature_table pc in
      let ct = Feature_table.class_table ft in
      let ctp,tvs = Class_table.class_type cls ct in
      let t1 =
        Feature_table.substituted t0 n 0 0
          (standard_substitution n)
          n [|ctp|] tvs ft in
      begin try
        let goal = QExp(n,empty_formals,empty_formals,t1,true) in
        let ivar = PC.find goal pc in
        if 1 < PC.verbosity pc then begin
          printf "    deferred assertion %2d \"%s\"\n"
            i (PC.string_of_term t pc);
          printf "      variant          %2d \"%s\"\n"
            ivar (PC.string_of_term_i ivar pc)
        end
      with Not_found ->
        let str =
          "The class " ^ (Class_table.class_name cls ct) ^
          " does not have a variant of the deferred assertion\n    " ^
          (PC.string_of_term t pc)
        in
        error_info info str
      end
  | _ ->
      assert false (* Cannot happen. Assertion is deferred and therefore must
                      have one formal generic and arguments. *)



let inherit_generics
    (par:int) (cls:int) (ghost:bool) (info:info) (pc:PC.t)
    : unit =
  (* Inherit in the generic features/assertions of the parent class [par] in
     the class [cls]. *)
  let ft = PC.feature_table pc in
  let sd_var_lst =
    List.fold_left
      (fun lst (is_ass,idx) ->
        if is_ass then begin
          inherit_assertion idx cls info pc;
          lst
        end else
          inherit_feature idx cls lst ghost info pc
      )
      []
      (Class_table.generics par (class_table pc))
  in
  let ass_set =
    List.fold_left
      (fun set (sd,ivar,ags) ->
        Feature_table.set_seed sd ivar ags ft;
        IntSet.union set (Feature_table.involved_assertions ivar ft)
      )
      IntSet.empty
      sd_var_lst
  in
  PC.remove_or_remap ass_set pc


let inherit_parents (cls:int) (clause:inherit_clause) (pc:PC.t): unit =
  let ct = PC.class_table pc
  and ft = PC.feature_table pc in
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
          printf "  inherit %s in %s\n"
            (Class_table.class_name par ct) (Class_table.class_name cls ct);
        if not (Class_table.is_interface_check ct) then begin
          Class_table.inherit_parent cls par par_args ghost tp.i ct;
          inherit_generics par cls ghost tp.i pc
        end
      end)
    clause
