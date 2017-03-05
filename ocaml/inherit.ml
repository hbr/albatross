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




let check_transform_valid
    (i:int) (ivar:int) (ags:agens) (info:info) (pc:PC.t)
    : unit =
  (* Check the validity of the specification of the feature [i] transformed
     into the environment of the feature [ivar] by using the actual generics
     [ags] to substitute the formal generics of [i]. *)
  let ft = PC.feature_table pc in
  if 3 <= PC.verbosity pc then begin
    printf "\n\n   Check the validity of the feature\n";
    printf "         %d %s\n" i (Feature_table.string_of_signature i ft);
    printf "      in %d %s\n" ivar (Feature_table.string_of_signature ivar ft);
  end;
  let specs = Feature_table.transformed_specifications i ivar ags ft in
  if 3 <= PC.verbosity pc then begin
    printf "\n\n   Check the validity of the feature\n";
    printf "         %d %s\n" i (Feature_table.string_of_signature i ft);
    printf "      in %d %s\n" ivar (Feature_table.string_of_signature ivar ft);
    List.iter (fun t -> printf "      %s\n" (PC.string_long_of_term t pc)) specs;
    printf "\n";
  end;
  List.iter
    (fun t ->
      try
        prove t pc
      with Proof.Proof_failed msg ->
        let sig1 = Feature_table.string_of_signature i ft
        and sig2 = Feature_table.string_of_signature ivar ft
        and tstr = PC.string_of_term t pc in
        let str =
          "The feature\n\t\"" ^ sig2 ^
          "\"\ncannot be a variant of the feature \n\t\"" ^ sig1 ^
          "\"\nbecause\n\t\"" ^ tstr ^
          "\"\ncannot be verified"
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
    (ghost:bool)
    (info:info)
    (pc:PC.t)
    : (int*bool*int*agens) list =
  (* Inherit the feature [idx] in the class [cls].

     - Find all new variants of the feature. Variants are either new variants
       which can be found in the search tables or already existing variants of
       the seed of [idx].

     - If [idx] is a deferred feature, then there must be a variant. Otherwise
       report an error.

     - If [idx] is an effective feature, then its specification has to be valid in
       all minimal variants of the feature.

     - Insert all new variants into the variant map of the seed of [idx].

     - Return a list of triples with
            sd:   Seed of the variant
            ivar: New variant
            ags:  Actual generics to substituted the formal generics of the seed.
   *)
  let ft = PC.feature_table pc in
  let defer = Feature_table.is_deferred idx ft in
  let fold_fun
      (is_new:bool)
      (lst:(int*bool*int*agens) list)
      ((ivar,ags):(int*agens))
      : (int*bool*int*agens) list =
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
    if is_new then
      Feature_table.add_variant info sd ivar sdags ft;
    check_ghost_variant idx ivar ghost info ft;
    if PC.is_private pc && not defer then
      check_transform_valid idx ivar ags info pc;
    (sd,is_new,ivar,sdags)::lst
  in
  let lst =
    List.fold_left
      (fold_fun false)
      []
      (Feature_table.find_minimal_variants idx cls ft)
  in
  let lst =
    List.fold_left
      (fold_fun true)
      lst
      (Feature_table.find_new_variants idx ft)
  in
  if not defer || PC.is_interface_use pc then
    lst
  else
    let error_deferred () =
      let ct = class_table pc  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " does not have a variant of the deferred feature \n\t\"" ^
        (Feature_table.string_of_signature idx ft) ^
        "\"" in
      error_info info str
    in
    match lst with
      [sd,is_new,ivar,ags] ->
        assert (Array.length ags = 1); (* nyi: deferred features with more than
                                          one formal generic *)
        let tvs = Feature_table.tvars ivar ft in
        if Tvars.principal_class ags.(0) tvs <> cls then begin
          error_deferred ()
        end;
        lst
    | _ ->
        error_deferred ()




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
          let lst1 = inherit_feature idx cls ghost info pc in
          List.rev_append lst1 lst
      )
      []
      (Class_table.generics par (class_table pc))
  in
  let ass_set =
    List.fold_left
      (fun set (sd,is_new,ivar,ags) ->
        if is_new then begin
          Feature_table.set_seed sd ivar ags ft;
          IntSet.union set (Feature_table.involved_assertions ivar ft)
        end else
          set
      )
      IntSet.empty
      sd_var_lst
  in
  PC.remove_or_remap ass_set pc




let add_new_feature (info:info) (idx:int) (pc:PC.t): unit =
  (* Do all inheritance related stuff for the new feature [idx].

     See if there is already a seed feature. If yes make the new feature
     a variant of the seed feature and verify the validity of the specification
     of the seed in the environment of the new feature.

     See if there are variants of the new feature in the search tables (this
     is possible only if the new feature does not have a proper seed). If yes,
     make the variant a variant of the new feature and check the validity of
     the specification of the new feature in the environment of the variant
     feature.

     Finally put the seeds to all newly created variants and remap all assertions
     which involve newly created variants.
*)
  let ft = PC.feature_table pc in
  let trace (sd:int) (ivar:int): unit =
    if 1 < PC.verbosity pc then begin
      printf "    generic feature %2d \"%s\"\n"
        sd (Feature_table.string_of_signature sd ft);
      printf "      variant       %2d \"%s\"\n"
        ivar (Feature_table.string_of_signature ivar ft);
    end
  in
  try
    let sd,ags = Feature_table.find_proper_seed info idx ft in
    trace sd idx;
    Feature_table.add_variant info sd idx ags ft;
    if PC.is_private pc then
      check_transform_valid sd idx ags info pc;
    Feature_table.set_seed sd idx ags ft
  with Not_found -> (* no proper seed *)
    let var_lst = Feature_table.find_new_variants idx ft
    in
    let ass_set =
      List.fold_left
        (fun set (ivar,ags) ->
          trace idx ivar;
          Feature_table.add_variant info idx ivar ags ft;
          if PC.is_private pc then
            check_transform_valid idx ivar ags info pc;
          IntSet.union set (Feature_table.involved_assertions ivar ft)
        )
        IntSet.empty
        var_lst
    in
    List.iter
      (fun (ivar,ags) -> Feature_table.set_seed idx ivar ags ft)
      var_lst;
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
        if par <> Constants.any_class &&
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
