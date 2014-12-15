open Support
open Term
open Container
open Printf

module FT = Feature_table


let class_table (ft:FT.t):Class_table.t =
  Feature_table.class_table ft



let inherit_deferred (i:int) (cls:int) (info:info) (ft:FT.t): unit =
  (* Inherit the deferred feature [i] in the class [cls] *)
  if 1 < Feature_table.verbosity ft then begin
    let ct   = class_table ft in
    let icls = Feature_table.get_class i ft in
    printf "   inherit deferred \"%s %s\" in %s\n"
      (Class_table.class_name icls ct)
      (Feature_table.string_of_signature i ft)
      (Class_table.class_name cls ct) end;
  assert (cls <> Feature_table.get_class i ft);
  let idx =
    try Feature_table.find_variant i cls ft
    with Not_found ->
      let ct   = class_table ft  in
      let str =
        "The class " ^ (Class_table.class_name cls ct) ^
        " does not have a feature unifyable with \"" ^
        (Feature_table.string_of_signature i ft) ^
        "\" with proper substitutions of the type variables" in
      error_info info str
  in
  Feature_table.inherit_feature i idx cls false ft







let inherit_effective (i:int) (cls:int) (info:info) (ft:FT.t): unit =
  if 1 < Feature_table.verbosity ft then begin
    let ct = class_table ft in
    let icls = Feature_table.get_class i ft in
    printf "   inherit \"%s %s\" in %s\n"
      (Class_table.class_name icls ct)
      (Feature_table.string_of_signature i ft)
      (Class_table.class_name cls ct) end;
  if not (Feature_table.has_anchor i ft) then
    ()
  else if not (Feature_table.has_variant i cls ft) then
    Feature_table.inherit_effective i cls ft
  else
    let ct   = class_table ft  in
    let str =
      "The class " ^ (Class_table.class_name cls ct) ^
      " has already a feature unifyable with \"" ^
      (Feature_table.string_of_signature i ft) ^
      "\"" in
    error_info info str


let export_inherited_variant (i:int) (cls:int) (ft:FT.t): unit =
  (* Export the inherited variant of the feature [i] in the class [cls] *)
  assert (Feature_table.is_interface_check ft);
  if Feature_table.has_anchor i ft then
    try
      let idx = Feature_table.private_variant i cls ft in
      Feature_table.export_feature idx ft;
      Feature_table.inherit_feature i idx cls true ft
    with Not_found ->
      assert (not (Feature_table.is_deferred i ft));
      assert (not (Feature_table.has_variant i cls ft));
      inherit_effective i cls UNKNOWN ft



let export_inherited
    (cls:int)
    (anc_lst: (int * type_term array) list)
    (ft:FT.t)
    : unit =
  (* Export all inherited features from all classes in the ancestor list [anc_lst]
     in the class [cls] *)
  let ct = class_table ft in
  List.iter
    (fun (par,par_args) ->
      let flst = Class_table.deferred_features par ct in
      List.iter (fun i -> export_inherited_variant i cls ft) flst;
      let flst = Class_table.effective_features par ct in
      List.iter (fun i -> export_inherited_variant i cls ft) flst)
    anc_lst



let inherit_to_descendants (i:int) (info:info) (ft:FT.t): unit =
  if not (Feature_table.is_deferred i ft) && Feature_table.has_anchor i ft then
    let ct = class_table ft in
    let cls = Feature_table.get_class i ft in
    let descendants = Class_table.descendants cls ct in
    IntSet.iter
      (fun cls -> inherit_effective i cls info ft)
      descendants

let do_inherit
    (cls:int)
    (anc_lst: (int * type_term array) list)
    (info:info)
    (ft:FT.t)
    : unit =
  (* For all ancestors in the list [anc_lst]:

     Go through all deferred features of the parent class [par_idx] and verify
     that the class [cls] has all these deferred features.

     Then inherit all effective features of the class [par_idx] into the class
     [cls_idx]
   *)
  let ct = class_table ft in
  List.iter
    (fun (par,par_args) ->
      let flst = Class_table.deferred_features par ct in
      List.iter (fun i -> inherit_deferred i cls info ft) flst;
      let flst = Class_table.effective_features par ct in
      List.iter (fun i -> inherit_effective i cls info ft) flst
    )
    anc_lst




let export_inherited_variant (i:int) (cls:int) (ft:FT.t): unit =
  (* Export the inherited variant of the feature [i] in the class [cls] *)
  assert (Feature_table.is_interface_check ft);
  if Feature_table.has_anchor i ft then
    try
      let idx = Feature_table.private_variant i cls ft in
      Feature_table.export_feature idx ft;
      Feature_table.inherit_feature i idx cls true ft
    with Not_found ->
      assert (not (Feature_table.is_deferred i ft));
      assert (not (Feature_table.has_variant i cls ft));
      inherit_effective i cls UNKNOWN ft



let export_inherited
    (cls:int)
    (anc_lst: (int * type_term array) list)
    (ft:FT.t)
    : unit =
  (* Export all inherited features from all classes in the ancestor list [anc_lst]
     in the class [cls] *)
  let ct = class_table ft in
  List.iter
    (fun (par,par_args) ->
      let flst = Class_table.deferred_features par ct in
      List.iter (fun i -> export_inherited_variant i cls ft) flst;
      let flst = Class_table.effective_features par ct in
      List.iter (fun i -> export_inherited_variant i cls ft) flst)
    anc_lst


let inherit_to_descendants (i:int) (info:info) (ft:FT.t): unit =
  if not (Feature_table.is_deferred i ft) &&  Feature_table.has_anchor i ft then
    let ct  = class_table ft in
    let cls = Feature_table.get_class i ft in
    let descendants = Class_table.descendants cls ct in
    IntSet.iter
      (fun cls -> inherit_effective i cls info ft)
      descendants
