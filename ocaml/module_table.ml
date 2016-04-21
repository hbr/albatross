(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Support
open Term
open Signature
open Printf


type formal = int * type_term


type desc = { name: int; (* module name *)
              lib:  int; (* library name of the module *)
              mutable priv: IntSet.t;
              mutable pub:  IntSet.t (* Privately and publicly used modules are
                                        identical for all used modules. For the
                                        current module the publicly used modules
                                        are a subset of the privately used modules *)
   (* The used modules of each module contain the directly and indirectly used
      modules. Usage is reflexive, i.e. each module uses itself.

      The modules are added in topologically sorted i.e. a module is entered into
      the table only if all its used modules are already in the table. *)
   }



type t = {mutable map:    int Module_map.t;
          mutable libmap: int Library_map.t;
          seq:            desc Seq.t;
          libseq:         library_name Seq.t;
          base:           IntSet.t;
          mutable base_added:     IntSet.t; (* Set of all base modules which are
                                               already in the module table *)
          mutable mode:   int;
          mutable fgens: type_term IntMap.t}



let count (mt:t): int =
  Seq.count mt.seq

let count_libraries (mt:t): int =
  Seq.count mt.libseq

let find ((name,lib):int * int list) (mt:t): int =
  Module_map.find (name,lib) mt.map

let find_library (lib:int list) (mt:t): int =
  Library_map.find lib mt.libmap

let has (nme:int*int list) (mt:t): bool =
  (* Is the module [lib.name] in the table?  *)
  try let _ = find nme mt in true
  with Not_found ->          false

let has_library (lib:int list) (mt:t): bool =
  try let _ = find_library lib mt in true
  with Not_found ->                 false


let has_base (nme:int) (mt:t): bool =
  IntSet.mem nme mt.base_added

let has_current (mt:t): bool =
  0 < count mt


let current (mt:t): int =
  assert (has_current mt);
  count mt - 1


let is_public  (mt:t): bool =
  has_current mt && mt.mode > 0

let is_private (mt:t): bool = not (is_public mt)

let is_interface_check (mt:t): bool =
  has_current mt && mt.mode = 1

let is_interface_use (mt:t): bool =
  has_current mt && mt.mode = 2

let used (mdl:int) (mt:t): IntSet.t =
  (* The publicly used modules of the module [mdl]. *)
  assert (mdl < count mt);
  (Seq.elem mdl mt.seq).pub

let used_priv (mdl:int) (mt:t): IntSet.t =
  (* The privately used modules of the module [mdl]. *)
  assert (mdl < count mt);
  (Seq.elem mdl mt.seq).priv


let current_used (mt:t): IntSet.t =
  assert (has_current mt);
  used (current mt) mt

let current_used_priv (mt:t): IntSet.t =
  assert (has_current mt);
  used_priv (current mt) mt

let descriptor (i:int) (mt:t): desc =
  assert (i < count mt);
  Seq.elem i mt.seq


let interface_used (used_blk: use_block) (mt:t): IntSet.t =
  (* The set of all directly and indirectly used modules of the use block [used_blk]
     occuring in the interface file of the current module *)
  assert (has_current mt);
  List.fold_left
    (fun set mdl ->
      try
        let i = find mdl.v mt in
        let desc = descriptor i mt in
        IntSet.union set desc.priv
      with Not_found ->
        error_info mdl.i ("module `" ^ (string_of_module mdl.v) ^
                          "' not used in implementation file"))
    (IntSet.singleton (current mt))
    used_blk


let library (lib_id:int) (mt:t): int list =
  assert (lib_id < count_libraries mt);
  Seq.elem lib_id mt.libseq


let library_name (lib_id:int) (mt:t): string =
  assert (lib_id < count_libraries mt);
  let lib = library lib_id mt in
  String.concat "." (List.rev_map ST.string lib)


let library_of_module (mdl:int) (mt:t): int list =
  assert (mdl < count mt);
  library (descriptor mdl mt).lib mt


let current_library (mt:t): int list =
  assert (has_current mt);
  let mdl = current mt in
  library_of_module mdl mt


let name_symbol (mdl:int) (mt:t): int =
  assert (mdl < count mt);
  (descriptor mdl mt).name

let simple_name (mdl:int) (mt:t): string =
  assert (mdl < count mt);
  ST.string (name_symbol mdl mt)


let name (mdl:int) (mt:t): string =
  assert (mdl < count mt);
  let desc = Seq.elem mdl mt.seq in
  let libstr = library_name desc.lib mt
  and nmestr = ST.string desc.name
  in
  let libstr = if libstr = "" then "" else libstr ^ "."
  in
  libstr ^ nmestr



let add_used ((nme,lib):int*int list) (used:IntSet.t) (mt:t): unit =
  (* Add the used module (nme,lib) of the current module with all its implicitely
     used modules. Note: The current module has not yet been inserted!
   *)
  assert (not (has (nme,lib) mt));
  assert (not (has_base nme mt));
  let n = count mt in
  let lib_id =
    try find_library lib mt
    with Not_found ->
      let id = count_libraries mt in
      Seq.push lib mt.libseq; id
  in
  let used = IntSet.add n used in
  Seq.push {name=nme; lib=lib_id; priv=used; pub=used} mt.seq;
  if IntSet.mem nme mt.base then
    mt.base_added <- IntSet.add nme mt.base_added;
  mt.map   <- Module_map.add (nme,lib) n mt.map;
  mt.mode  <- 2;
  mt.fgens <- IntMap.empty(*;
  printf "add_used of module %s\n" (name (current mt) mt);
  IntSet.iter
    (fun mdl ->
      printf "  %s\n" (name mdl mt))
    used*)



let add_current (name:int) (used:IntSet.t) (mt:t): unit =
  assert (not (has (name,[]) mt));
  assert (not (has_base name mt));
  let n = count mt in
  let used = IntSet.add n used in
  Seq.push {name=name; lib=0; priv=used; pub=IntSet.empty} mt.seq;
  if IntSet.mem name mt.base then
    mt.base_added <- IntSet.add name mt.base_added;
  mt.map   <- Module_map.add (name,[]) n mt.map;
  mt.mode  <- 0;
  mt.fgens <- IntMap.empty



let is_visible (mdl:int) (mt:t): bool =
  (* Is the module [mdl] visible i.e. exported? *)
  assert (0 <= mdl);
  assert (mdl < count mt);
  assert (has_current mt);
  assert (mdl <> current mt);
  let desc = descriptor (current mt) mt in
  IntSet.mem mdl desc.pub



let set_interface_check (pub_used:IntSet.t) (mt:t): unit =
  assert (has_current mt);
  assert (is_private mt);
  assert (IntSet.subset pub_used (used_priv (current mt) mt));
  let desc = Seq.elem (current mt) mt.seq in
  desc.pub  <- pub_used;
  mt.mode   <- 1;
  mt.fgens  <- IntMap.empty



let base_set: IntSet.t =
  (* The set of all basic modules. *)
  IntSet.of_list
    (List.rev_map ST.symbol ["boolean";"any";"predicate";"tuple";"function"])



let make (): t =
  let libseq = Seq.empty() in
  Seq.push [] libseq;
  {map     = Module_map.empty;
   libmap  = Library_map.singleton [] 0;
   seq     = Seq.empty ();
   libseq  = libseq;
   base    = base_set;
   base_added = IntSet.empty;
   mode    = 0;
   fgens   = IntMap.empty}



let find_formal (name: int) (mt:t): type_term =
  IntMap.find name mt.fgens



let put_formal (name: int withinfo) (concept: type_term) (mt:t): unit =
  (** Add the formal generic with [name] and [concept] to the formal generics
      of the class table [ct] *)
  if IntMap.mem name.v mt.fgens then
    error_info
      name.i
      ("formal generic " ^ (ST.string name.v) ^ " already defined")
  else
    mt.fgens <- IntMap.add name.v concept mt.fgens



let add_fg
    (name:int)
    (path: int list)
    (fgs: formal list)
    (tvs:TVars_sub.t)
    (mt:t)
    : formal list =
  (* Check if [name] is a new formal generic. If yes prepend it to [fgs].

     Note: [fgs] is reversed *)
  if path = [] &&
    not (List.exists (fun (nme,_)-> nme=name) fgs) &&
    not (TVars_sub.has_fg name tvs)
  then
    try
      let cpt = IntMap.find name mt.fgens in
      (name,cpt) :: fgs
    with Not_found ->
      fgs
  else
    fgs


let collect_fgs
    (tp:type_t)
    (fgs:formal list)
    (tvs:TVars_sub.t)
    (mt:t)
    : formal list =
  (* Collect the formal generics of the type [tp] and prepend them to [fgs] if
     they are new.

     Note: [fgs] is reversed *)
  let rec collect (tp:type_t) (fgs:formal list): formal list =
    match tp with
      Normal_type (path,name,args) ->
        let fgs = List.fold_left
            (fun lst tp -> collect tp lst)
            fgs
            args
        in
        add_fg name path fgs tvs mt
    | Arrow_type (tpa,tpb) ->
        collect tpb (collect tpa fgs)
    | QMark_type tp | Star_type tp | Paren_type tp | List_type tp ->
        collect tp fgs
    | Tuple_type lst ->
        List.fold_left (fun fgs tp -> collect tp fgs) fgs lst
  in
  collect tp fgs



let formal_generics
    (entlst:   entities list withinfo)
    (rt:       return_type)
    (is_func:  bool)
    (ntvs_gap: int)
    (tvs:      TVars_sub.t)
    (mt:       t)
    : TVars_sub.t =
  let ntvs_new,fgs_new =
    List.fold_left
      (fun (ntvs,fgs) ent ->
        match ent with
          Untyped_entities vars ->
            ntvs + List.length vars, fgs
        | Typed_entities (_,tp) ->
            ntvs, collect_fgs tp fgs tvs mt)
      (0,[])
      entlst.v
  in
  let ntvs_new, fgs_new =
    match rt with
      None when is_func -> ntvs_new + 1, fgs_new
    | None -> ntvs_new, fgs_new
    | Some tp ->
        let t,_,_ = tp.v in
        ntvs_new, collect_fgs t fgs_new tvs mt
  in
  let fgs_new = Array.of_list (List.rev fgs_new) in
  let fgnames,fgconcepts = Myarray.split fgs_new in
  let nfgs_new = Array.length fgconcepts in
  let fgconcepts = Array.map (fun tp -> Term.up nfgs_new tp) fgconcepts in
  TVars_sub.augment (ntvs_new+ntvs_gap) fgnames fgconcepts tvs




let class_formal_generics (fgens: formal_generics) (mt:t): formal array =
  Array.of_list
    (List.map
       (fun nme ->
         try
           nme, IntMap.find nme mt.fgens
         with Not_found ->
           let str = "Unknown formal generic " ^ (ST.string nme) in
           error_info fgens.i str)
       fgens.v)


let class_tvs (fgens:formal_generics) (mt:t): Tvars.t =
  let fgs = class_formal_generics fgens mt in
  let fgnms, fgcon = Myarray.split fgs in
  let nfgs = Array.length fgcon in
  let fgcon = Array.map (fun tp -> Term.up nfgs tp) fgcon in
  Tvars.make_fgs fgnms fgcon
