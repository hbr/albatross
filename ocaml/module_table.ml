open Container
open Support
open Term
open Signature
open Printf

module Modmap = Map.Make(struct
  let compare = Pervasives.compare
  type t = int * int list
end)


type formal = int * type_term

type content = {mutable used: IntSet.t;
                mutable clss: IntSet.t}

type desc = { name: int;
              lib:  int list;
              priv: content;
              pub:  content
            }


type t = {mutable map:    int Modmap.t;
          seq:            desc Seq.t;
          mutable mode:   int;
          mutable fgens: type_term IntMap.t}



let count (mt:t): int =
  Seq.count mt.seq


let find (name:int) (lib:int list) (mt:t): int =
  Modmap.find (name,lib) mt.map


let has (name:int) (lib: int list) (mt:t): bool =
  (* Is the module [lib.name] in the table?  *)
  try let _ = find name lib mt in true
  with Not_found ->               false


let has_current (mt:t): bool =
  0 < count mt


let current (mt:t): int =
  assert (has_current mt);
  count mt - 1


let is_public  (mt:t): bool =
  has_current mt && mt.mode > 0

let is_private (mt:t): bool = not (is_public mt)

let is_interface_use (mt:t): bool =
  has_current mt && mt.mode = 2

let used (mdl:int) (mt:t): IntSet.t =
  (* The publicly used modules of the module [mdl]. *)
  assert (mdl < count mt);
  (Seq.elem mdl mt.seq).pub.used

let used_priv (mdl:int) (mt:t): IntSet.t =
  (* The privately used modules of the module [mdl]. *)
  assert (mdl < count mt);
  (Seq.elem mdl mt.seq).priv.used



let add (name:int) (lib:int list) (mode:int) (mt:t): unit =
  assert (0 <= mode);
  assert (mode <= 2);
  printf "add module %s\n" (ST.string name);
  assert (not (has name lib mt));
  let n = count mt
  and cont = {used=IntSet.empty; clss=IntSet.empty} in
  Seq.push {name=name; lib=lib; priv=cont; pub=cont} mt.seq;
  mt.map   <- Modmap.add (name,lib) n mt.map;
  mt.mode  <- mode;
  mt.fgens <- IntMap.empty


let set_used (set:IntSet.t) (mt:t): unit =
  assert (has_current mt);
  let mdl = current mt           in
  let desc = Seq.elem mdl mt.seq
  and set  = IntSet.add mdl set  in
  if is_public mt then
    desc.pub.used <- set
  else
    desc.priv.used <- set





let make (): t =
  {map=Modmap.empty; seq=Seq.empty (); mode=0; fgens = IntMap.empty}



let name (mdl:int) (mt:t): string =
  assert (mdl < count mt);
  let desc = Seq.elem mdl mt.seq in
  let libstr = String.concat "." (List.map ST.string desc.lib)
  and nmestr = ST.string desc.name
  in
  let libstr = if libstr = "" then "" else libstr ^ "."
  in
  libstr ^ nmestr


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
    | Current_type lst ->
        assert false (* nyi: but might be eliminated from the language *)
    | Arrow_type (tpa,tpb) ->
        collect tpb (collect tpa fgs)
    | Ghost_type tp | QMark_type tp | Paren_type tp ->
        collect tp fgs
    | Tuple_type lst ->
        List.fold_left (fun fgs tp -> collect tp fgs) fgs lst
  in
  collect tp fgs



let formal_generics
    (entlst:   entities list withinfo)
    (rt:       return_type)
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
  let fgs_new =
    match rt with
      None -> fgs_new
    | Some tp ->
        let t,_,_ = tp.v in
        collect_fgs t fgs_new tvs mt
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
