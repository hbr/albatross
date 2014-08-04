open Container
open Support
open Printf

module Modmap = Map.Make(struct
  let compare = Pervasives.compare
  type t = int * int list
end)


type content = {mutable used: IntSet.t;
                mutable clss: IntSet.t}

type desc = { name: int;
              lib:  int list;
              priv: content;
              pub:  content
            }


type t = {mutable map:    int Modmap.t;
          seq:            desc Seq.t;
          mutable mode:   int}



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
  mt.mode  <- mode


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
  {map=Modmap.empty; seq=Seq.empty (); mode=0}



let name (mdl:int) (mt:t): string =
  assert (mdl < count mt);
  let desc = Seq.elem mdl mt.seq in
  let libstr = String.concat "." (List.map ST.string desc.lib)
  and nmestr = ST.string desc.name
  in
  let libstr = if libstr = "" then "" else libstr ^ "."
  in
  libstr ^ nmestr
