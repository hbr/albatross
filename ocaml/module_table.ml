open Container
open Support

module Modmap = Map.Make(struct
  let compare = Pervasives.compare
  type t = int * int list
end)


type content = {mutable used: IntSet.t;
                mutable clss: IntSet.t}

type desc = { name: int;
              lib:  int list;
              priv: content;
              pub:  content;
              mutable on_stack: bool
            }

type t = {mutable map:    int Modmap.t;
          seq:            desc Seq.t;
          mutable stack:  int list;
          mutable is_pub: bool}

let count (mt:t): int =
  Seq.count mt.seq

let find (name:int) (lib:int list) (mt:t): int =
  Modmap.find (name,lib) mt.map

let has (name:int) (lib: int list) (mt:t): bool =
  (* Is the module [lib.name] in the table?  *)
  try let _ = find name lib mt in true
  with Not_found ->               false

let has_current (mt:t): bool =
  mt.stack <> []

let is_toplevel (mt:t): bool =
  match mt.stack with
    [_] -> true
  | _   -> false

let current (mt:t): int =
  assert (has_current mt);
  List.hd mt.stack

let is_public  (mt:t): bool =
  match mt.stack with
    []   -> false
  | [_]  -> mt.is_pub
  | _    -> true

let is_private (mt:t): bool = not (is_public mt)

let set_public (mt:t): unit =
  assert (is_toplevel mt);
  assert (is_private  mt);
  mt.is_pub <- true

let used (mdl:int) (mt:t): IntSet.t =
  (* The publicly used modules of the module [mdl]. *)
  assert (mdl < count mt);
  (Seq.elem mdl mt.seq).pub.used

let used_priv (mdl:int) (mt:t): IntSet.t =
  (* The privately used modules of the module [mdl]. *)
  assert (mdl < count mt);
  (Seq.elem mdl mt.seq).priv.used


let make (): t =
  {map=Modmap.empty; seq=Seq.empty (); stack=[]; is_pub=false}

let push (name:int) (lib: int list) (mt:t): unit =
  assert (not (has name lib mt));
  let n = count mt
  and cont = {used=IntSet.empty; clss=IntSet.empty} in
  Seq.push {name=name; lib=lib; priv=cont; pub=cont; on_stack=true} mt.seq;
  mt.stack <- n :: mt.stack;
  mt.map   <- Modmap.add (name,lib) n mt.map


let add_used_1 (used_mdl: int) (mt:t): unit =
  (* Add the module [used_mdl] and all its used modules to the
     current module of the table [mt] *)
  assert (has_current mt);
  assert (used_mdl < count mt);
  let usd = used used_mdl mt in
  let usd = IntSet.add used_mdl usd in
  let mdl = current mt in
  let desc = Seq.elem mdl mt.seq in
  let cont =
    if is_toplevel mt && not mt.is_pub then desc.priv
    else desc.pub
  in
  let usd = IntSet.union usd cont.used in
  cont.used <- usd


let pop (mt:t): unit =
  (* Pop the current module off the stack and add it all its used modules to
     the remaining current module if there is one.  *)
  assert (has_current mt);
  let used_mdl = current mt in
  mt.stack <- List.tl mt.stack;
  (Seq.elem used_mdl mt.seq).on_stack <- false;
  if has_current mt then begin
    add_used_1 used_mdl mt
  end else
    mt.is_pub <- false


let stack_to (mdl:int) (mt:t): int list =
  let rec stckto (stack: int list) (lst:int list): int list =
    match stack with
      [] -> assert false
    | i::tl ->
        if i=mdl then i::lst
        else stckto tl (i::lst)
  in
  stckto mt.stack [mdl]

let name (mdl:int) (mt:t): string =
  assert (mdl < count mt);
  let desc = Seq.elem mdl mt.seq in
  let libstr = String.concat "." (List.map ST.string desc.lib)
  and nmestr = ST.string desc.name
  in
  let libstr = if libstr = "" then "" else libstr ^ "."
  in
  libstr ^ nmestr


let add_used (mdl:int) (inf:info) (mt:t): unit =
  assert (mdl < count mt);
  if (Seq.elem mdl mt.seq).on_stack then begin
    let lst = stack_to mdl mt in
    let str = String.concat "," (List.map (fun i -> name i mt) lst) in
    let str = "Circular module usage [" ^ str ^ "]" in
    error_info inf str
  end else
    add_used_1 mdl mt
