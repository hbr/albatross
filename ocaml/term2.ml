open Alba2_common

module Sort =
  struct
    type t =
      | Var of int
      | Level of int
    type constraint_ =
      | Eq of int * int
      | LE of int * int
      | LT of int * int
  end

type fix_index = int
type decr_index = int
type oo_application = bool

type t =
  {term: t0; info: Info.t}
and t0 =
  | Sort of Sort.t
  | Variable of int
  | Application of t * t * oo_application
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * inspect_map * t array
  | Fix of fix_index * fixpoint
and typ = t
and abstraction =  string option * typ * t
and inspect_map = t
and fixpoint = (Feature_name.t option * typ * decr_index * t) array


let fold_free_from (start:int) (f:'a->int->'a) (a:'a) (t:t): 'a =
  let rec fold s a t =
    match t.term with
    | Sort s -> t
    | Variable i when i < start ->
       a
    | Variable i ->
       assert (s <= i);
       f a (i-s)
    | Application (g,x,_) ->
       fold s (fold s a g) x
    | Lambda (_,tp,t) ->
       fold (s+1) (fold s a tp) t
    | All (_,tp,t) ->
       fold (s+1) (fold s a tp) t
    | Inspect (t,mp,arr) ->
       let fld = fold s in
       Array.fold_left
         fld
         (fld (fld a t) mp)
         arr
    | Fix (idx,arr) ->
       let fld = fold (s + Array.length arr) in
       Array.fold_left
         (fun a (_,tp,_,t) ->
           fld (fld a tp) t)
         a
         arr
  in
  fold start a t


let fold_free (f:'a->int->'a) (a:'a) (t:t): 'a =
  fold_free_from 0 f a t


let map_free_from (start:int) (f:int->int) (t:t): t =
  let info = t.info in
  let rec map s t =
    match t.term with
    | Sort s -> t
    | Variable i when i < start ->
       t
    | Variable i ->
       assert (s <= i);
       {term = Variable (f (i-s) + s); info}
    | Application (a,b,oo) ->
       {term = Application (map s a, map s b, oo); info}
    | Lambda (nm,tp,t) ->
       {term = Lambda (nm, map s tp, map (s+1) t); info}
    | All (nm,tp,t) ->
       {term = All (nm, map s tp, map (s+1) t); info}
    | Inspect (t,mp,arr) ->
       {term = Inspect (map s t, map s mp, Array.map (map s) arr); info}
    | Fix (idx,arr) ->
       let s = s + Array.length arr in
       {term = Fix (idx,
                    Array.map
                      (fun (nm,tp,didx,t) ->
                        nm, map s tp, didx, map s t)
                      arr);
        info}
  in
  map start t

let map_free (f:int -> int) (t:t): t = map_free_from 0 f t

let up_from (start:int) (n:int) (t:t): t =
  map_free_from start (fun i -> i + n) t

let up (n:int) (t:t): t =
  up_from 0 n t



module type PRINT_CONTEXT =
  sig
    type term = t
    type t
    val push: Feature_name.t option -> t -> t
    val count: t -> int
    val name: int -> t -> Feature_name.t option
    val shadow_level: int -> t -> int
    val type_: int -> t -> term
  end

module Printer (C:PRINT_CONTEXT) (PP:Pretty_printer.PRETTY) =
  struct
  end
