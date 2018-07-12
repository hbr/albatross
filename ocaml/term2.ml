open Alba2_common

module Sort =
  struct
    type sortvariable = int
    type t =
      | Proposition
      | Level of int
      | Variable of int
      | Type_of of t
      | Max of int * sortvariable
      | Product of t * t

    let type_of (s:t): t =
      match s with
      | Proposition -> Level 1
      | Level i -> Level (i+1)
      | _ -> Type_of s

    let product (s1:t) (s2:t): t =
      match s1, s2 with
      | Proposition, s2 ->
         s2
      | _, Proposition ->
         Proposition
      | Level i, Level k ->
         Level (max i k)
      | Type_of s1, s2 when s1 = s2 ->
         Type_of s1
      | s1, Type_of s2 when s1 = s2 ->
         Type_of s1
      | Level i, Variable sv | Variable sv, Level i ->
         Max (i,sv)
      | _, _ ->
         Product (s1,s2)
  end

type fix_index = int
type decr_index = int
type oo_application = bool

type t =
  | Sort of Sort.t * Info.t
  | Variable of int * Info.t
  | Application of t * t * oo_application *Info.t
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * inspect_map * t array * Info.t
  | Fix of fix_index * fixpoint * Info.t
and typ = t
and abstraction =  string option * typ * t * Info.t
and inspect_map = t
and fixpoint = (Feature_name.t option * typ * decr_index * t) array


let maybe_sort (t:t): Sort.t option =
  match t with
  | Sort (s,_) ->
     Some s
  | _ ->
     None



let sort_of (t:t): Sort.t =
  match t with
  | Sort (s,_) ->
     s
  | _ ->
     assert false (* is not a sort *)



let fold_free_from (start:int) (f:'a->int->'a) (a:'a) (t:t): 'a =
  let rec fold s a t =
    match t with
    | Sort (s,_) -> t
    | Variable (i,_) when i < start ->
       a
    | Variable (i,_) ->
       assert (s <= i);
       f a (i-s)
    | Application (g,x,_,_) ->
       fold s (fold s a g) x
    | Lambda (_,tp,t,_) ->
       fold (s+1) (fold s a tp) t
    | All (_,tp,t,_) ->
       fold (s+1) (fold s a tp) t
    | Inspect (t,mp,arr,_) ->
       let fld = fold s in
       Array.fold_left
         fld
         (fld (fld a t) mp)
         arr
    | Fix (idx,arr,_) ->
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
  let rec map s t =
    match t with
    | Sort (s,_) -> t
    | Variable (i,_) when i < start ->
       t
    | Variable (i,info) ->
       assert (s <= i);
       Variable (f (i-s) + s, info)
    | Application (a,b,oo,info) ->
       Application (map s a, map s b, oo, info)
    | Lambda (nm,tp,t,info) ->
       Lambda (nm, map s tp, map (s+1) t, info)
    | All (nm,tp,t,info) ->
       All (nm, map s tp, map (s+1) t, info)
    | Inspect (t,mp,arr,info) ->
       Inspect (map s t, map s mp, Array.map (map s) arr, info)
    | Fix (idx,arr,info) ->
       let s = s + Array.length arr in
       Fix (idx,
            Array.map
              (fun (nm,tp,didx,t) ->
                nm, map s tp, didx, map s t)
              arr,
            info)
  in
  map start t

let map_free (f:int -> int) (t:t): t = map_free_from 0 f t

let up_from (start:int) (n:int) (t:t): t =
  map_free_from start (fun i -> i + n) t

let up (n:int) (t:t): t =
  up_from 0 n t

let rec split_application (f:t) (args:t list): t * t list =
  (* Analyze the term [f(args)] and split [f] as long as it is an
         application. Push all remaining arguments in the term [f] in front of
         the arguments [args].  *)
  match f with
  | Application (f,a,_,_) ->
     split_application f (a::args)
  | _ ->
     f, args

let apply_args (f:t) (args:t list): t =
  List.fold_left
    (fun f a -> Application (f,a,false,Info.Unknown))
    f args

let substitute (a:t) (b:t): t =
  (* Substitute the variable 0 in the term [a] by the term [b]. *)
  assert false

let substitute_args (n:int) (f:int->t) (t:t): t =
  (* Substitute the first [n] variables by the terms returned by the
         function [f] in the term [t]. Shift all variables above [n] down by
         [n]. *)
  let rec subst bnd t =
    match t with
    | Sort _ -> t
    | Variable (i,_) when i < bnd ->
       t
    | Variable (i,_) when i < bnd + n ->
       assert false
    | Variable (i,info) ->
       Variable (i-n,info)
    | Application (a, b, oo, info) ->
       let sub = subst bnd in
       Application (sub a, sub b, oo, info)
    | Lambda (nm, tp, t0, info) ->
       Lambda (nm, subst bnd tp, subst (bnd+1) t0, info)
    | All (nm, tp, t0, info) ->
       All (nm, subst bnd tp, subst (bnd+1) t0, info)
    | Inspect (exp, map, cases, info) ->
       let sub = subst bnd in
       Inspect (sub exp, sub map, Array.map sub cases, info)
    | Fix (idx, arr, info) ->
       let sub = subst (bnd + Array.length arr) in
       Fix (idx,
            Array.map
              (fun (nm,tp,decr,t) -> nm, sub tp, decr, sub t)
              arr,
            info)

  in
  subst 0 t

let beta_reduce (f:t) (args:t list): t * t list =
  (* Beta reduce the term [f(args)] where [f] is not an
         application. Analyze the function term [f] and extract lambda terms
         possible as many as there are arguments and do beta reduction. Return
         the beta reduced term and the remaining arguments. *)
  let rec beta f args args_rest =
    match f,args_rest with
    | Lambda (_,_,t0,_), a :: args_rest ->
       beta t0 (a :: args) args_rest
    | Application _, _ ->
       assert false (* [f] must not be an application. *)
    | _, _ ->
       let args = Array.of_list args in
       let nargs = Array.length args in
       (substitute_args
          nargs
          (fun i ->
            (* argument 0 is the last argument (list is reversed). Last
                   argument (innermost) has to replace the variable 0. *)
            assert (i < nargs);
            args.(i)
          )
          f),
       args_rest
  in
  beta f [] args
