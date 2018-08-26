open Container
open Alba2_common




type fix_index = int
type decr_index = int
type oo_application = bool

type t =
  | Sort of Sorts.t
  | Variable of int
  | Application of t * t * oo_application
  | Lambda of abstraction
  | All of abstraction
  | Inspect of t * t * t array
  | Fix of fix_index * fixpoint
and typ = t
and abstraction =  string option * typ * t
and fixpoint =
  (Feature_name.t option * typ * decr_index * t) array (* typ in outer context,
                                                          t in inner context *)

type name_type = string option * typ
type fname_type = Feature_name.t option * typ
type gamma = fname_type array
type arguments = name_type array
type argument_list = name_type list



let datatype: t = Sort Sorts.Datatype
let proposition: t = Sort Sorts.Proposition
let any1: t = Sort Sorts.Any1

let sort_variable (i:int): t =
  Sort (Sorts.variable i)

let sort_variable_type (i:int): t =
  Sort (Sorts.variable_type i)


let product (a:t) (b:t): t option =
  match a, b with
  | Sort sa, Sort sb ->
     Some (Sort (Sorts.product sa sb))
  | _ ->
     None


let get_sort (a:t): Sorts.t option =
  match a with
  | Sort s ->
     Some s
  | _ ->
     None


let variable0: t = Variable 0
let variable1: t = Variable 1
let variable2: t = Variable 2
let variable3: t = Variable 3
let variable4: t = Variable 4
let variable5: t = Variable 5

let apply0 (a:t) (b:t): t =
  Application (a, b, false)



let rec equal (a:t) (b:t): bool =
  match a,b with
  | Sort sa, Sort sb ->
     Sorts.equal sa sb
  | Variable i, Variable j when i = j ->
     true
  | Application (fa,a,_), Application (fb,b,_) ->
     equal fa fb && equal a b
  | Lambda (_,tp1,t1), Lambda (_,tp2,t2)
    | All (_,tp1,t1), All (_,tp2,t2) ->
     equal tp1 tp2 && equal t1 t2
  | Inspect(e1,r1,f1), Inspect(e2,r2,f2) ->
     let n = Array.length f1 in
     n = Array.length f2
     && equal e1 e2
     && equal r1 r2
     && assert false (* nyi *)
  | Fix(i1,f1), Fix(i2,f2) when i1 = i2 ->
     assert false (* nyi *)
  | _, _ ->
     false


let equal1 (a:t option) (b:t): bool =
  match a with
  | None ->
     false
  | Some a ->
     equal a b



let fold_from (start:int) (f:'a->int->'a) (a:'a) (t:t): 'a =
  let rec fold (s:int) (a:'a) (t:t): 'a =
    match t with
    | Sort s -> a
    | Variable i when i < s ->
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
       Array.fold_left
         (fun a (_,tp,_,t) ->
           fold (s + Array.length arr) (fold s a tp) t)
         a
         arr
  in
  fold start a t


let fold (f:'a->int->'a) (a:'a) (t:t): 'a =
  fold_from 0 f a t


let has_variables (f:int->bool) (t:t): bool =
  fold
    (fun has v -> has || f v)
    false
    t


let map_from (start:int) (f:int->int) (t:t): t =
  let rec map s t =
    match t with
    | Sort s -> t
    | Variable i when i < s ->
       t
    | Variable i ->
       assert (s <= i);
       let idx = f (i-s) + s in
       assert (s <= idx); (* no capturing allowed *)
       Variable idx
    | Application (a,b,oo) ->
       Application (map s a, map s b, oo)
    | Lambda (nm,tp,t) ->
       Lambda (nm, map s tp, map (s+1) t)
    | All (nm,tp,t) ->
       All (nm, map s tp, map (s+1) t)
    | Inspect (t,mp,arr) ->
       Inspect (map s t, map s mp, Array.map (map s) arr)
    | Fix (idx,arr) ->
       let s1 = s + Array.length arr in
       Fix (idx,
            Array.map
              (fun (nm,tp,didx,t) ->
                nm, map s tp, didx, map s1 t)
              arr)
  in
  map start t

let map (f:int -> int) (t:t): t = map_from 0 f t

let shift_from (start:int) (n:int) (t:t): t =
  map_from start (fun i -> i + n) t

let shift (n:int) (t:t): t =
  shift_from 0 n t

let up_from (start:int) (n:int) (t:t): t =
  assert (0 <= n);
  shift_from start n t


let up (n:int) (t:t): t =
  assert (0 <= n);
  up_from 0 n t


let arrow (a:t) (b:t): t =
  All (None, a, up 1 b)






let rec split_application (f:t) (args:t list): t * t list =
  (* Analyze the term [f(args)] and split [f] as long as it is an
         application. Push all remaining arguments in the term [f] in front of
         the arguments [args].  *)
  match f with
  | Application (f,a,_) ->
     split_application f (a::args)
  | _ ->
     f, args



let apply_args (f:t) (args:t list): t =
  List.fold_left
    (fun f a -> Application (f,a,false))
    f args


let apply_arg_array (f:t) (args: t array): t =
  let nargs = Array.length args in
  let rec apply i t =
    if i = nargs then
      t
    else
      apply (i+1) (Application (t,args.(i),false))
  in
  apply 0 f



let apply_standard (n:int) (start:int) (f:t): t =
  (* Compute the application

         f (Variable (start+n-1)) (Variable (start+n-2)) ... (Variable start)
   *)
  let res = ref f in
  for i = 0 to n - 1 do
    res := Application (!res, Variable (start + n - 1 - i), false)
  done;
  !res



let rec split_lambda0 (a:typ) (args: argument_list): typ * argument_list =
  (* Analyze [(a:A,b:B, ...) := t], return (t, [...,b:B,a:A,args]) *)
  match a with
  | Lambda(nme,tp,t) ->
     split_lambda0 t ((nme,tp) :: args)
  | _ ->
     a, args





let rec split_product0 (a:typ) (args: argument_list): typ * argument_list =
  (* Analyze [all(a:A,b:B, ...) T], return (T, [...,b:B,a:A,args]) *)
  match a with
  | All(nme,tp,t) ->
     split_product0 t ((nme,tp) :: args)
  | _ ->
     a, args



let split_product(a:typ): arguments * typ =
  (* Analyze [all(a:A,b:B, ...) T], return ([A,B,...], T) *)
  let tp, args = split_product0 a [] in
  let n = List.length args in
  let arr = Array.make n (None,tp) in
  let rec mkarr i args =
    match args with
    | [] ->
       assert (i = 0)
    | a :: tl ->
       assert (i > 0);
       arr.(i-1) <- a;
       mkarr (i-1) tl
  in
  mkarr n args;
  arr, tp


let push_product (args:arguments) (tp:typ): typ =
  let tp = ref tp
  and n = Array.length args in
  for i = 0 to Array.length args - 1 do
    let nme,t = args.(n - 1 - i) in
    tp := All(nme,t,!tp)
  done;
  !tp



let substitute_args (n:int) (f:int->t) (t:t): t =
  (* Substitute the first [n] variables by the terms returned by the
         function [f] in the term [t]. Shift all variables above [n] down by
         [n]. *)
  let rec subst bnd t =
    match t with
    | Sort _ -> t
    | Variable i when i < bnd ->
       t
    | Variable i when i < bnd + n ->
       f (i - bnd) |> up bnd
    | Variable (i) ->
       Variable (i-n)
    | Application (a, b, oo) ->
       let sub = subst bnd in
       Application (sub a, sub b, oo)
    | Lambda (nm, tp, t0) ->
       Lambda (nm, subst bnd tp, subst (bnd+1) t0)
    | All (nm, tp, t0) ->
       All (nm, subst bnd tp, subst (bnd+1) t0)
    | Inspect (exp, map, cases) ->
       let sub = subst bnd in
       Inspect (sub exp, sub map, Array.map sub cases)
    | Fix (idx, arr) ->
       let sub = subst (bnd + Array.length arr) in
       Fix (idx,
            Array.map
              (fun (nm,tp,decr,t) -> nm, sub tp, decr, sub t)
              arr)

  in
  subst 0 t



let substitute (a:t) (b:t): t =
  (* Substitute the variable 0 in the term [a] by the term [b]. *)
  substitute_args 1 (fun _ -> b) a


let beta_reduce (f:t) (args:t list): t * t list =
  (* Beta reduce the term [f(args)] where [f] is not an
         application. Analyze the function term [f] and extract lambda terms
         possible as many as there are arguments and do beta reduction. Return
         the beta reduced term and the remaining arguments. *)
  let rec beta f args args_rest =
    match f,args_rest with
    | Lambda (_,_,t0), a :: args_rest ->
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
