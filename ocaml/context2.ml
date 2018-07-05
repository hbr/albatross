open Alba2_common
open Container

module IArr = Immutable_array

module Term = Term2

type gamma = (Feature_name.t option * Term.typ) array

type definition =
  Feature_name.t option * Term.typ * Term.t

type inductive = {
    nparams: int;
    types:  gamma;
    constructors: gamma
  }

type justification =
  | Assumption of Feature_name.t option
  | Definition of definition
  | Indtype of int * inductive
  | Constructor of int * inductive
  | Recursive of Term.fixpoint

type entry = {
    typ:  Term.t;
    just: justification
  }

type t = {
    gamma: entry IArr.t;
    assumption: int list
  }

let count (c:t): int =
  IArr.length c.gamma

let entry (i:int) (c:t): entry =
  (* entry 0 is the most recently added (i.e. the last) element *)
  let n = count c in
  assert (i < n);
  IArr.elem (n - 1 - i) c.gamma

let entry_type (i:int) (c:t): Term.t =
  Term.up (i + 1) (entry i c).typ

let definition_opt (i:int) (c:t): Term.t option =
  assert false (* nyi *)

let has_definition (i:int) (c:t): bool =
  match definition_opt i c with
  | None -> false
  | Some _ -> true

let definition (i:int) (c:t): Term.t =
  match definition_opt i c with
  | None -> assert false (* must have a definition *)
  | Some t -> t

let is_constructor (i:int) (c:t): bool =
  assert false (* nyi *)

let constructor_offset (i:int) (c:t): int =
  assert (is_constructor i c);
  assert false (* nyi *)

let push (nm:Feature_name.t option) (tp:Term.typ) (c:t): t =
  assert false

let head_normal0
      (f:Term.t)
      (args:Term.t list)
      (c:t)
    : Term.t * Term.t list =
  (* Transform [f(args)] into the head normal form. Assume that [f(args)]
         is wellformed. Return an equivalent term [f2(args2)] which cannot be
         head reduced. *)
  let rec normalize f args =
    let f,args = Term.split_application f args in
    let f,args = Term.beta_reduce f args in
    match f with
    (* normal cases *)
    | Term.Variable (i,_) when has_definition i c ->
       normalize (definition i c) args
    | Term.Inspect (exp,map,cases,_) ->
       let f1,args1 = normalize exp [] in
       begin
         match f1 with
         | Term.Variable (cidx,_) when is_constructor cidx c ->
            normalize
              cases.(constructor_offset cidx c)
              (args1 @ args)
         | _ ->
            f1, args1 @ args
       end
    | Term.Fix (idx,arr,_) ->
       assert false (* nyi *)

    (* error cases *)
    | Term.Sort (s,_) when args <> [] ->
       assert false (* A sort cannot be applied. *)
    | Term.Application _ ->
       assert false (* f cannot be an application. *)
    | Term.Lambda _ when args <> [] ->
       assert false (* cannot happen, term is already beta reduced *)
    | Term.All _ when args <> [] ->
       assert false (* cannot be applied *)

    (* default case, beta reduced term is already in simple head normal
         form. *)
    | _ ->
       f, args
  in normalize f args


let head_normal (t:Term.t) (c:t): Term.t =
  (* Transform [t] into its head normal form. *)
  let f,args = head_normal0 t [] c in
  Term.apply_args f args


let rec equivalent (a:Term.t) (b:Term.t) (c:t): bool =
  (* Are [a] and [b] equivalent (i.e. convertible) in the context [c]?
     Assume that both terms are wellformed. *)
  let ha,argsa = head_normal0 a [] c in
  let hb,argsb = head_normal0 b [] c in
  equivalent_head ha hb c && equivalent_arguments argsa argsb c


and equivalent_head (a:Term.t) (b:Term.t) (c:t): bool =
  (* Are [a] and [b] equivalent as heads of an application in head normal form
     in the context [c]? Assume that both terms are wellformed. *)
  let open Term in
  match a, b with
  | Sort (sa,_), Sort (sb,_) ->
     sa = sb
  | Variable (i,_), Variable (j,_) ->
     i = j
  | Lambda (_,tpa,ta,_), Lambda (_,tpb,tb,_) when equivalent tpa tpb c ->
     equivalent ta tb (push None tpa c)
  | All (_,tpa,ta,_), All (_,tpb,tb,_) when equivalent tpa tpb c ->
     equivalent ta tb (push None tpa c)
  | Inspect (ea,pa,casesa,_), Inspect (eb,pb,casesb,_)
       when equivalent ea eb c && equivalent pa pa c ->
     let ncases = Array.length casesa in
     assert(ncases <> Array.length casesb);
     interval_for_all
       (fun i -> equivalent casesa.(i) casesb.(i) c)
       0 ncases
  | Fix _, Fix _ ->
     assert false (* nyi *)
  (* default case: not an  application or different constructors *)
  | _ ->
     false

and equivalent_arguments (argsa: Term.t list) (argsb:Term.t list) (c:t)
    : bool =
  match argsa, argsb with
  | [], [] ->
     true
  | a :: argsa, b :: argsb ->
     equivalent a b c && equivalent_arguments argsa argsb c
  | _ ->
     false


let rec is_subtype (a:Term.typ) (b:Term.typ) (c:t): bool =
  (* Is [a] a subtype of [b] in the context [c]. Assume that both are
     wellformed.  *)
  let ha,argsa = head_normal0 a [] c in
  let hb,argsb = head_normal0 b [] c in
  let open Term in
  match ha, hb with
  | Sort (Sort.Level i,_), Sort (Sort.Level j,_) ->
     i <= j
  | Sort (sa,_), Sort (sb,_) ->
     assert false (* nyi *)
  | All (_,tpa,ta,_), All(_,tpb,tb,_) ->
     equivalent tpa tpb c
     && is_subtype ta tb (push None tpa c)
  | _ ->
     equivalent_head ha hb c && equivalent_arguments argsa argsb c




let rec type_of (c:t) (t:Term.t): Term.typ option =
  (* Return the type of [t] if it is wellformed. *)
  let open Term in
  match t with
  | Sort (Sort.Level i,_) ->
     Some (Sort (Sort.Level (if i = 0 then 2 else i+1), Info.Unknown))
  | Sort (Sort.Variable i,_) ->
     assert false (* nyi *)
  | Variable (i,_) ->
     assert (i < count c);
     Some (entry_type i c)
  | Application (f,a,_,_) ->
     let f,args = split_application f [a] in
     Option.(
       type_of c f >>= fun f_tp ->
       let rec do_args f_tp args =
         match args with
         | [] ->
            Some f_tp
         | a::tl ->
            type_of c a >>= fun a_tp ->
            (application_result c f_tp a a_tp) >>= fun r_tp ->
            do_args r_tp tl
       in
       do_args f_tp args)
  | _ ->
     assert false

and application_result (c:t) (f:Term.typ) (a:Term.t) (a_tp:Term.typ)
    : Term.typ option =
  (* The result type of a function of type [f] applied to an argument [a]
         of type [a_tp]. Assume that both types are wellformed. Return [None]
         if a term of type [f] cannot be applied to an argument of type
         [a]. *)
  match head_normal f c with
  | Term.All (_,tp,res_tp,_) when is_subtype a_tp tp c ->
     Some (Term.substitute res_tp a)
  | _ ->
     None


let is_wellformed (c:t) (t:Term.t): bool =
  match type_of c t with
  | None -> false
  | Some _ -> true
