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
    nsorts: int;
    gamma: entry IArr.t;
    assumptions: int list
  }

let count (c:t): int =
  IArr.length c.gamma

let count_sorts (c:t): int =
  c.nsorts

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

let empty: t =
  {nsorts = 0;
   gamma = IArr.empty;
   assumptions = []}


let push (nm:Feature_name.t option) (tp:Term.typ) (c:t): t =
  let n = count c in
  {c with
    gamma = IArr.push {typ = tp; just = Assumption nm} c.gamma;
    assumptions = n :: c.assumptions}



let push_unnamed (tp:Term.typ) (c:t): t =
  push None tp c

let push_sort_variable (c:t): t =
  {c with nsorts = 1 + c.nsorts}

let push_sort_variables (n:int) (c:t): t =
  {c with nsorts = n + c.nsorts}



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
    | Term.Variable i when has_definition i c ->
       normalize (definition i c) args
    | Term.Inspect (exp,map,cases) ->
       let f1,args1 = normalize exp [] in
       begin
         match f1 with
         | Term.Variable cidx when is_constructor cidx c ->
            normalize
              cases.(constructor_offset cidx c)
              (args1 @ args)
         | _ ->
            f1, args1 @ args
       end
    | Term.Fix (idx,arr) ->
       assert false (* nyi *)

    (* error cases *)
    | Term.Sort s when args <> [] ->
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
  | Sort sa, Sort sb ->
     sa = sb
  | Variable i,  Variable j ->
     i = j
  | Lambda (_,tpa,ta), Lambda (_,tpb,tb) when equivalent tpa tpb c ->
     equivalent ta tb (push_unnamed tpa c)
  | All (_,tpa,ta), All (_,tpb,tb) when equivalent tpa tpb c ->
     equivalent ta tb (push_unnamed tpa c)
  | Inspect (ea,pa,casesa), Inspect (eb,pb,casesb)
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







let is_subsort (a:Term.Sort.t) (b:Term.Sort.t) (c:t): bool =
  assert false
  (*let open Term.Sort in
  match a, b with
  | Proposition, _ ->
     true
  | Level i, Level j ->
     i <= j
  | _ ->
     assert false (* nyi *)
   *)




let rec is_subtype (a:Term.typ) (b:Term.typ) (c:t): bool =
  (* Is [a] a subtype of [b] in the context [c]. Assume that both are
     wellformed.  *)
  let ha,argsa = head_normal0 a [] c in
  let hb,argsb = head_normal0 b [] c in
  let open Term in
  match ha, hb with
  | Sort sa, Sort sb ->
     is_subsort sa sb c
  | All (_,tpa,ta), All(_,tpb,tb) ->
     equivalent tpa tpb c
     && is_subtype ta tb (push_unnamed tpa c)
  | _ ->
     equivalent_head ha hb c && equivalent_arguments argsa argsb c








let rec maybe_type_of (t:Term.t) (c:t): Term.typ option =
  (* Return the type of [t] in the context [c] if it is wellformed. *)
  let open Term in
  match t with
  | Sort s ->
     begin
       match s with
       | Sort.Variable i | Sort.Variable_type i when i < 0 || c.nsorts <= i ->
          None
       | _ ->
          Option.(
           Sort.maybe_sort_of s >>= fun s ->
           Some (Sort s)
          )
     end

  | Variable i ->
     if  i < count c then
       Some (entry_type i c)
     else
       None

  | Application (f,a,_) ->
     (* Does the type of [a] fit the argument type of [f]? *)
     Option.(
      maybe_type_of f c >>= fun ftp ->
      maybe_type_of a c >>= fun atp ->
      match head_normal ftp c with
      | All (_, tp, res) when is_subtype atp tp c  ->
         Some (Term.substitute res a)
      | _ ->
         None
     )
  | Lambda (_,tp,t) ->
     (* [tp] must be a wellformed type, [t] must be a wellformed term in the
        context [c,tp] and the corresponding product must be wellformed.*)
     Option.(
      maybe_sort_of tp c
      >> maybe_type_of t (push_unnamed tp c) >>= fun ttp ->
      let lam_tp = All (None, tp, ttp) in
      maybe_sort_of lam_tp c
      >> Some lam_tp
     )
  | All (_,arg_tp,res_tp) ->
     (* [arg_tp] must be a wellformed type. [res_tp] must be a wellformed type
        in the context with [arg_tp] pushed. The sorts of [arg_tp] and
        [res_tp] determine the sort of the quantified expression. *)
     Option.(
      let open Term in
      maybe_type_of arg_tp c >>= fun arg_s ->
      maybe_type_of res_tp (push_unnamed arg_tp c) >>= fun res_s ->
      maybe_product arg_s res_s
     )
  | Inspect (e,res,cases) ->
     assert false (* nyi *)
  | Fix (idx, arr) ->
     assert false (* nyi *)

and maybe_sort_of (t:Term.t) (c:t): (Term.typ * Term.Sort.t) option =
  (* If [t] is a type, return the sort of the type, otherwise return [None].
     Note: [Term.typ] is redundant, it can be reconstructed from the sort.
   *)
  Option.(
    maybe_type_of t c >>= fun tp ->
    Term.maybe_sort tp >>= fun s ->
    Some (tp,s)
  )


let is_wellformed (t:Term.t) (c:t): bool =
  match maybe_type_of t c with
  | None ->
     false
  | Some _ ->
     true


(* Function arrow:

   (->) (A:Any(0), B:Any(1)): Any(0) * Any(1)
       := all(_:A) B

   (->): all(A:Any(0), B:Any(1), _:A) Any(0) * Any(1)


   We get 2 sort variables i and j: all(A:Any(i), B:Any(j), _:A) B
 *)

let test (): unit =
  Printf.printf "Test type checker\n";
  let open Term in
  let c = push_unnamed datatype
            (push_sort_variables 2 empty) in
  let c1 = push_unnamed (Variable 0) c in
  assert ( is_wellformed (sort_variable 0) c);
  assert ( is_wellformed (sort_variable 1) c);
  assert ( maybe_type_of (sort_variable 0) c = Some (sort_variable_type 0));
  assert ( maybe_type_of (sort_variable 2) c = None);
  assert ( maybe_type_of (Variable 0) c = Some datatype);
  assert ( maybe_type_of (Variable 1) c1 = Some datatype);
  assert ( is_wellformed (Variable 0) c1);
  assert ( maybe_type_of (Variable 0) c1 = Some (Variable 1));
  assert (
      Option.(
        maybe_type_of (Variable 0) c1 >>= fun tp ->
        maybe_type_of tp c1
      ) = Some datatype);
  (* Proposition -> Proposition *)
  assert ( maybe_type_of (arrow proposition proposition) c = Some any1);

  (* Natural -> Proposition *)
  assert ( maybe_type_of (arrow (Variable 0) proposition) c = Some any1);

  (* all(A:Prop) A -> A : Proposition *)
  assert ( maybe_product proposition proposition = Some proposition );
  assert ( maybe_product datatype proposition    = Some proposition );
  assert ( maybe_type_of (All (None,
                               proposition,
                               arrow (Variable 0) (Variable 0))) c
           = Some proposition);

  (* all(n:Natural) n -> n is illformed *)
  assert ( maybe_type_of (All (None,
                               Variable 0,
                               arrow (Variable 0) (Variable 0))) c
           = None);

  (* Natural -> Natural : Datatype *)
  assert ( maybe_product datatype datatype    = Some datatype );
  assert ( maybe_type_of (arrow (Variable 0) (Variable 0)) c
           = Some datatype);
  ()
