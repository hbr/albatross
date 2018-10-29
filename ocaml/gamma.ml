open Alba2_common
open Container
open Printf

module IArr = Immutable_array

module Term = Term2



type constraint_list = (int*int*bool) list

module Definition =
  struct
    type t = {name: Feature_name.t option;
              typ:  Term.typ;
              term: Term.t;
              constraints: constraint_list}
    let name (def:t): Feature_name.t option = def.name
    let typ (def:t): Term.typ = def.typ
    let term (def:t): Term.t  = def.term
    let constraints (def:t): constraint_list = def.constraints
    let make name typ term constraints = {name;typ;term;constraints}
    let make_simple name typ term constraints =
      make (some_feature_name_opt name) typ term constraints
  end


type justification =
  | Assumption of Feature_name.t option
  | Definition of Definition.t
  | Indtype of int * Inductive.t
  | Constructor of int * int * Inductive.t
  | Recursive of Term.fixpoint

type entry = {
    typ:  Term.t;
    just: justification
  }




type t = {
    sort_variables: Sorts.Variables.t;
    gamma: entry IArr.t;
    assumptions: int list
  }


let count_sorts (c:t): int =
  Sorts.Variables.count c.sort_variables


let sort_variables (c:t): Sorts.Variables.t =
  c.sort_variables


let push_sorts (n:int) (cs: (int*int*bool) list) (c:t): t =
  {c with
    sort_variables = Sorts.Variables.push n cs c.sort_variables}

let push_sort_variables (n:int) (c:t): t =
  push_sorts n [] c


let push_sort_variable (c:t): t =
  push_sort_variables 1 c







let count (c:t): int =
  IArr.length c.gamma


let to_level (i:int) (c:t): int =
  assert (i < count c);
  count c - i - 1

let to_index (level:int) (c:t): int =
  assert (level < count c);
  (* to_index (to_level i c) c =
     count c - (count c - i - 1) - 1 =
     count c - count c + i + 1 - 1 =  i
   *)
  count c - level - 1

let entry (i:int) (c:t): entry =
  (* entry 0 is the most recently added (i.e. the last) element *)
  let n = count c in
  assert (i < n);
  IArr.elem (n - 1 - i) c.gamma

let entry_type (i:int) (c:t): Term.t =
  Term.up (i + 1) (entry i c).typ

let name (i:int) (c:t): Feature_name.t option =
  match (entry i c).just with
  | Assumption nme ->
     nme
  | Definition def ->
     Definition.name def
  | Indtype (i,ind) ->
     Inductive.name i ind
  | Constructor (i,j,ind) ->
     Inductive.cname i j ind
  | Recursive fp ->
     assert false

let definition_term (i:int) (c:t): Term.t option =
  match (entry i c).just with
  | Definition d ->
     Some (Definition.term d)
  | _ ->
     None


let has_definition (i:int) (c:t): bool =
  match definition_term i c with
  | None -> false
  | Some _ -> true


let definition (i:int) (c:t): Term.t =
  match definition_term i c with
  | None -> assert false (* illegal call *)
  | Some t -> t



let inductive_index (t:Term.t) (c:t): (int * Inductive.t) option =
  let open Term in
  match t with
  | Variable i when i < count c ->
     begin
       match (entry i c).just with
       | Indtype (i,ind) ->
          Some (i,ind)
       | _ ->
          None
     end
  | _ ->
     None


let constructor_index (t:Term.t) (c:t): (int * int * Inductive.t) option =
  let open Term in
  match t with
  | Variable i when i < count c ->
     begin
       match (entry i c).just with
       | Constructor (i,j,ind) ->
          Some (i,j,ind)
       | _ ->
          None
     end
  | _ ->
     None


let is_inductive (i:int) (c:t): bool =
  match (entry i c).just with
  | Indtype _ ->
     true
  | _ ->
     false

let count_inductive_params_and_types (i:int) (c:t): (int * int) option =
  match (entry i c).just with
  | Indtype (ii,ind) ->
     Some (Inductive.nparams ind, Inductive.ntypes ind)
  | _ ->
     None



let is_constructor (i:int) (c:t): bool =
  assert false (* nyi *)

let constructor_offset (i:int) (c:t): int =
  assert (is_constructor i c);
  assert false (* nyi *)


let constructor_of_inductive (j:int) (ivar:int) (c:t): int =
  (* The index of the j-th constructor of the inductive type i *)
  match  (entry ivar c).just with
  | Indtype (i,ind)  ->
     to_index
       (to_level ivar c - i        (* start level of the family *)
        + Inductive.ntypes ind     (* start level of constructors *)
        + Inductive.constructor_base_index i ind
        + j)
       c
  | _ ->
     assert false (* Illegal call *)


let constructor_of_inductive_variable (j:int) (ivar:Term2.t) (c:t): int =
  (* The index of the j-th constructor of the inductive type ivar *)
  match ivar with
  | Term.Variable i ->
     constructor_of_inductive j i c
  | _ ->
     assert false (* Illegal call *)


let constructor_types (i:int) (params:Term.t list) (c:t): Term.typ list =
  (* The constructor types of the inductive type [i] applied to the parameters
     [params]. *)
  match (entry i c).just with
  | Indtype (ith,ind) ->
     assert (Inductive.nparams ind = List.length params);
     assert false (* nyi *)
  | _ ->
     assert false (* Illegal call: [i] is not an inductive type. *)



let inductive_family (i:int) (c:t): int * Inductive.t =
  match (entry i c).just with
  | Indtype (ith,ind) ->
     ith, ind
  | _ ->
     assert false (* Illegal call: [i] is not part of an inductive definition.*)



let empty: t =
  {sort_variables = Sorts.Variables.empty;
   gamma = IArr.empty;
   assumptions = []}


let push_definition
      (d: Definition.t) (c:t)
    : t =
  {c with gamma =
            IArr.push {typ = Definition.typ d;
                       just = Definition d}
              c.gamma}




let push (nm:Feature_name.t option) (tp:Term.typ) (c:t): t =
  let n = count c in
  {c with
    gamma = IArr.push {typ = tp; just = Assumption nm} c.gamma;
    assumptions = n :: c.assumptions}

let push_simple (nme:string option) (tp:Term.typ) (c:t): t =
  push (some_feature_name_opt nme) tp c

let push_unnamed (tp:Term.typ) (c:t): t =
  push None tp c


let push_n (n:int) (f:int -> Term.fname_type) (c:t): t =
  let cr = ref c in
  for i = 0 to n - 1 do
    let nme,tp = f i in
    cr := push nme tp !cr
  done;
  !cr

let push_arguments (args:Term.arguments) (c:t): t =
  push_n
    (Array.length args)
    (fun i -> let nme,tp = args.(i) in
              some_feature_name_opt nme,tp)
    c

let rec push_argument_list (args:Term.argument_list) (c:t): t =
  match args with
  | [] ->
     c
  | (nme,tp) :: tl ->
     push_argument_list tl (push_simple nme tp c)


let push_fixpoint (fp:Term.fixpoint) (c:t): t =
  interval_fold
    (fun c i ->
      let nme,tp,_,_ = fp.(i) in
      push nme (Term.up i tp) c)
    c 0 (Array.length fp)


let push_gamma (g:Term.gamma) (c:t): t =
  push_n
    (Array.length g)
    (fun i -> g.(i))
    c


let push_lambda (t:Term.t) (c:t): Term.t * t =
  let t1,args = Term.split_lambda0 (-1) t 0 [] in
  let c1 = push_argument_list (List.rev args) c in
  t1,c1



let push_ind_params (ind: Inductive.t) (c:t): t =
  push_arguments (Inductive.params0 ind) c


let push_ind_types_params (ind:Inductive.t) (c:t): t =
  push_gamma (Inductive.types ind) c
  |> push_arguments (Inductive.params ind)


let push_inductive
      (ind:Inductive.t)
      (c:t)
    :t =
  let gr = ref c.gamma in
  for i = 0 to Inductive.ntypes ind - 1 do
    let nme,typ = Inductive.itype i ind in
    gr := IArr.push
            {typ = Term.up i typ;
             just = Indtype (i,ind)}
            !gr
  done;
  for i = 0 to Inductive.ntypes ind - 1 do
    for j = 0 to Inductive.nconstructors i ind - 1 do
      let nme,typ = Inductive.ctype i j ind in
      gr := IArr.push
              {typ; just = Constructor (i,j,ind)}
              !gr
    done
  done;
  {c with gamma = !gr}



let push_simple_inductive
      (nme: Feature_name.t option)
      (params:Term.arguments)
      (tp: Term.typ)
      (cons: Inductive.Constructor.t array)
      (c:t)
    :t =
  let types = [| (nme, tp) |]
  and constructors = [| cons |] in
  push_inductive (Inductive.make params types constructors) c
