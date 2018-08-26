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


let is_constructor (i:int) (c:t): bool =
  assert false (* nyi *)

let constructor_offset (i:int) (c:t): int =
  assert (is_constructor i c);
  assert false (* nyi *)

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

let push_gamma (g:Term.gamma) (c:t): t =
  push_n
    (Array.length g)
    (fun i -> g.(i))
    c


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
            {typ; just = Indtype (i,ind)}
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
