open Alba2_common
open Container
open Printf

module IArr = Immutable_array

module Term = Term2





type definition =
  Feature_name.t option * Term.typ * Term.t


type justification =
  | Assumption of Feature_name.t option
  | Definition of definition
  | Indtype of int * Inductive.t
  | Constructor of int * int * Inductive.t
  | Recursive of Term.fixpoint

type entry = {
    typ:  Term.t;
    just: justification
  }


module Sort_variables =
  struct
    type t = Sorts.Set.t IArr.t

    let count (vs:t): int =
      IArr.length vs

    let le (vs:t) (i:int) (j:int): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      Sorts.Set.is_lower_bound i (IArr.elem j vs)

    let lt (vs:t) (i:int) (j:int): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      Sorts.Set.is_strict_lower_bound i (IArr.elem j vs)

    let empty: t =
      IArr.empty


    let push (n:int) (cs:(int*int*bool) list) (vs:t): t =
      let nvars = n + count vs
      and vsr = ref vs in
      for i = 0 to n - 1 do
        vsr := IArr.push Sorts.Set.empty !vsr
      done;
      assert (IArr.length !vsr = nvars);
      List.iter
        (fun (i,j,strict) ->
          assert (i <> j);
          assert (i < nvars);
          assert (j < nvars);
          assert (not (strict && le vs j i));
          (* add i and the transitive closure to the lower bounds of j *)
          vsr := IArr.put
                   j
                   (Sorts.Set.add i strict (IArr.elem j !vsr)
                    |> Sorts.Set.union (IArr.elem i !vsr))
                   !vsr
        )
        cs;
      !vsr
  end

type t = {
    sort_variables: Sort_variables.t;
    gamma: entry IArr.t;
    assumptions: int list
  }


let count_sorts (c:t): int =
  Sort_variables.count c.sort_variables


let sortvariable_le (c:t) (i:int) (j:int): bool =
  Sort_variables.le c.sort_variables i j


let sortvariable_lt (c:t) (i:int) (j:int): bool =
  Sort_variables.lt c.sort_variables i j


let push_sorts (n:int) (cs: (int*int*bool) list) (c:t): t =
  {c with
    sort_variables = Sort_variables.push n cs c.sort_variables}

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
  | Definition (nme,_,_) ->
     nme
  | Indtype (i,ind) ->
     Inductive.name i ind
  | Constructor (i,j,ind) ->
     Inductive.cname i j ind
  | Recursive fp ->
     assert false

let definition_opt (i:int) (c:t): Term.t option =
  match (entry i c).just with
  | Definition _ ->
     assert false (* nyi *)
  | _ ->
     None

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
  {sort_variables = Sort_variables.empty;
   gamma = IArr.empty;
   assumptions = []}


let push (nm:Feature_name.t option) (tp:Term.typ) (c:t): t =
  let n = count c in
  {c with
    gamma = IArr.push {typ = tp; just = Assumption nm} c.gamma;
    assumptions = n :: c.assumptions}



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
