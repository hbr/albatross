open Container
open Alba2_common

module Term = Term2

module Constructor =
  struct
    (* A constructor consists of a name and a type. The type is a function
       type i.e. a product of a function with 0 or more arguments. The final
       type of the product is the inductive type of the constructed object.

           c: all(args) I iparams iargs

       The parameters are fixed and identical for all inductive types and all
       constructors. The [iargs] can depent on the [args].

       The type is valid in an environment with all inductive types and the
       parameters in the context (in that order) *)
    type t = {
        name: Feature_name.t option;
        args: Term.arguments;  (* without parameters *)
        iargs: Term.t array    (* only index, no parameters *)
      }
    let make name args iargs :t =
      {name; args; iargs}

    let name (c:t): Feature_name.t option = c.name

    let cargs (c:t): Term.arguments = c.args


    let ctype (i:int) (ni:int) (np:int) (c:t): Term.typ =
      let open Term in
      let ncargs = Array.length c.args in
      push_product
        c.args
        (apply_arg_array
           (apply_standard np ncargs (Variable (ncargs + i)))
           c.iargs)

    let is_valid_iargs (ni:int) (np:int) (c:t): bool =
      (* The arguments (index) of the constructed inductive type must not
         contain any other inductive type of the definition. The context
         contains all inductive types and the parameters in this order. *)
      interval_for_all
        (fun i ->
          not (Term.has_variables
                 (fun v -> np <= v && v < ni + np)
                 c.iargs.(i)))
      0 (Array.length c.iargs)

  end (* Constructor *)






type t = {
    params: Term.arguments;
    types:  Term.gamma; (* valid in a context with parameters *)
    restr:  bool array;
    constructors: Constructor.t array array (* valid in a context with
                                                   parameters and inductive
                                                   types *)
  }
let nparams (ind:t): int =
  Array.length ind.params

let ntypes (ind:t): int =
  Array.length ind.types

let is_restricted (i:int) (ind:t): bool =
  ind.restr.(i)

let nconstructors (i:int) (ind:t): int =
  assert (i < ntypes ind);
  Array.length ind.constructors.(i)

let constructor (i:int) (j:int) (ind:t): Constructor.t =
  assert (i < ntypes ind);
  assert (j < nconstructors i ind);
  ind.constructors.(i).(j)


let recursive_arguments (i:int) (j:int) (ind:t): int list =
  (* The recursive arguments of the constructor. *)
  assert (i < ntypes ind);
  let con = constructor i j ind in
  let args = Constructor.cargs con in
  let nargs = Array.length args in
  let np = nparams ind
  and nt = ntypes ind in
  let is_inductive i =
    np <= i && i <= np + nt
  in
  interval_fold
    (fun lst i ->
      let j = nargs - i - 1 in
      let _,tp = args.(j) in
      if Term.has_variables is_inductive tp then
        j :: lst
      else
        lst
    )
    [] 0 nargs


let parameter (i:int) (ind:t): string option * Term.typ =
  assert (i < nparams ind);
  ind.params.(i)

let params0 (ind:t): Term.arguments =
  ind.params

let params (ind:t): Term.arguments =
  let ni = ntypes ind
  and np = nparams ind in
  Array.map
    (fun (nme,tp) -> nme, Term.up_from np ni tp)
    ind.params

let name (i:int) (ind:t): Feature_name.t option =
  assert (i < ntypes ind);
  fst ind.types.(i)

let types0 (ind:t): Term.gamma =
  ind.types

let itype0 (i:int) (ind:t): Term.fname_type =
  assert (i < ntypes ind);
  ind.types.(i)


let itype (i:int) (ind:t): Term.fname_type =
  let nme,tp = itype0 i ind in
  nme, Term.push_product ind.params tp



let types (ind:t): Term.gamma =
  Array.map
    (fun (nme,tp) -> nme, Term.push_product ind.params tp)
    ind.types

let cname (i:int) (j:int) (ind:t): Feature_name.t option =
  Constructor.name (constructor i j ind)

let ctype0 (i:int) (j:int) (ind:t): Feature_name.t option * Term.typ =
  let ni = ntypes ind
  and np = nparams ind
  and cons = constructor i j ind in
  Constructor.name cons,
  Constructor.ctype (np + ni - 1 - i) ni np cons

let is_valid_iargs (i:int) (j:int) (ind:t): bool =
  Constructor.is_valid_iargs
    (ntypes ind)
    (nparams ind)
    (constructor i j ind)

let cargs (i:int) (j:int) (ind:t): Term.arguments =
  Constructor.cargs (constructor i j ind)


let constructor_base_index (i:int) (ind:t): int =
  assert (i < ntypes ind);
  let base = ref 0 in
  for k = 0 to i - 1 do
    base := !base + nconstructors k ind
  done;
  !base

let ctype (i:int) (j:int) (ind:t): Feature_name.t option * Term.typ =
  assert (i < ntypes ind);
  assert (j < nconstructors i ind);
  let nshift = constructor_base_index i ind in
  let nm,tp = ctype0 i j ind in
  nm, Term.up (nshift+j) tp


let restricted (i:int) (ind:t): t =
  assert (i < ntypes ind);
  let restr = Array.copy ind.restr in
  restr.(i) <- true;
  {ind with restr}

let make params types constructors =
  assert (Array.length types = Array.length constructors);
  let restr = Array.make (Array.length types) false in
  {params; types; restr; constructors}

let make_simple nme params tp cons =
  let types = [| (nme, tp) |]
  and constructors = [| cons |] in
  make params types constructors


(* class
       Natural
   create
       0
       successor(Natural)
   end *)
let make_natural: t =
  let open Term in
  make_simple
    (some_feature_name "Natural")
    [||]     (* no parameter *)
    datatype (* of sort datatype *)
    [|
      Constructor.make
        (some_feature_number 0)
        [||] [||];
      Constructor.make
        (some_feature_name "successor")
        [|None,variable0|] [||]
    |]

(* class
       List(A)
   create
       []
       (^)(A,List(A))
   end
 *)
let make_list (sv0:int): t =
  let open Term in
  make_simple
    (some_feature_name "List")
    [| Some "A",sort_variable sv0 |]
    (sort_variable (sv0+1))
    [| Constructor.make
         some_feature_bracket
         [||]
         [||];
       Constructor.make
         (some_feature_operator Operator.Caretop)
         [| None, variable0;  (* A *)
            None, (apply1 variable2 variable1) (* List(A) *) |]
         [| |]
    |]


(* class false create end *)
let make_false: t =
  let open Term in
  make_simple
    some_feature_false
    [||] proposition [||]



(* class true create
       true_is_valid
    end *)
let make_true: t =
  let open Term in
  make_simple
    some_feature_true
    [||] proposition
    [| Constructor.make
         (some_feature_name "true_is_valid") [||] [||] |]


(* class
       (and) (a,b:Proposition): Proposition
   create
       conjunction (a,b): a and b
   end
 *)
let make_and: t =
  let open Term in
  make_simple
    (some_feature_operator Operator.Andop)
    [| Some "a", proposition; Some "b", proposition |]
    proposition
    [| Constructor.make
         (some_feature_name "conjunction")
         [| None, variable1; None, variable1|]
         [||]
    |]


(* class
       (or) (a,b:Proposition): Proposition
   create
       left (a): a or b
       right(b): a or b
   end
 *)
let make_or: t =
  let open Term in
  make_simple
    (some_feature_operator Operator.Orop)
    [| Some "a", proposition; Some "b", proposition |]
    proposition
    [| Constructor.make
         (some_feature_name "left")
         [| None, variable1|]
         [||];
       Constructor.make
         (some_feature_name "right")
         [| None, variable0|]
         [||]
    |]



(* class
       accessible (A:Any, r:Relation(A,A), y:A): Proposition
   create
       access_intro
           (f:all(x) r(x,y) -> r.accessible(x))
           : r.accessible(y)
   end
 *)
let make_accessible (sv0:int): t =
  let open Term in
  make_simple
    (some_feature_name "accessible")
    [| Some "A", sort_variable sv0;
       Some "r", arrow variable0 (arrow variable0 proposition);
       Some "y", variable1|]
    proposition
    [| Constructor.make
         (some_feature_name "access_intro")
         [| Some "f",
            All(Some "x",
                variable2,
                arrow
                  (apply_args variable2 [variable0;variable1])
                  (apply_args variable4 [variable3;variable2;variable0])
              ) |]
         [||]
    |]


(* class
       (=) (A:Any, a:A): all(B:Any) B -> Proposition
   create
       reflexive: a = a
   end
 *)
let make_equal (sv0:int): t =
  let open Term in
  make_simple
    (some_feature_operator Operator.Eqop)
    [| (Some "A",sort_variable sv0); (Some "a",variable0) |]
    (All (Some "B",sort_variable (sv0+1), arrow variable0 proposition))
    [| Constructor.make
         (some_feature_name "reflexive")
         [||] [| variable1; variable0 |]|]
