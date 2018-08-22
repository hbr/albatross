open Alba2_common
open Container
open Printf

module IArr = Immutable_array

module Term = Term2

type name_type = string option * Term.typ
type fname_type = Feature_name.t option * Term.typ
type gamma = fname_type array

(* Examples of inductive types:

   Predicate (A:Any):  Any := A -> Proposition

   Relation (A,B:Any): Any := A -> B -> Proposition

   class
       ( * ) (A:Any, r:Relation(A,A)): Relation(A,A)
   create
       start (a:A): ( *r)(a,a)
       next (a,b,c:A): ( *r)(a,b) -> r(b,c) -> ( *r)(a,c)
   end

 *)

module Constructor =
  struct
    (* c: all(args) I iparams iargs

       The type is valid in an environment with all inductive types and the
       parameters in the context (in that order)  *)
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






module Inductive =
  struct
    type t = {
        params: Term.arguments;
        types:  gamma; (* valid in a context with parameters *)
        constructors: Constructor.t array array (* valid in a context with
                                                   parameters and inductive
                                                   types *)
      }
    let nparams (ind:t): int =
      Array.length ind.params

    let ntypes (ind:t): int =
      Array.length ind.types

    let nconstructors (i:int) (ind:t): int =
      assert (i < ntypes ind);
      Array.length ind.constructors.(i)

    let constructor (i:int) (j:int) (ind:t): Constructor.t =
      assert (i < ntypes ind);
      assert (j < nconstructors i ind);
      ind.constructors.(i).(j)

    let parameter (i:int) (ind:t): string option * Term.typ =
      assert (i < nparams ind);
      ind.params.(i)

    let itype0 (i:int) (ind:t): Feature_name.t option * Term.typ =
      assert (i < ntypes ind);
      ind.types.(i)

    let itype (i:int) (ind:t): Feature_name.t option * Term.typ =
      let nme,tp = itype0 i ind in
      if i <> 0 then
        printf "itype %d\n" i;
      nme, Term.up i (Term.push_product ind.params tp)

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


    let ctype (i:int) (j:int) (ind:t): Feature_name.t option * Term.typ =
      assert (i < ntypes ind);
      assert (j < nconstructors i ind);
      let nshift = ref 0 in
      for k = 0 to i - 1 do
        nshift := !nshift + nconstructors k ind
      done;
      let nm,tp = ctype0 i j ind in
      nm, Term.up (!nshift+j) tp


    let make params types constructors =
      assert (Array.length types = Array.length constructors);
      {params; types; constructors}

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
                None, (apply0 variable2 variable1) (* List(A) *) |]
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
  end (* Inductive *)






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
    type t = bool IntMap.t IArr.t (* set of lower bounds, if maps to true,
                                     then it is a strict lower bound *)
    let count (vs:t): int =
      IArr.length vs

    let le (vs:t) (i:int) (j:int): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      try
        IntMap.mem i (IArr.elem j vs)
      with Not_found ->
        false

    let lt (vs:t) (i:int) (j:int): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      try
        IntMap.find i (IArr.elem j vs)
      with Not_found ->
        false

    let empty: t =
      IArr.empty


    let add_map (i:int) (strict:bool) (m:bool IntMap.t): bool IntMap.t =
      if strict || not (IntMap.mem i m) then
        IntMap.add i strict m
      else
        m


    let push (n:int) (cs:(int*int*bool) list) (vs:t): t =
      let nvars = n + count vs
      and vsr = ref vs in
      for i = 0 to n - 1 do
        vsr := IArr.push IntMap.empty !vsr
      done;
      assert (IArr.length !vsr = nvars);
      List.iter
        (fun (i,j,strict) ->
          assert (i <> j);
          assert (i < nvars);
          assert (j < nvars);
          assert (not (strict && le vs j i));
          let jmap = ref (IArr.elem j !vsr) in
          jmap := add_map i strict !jmap;
          (* transitive closure *)
          IntMap.iter
            (fun k kstrict -> jmap := add_map k kstrict !jmap)
            (IArr.elem i !vsr);
          vsr := IArr.put j !jmap !vsr
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
      (cons: Constructor.t array)
      (c:t)
    :t =
  let types = [| (nme, tp) |]
  and constructors = [| cons |] in
  push_inductive (Inductive.make params types constructors) c







let head_normal0
      (f:Term.t)
      (args:Term.t list)
      (c:t)
    : Term.t * Term.t list =
  (* Transform [f(args)] into the head normal form. Assume that [f(args)] is
     wellformed. Return an equivalent term [f2(args2)] which cannot be head
     reduced. *)
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




let normalize (t:Term.t) (c:t): Term.t =
  t (* nyi BUG!! *)




let rec is_subtype (a:Term.typ) (b:Term.typ) (c:t): bool =
  (* Is [a] a subtype of [b] in the context [c]. Assume that both are
     wellformed.  *)
  let ha,argsa = head_normal0 a [] c in
  let hb,argsb = head_normal0 b [] c in
  let open Term in
  match ha, hb with
  | Sort sa, Sort sb ->
     Sort.sub sa sb (sortvariable_le c)
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
       | Sort.Variable i | Sort.Variable_type i
            when i < 0 || count_sorts c <= i ->
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
  | Lambda (nme,tp,t) ->
     (* [tp] must be a wellformed type, [t] must be a wellformed term in the
        context [c,tp] and the corresponding product must be wellformed.*)
     Option.(
      maybe_type_of tp c
      >> maybe_type_of t (push_unnamed tp c) >>= fun ttp ->
      let lam_tp = All (nme,tp,ttp) in
      maybe_type_of lam_tp c
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


let is_wellformed (t:Term.t) (c:t): bool =
  maybe_type_of t c <> None

let is_wellformed_type (tp:Term.t) (c:t): bool =
  Option.(
    maybe_type_of tp c >>= fun s ->
    Term.get_sort s
  ) <> None


let check_inductive (ind:Inductive.t) (c:t): Inductive.t option =
  (* Are all parameter types are valid? *)
  let check_parameter (c:t): t option =
    let np = Inductive.nparams ind in
    let rec check i c =
      if i = np then
        Some c
      else
        let _,tp = Inductive.parameter i ind in
        if is_wellformed tp c then
          check (i+1) (push_unnamed tp c)
        else
          begin
            printf "parameter %d not wellformed\n" i;
            None
          end
    in
    check 0 c
  in
  (* Are all inductive types arities of some sort? *)
  let check_types (c:t): unit option =
    let ni = Inductive.ntypes ind in
    let rec check i =
      if i = ni then
        Some ()
      else
        let _,tp = Inductive.itype0 i ind in
        let tp = normalize tp c in
        Option.(
          maybe_type_of tp c >>= fun s ->
          Term.get_sort s (* BUG, we need the inner sort!!! *)
          >> check (i+1)
        )
    in
    check 0
  in
  let push_itypes (c:t): t =
    let cr = ref c in
    for i = 0 to Inductive.ntypes ind - 1 do
      let _,tp = Inductive.itype i ind in
      assert (maybe_type_of tp !cr <> None);
      cr := push_unnamed tp !cr
    done;
    !cr
  in
  let push_parameter (c:t): t =
    let ni = Inductive.ntypes ind
    and np = Inductive.nparams ind
    and cr = ref c in
    for i = 0 to np - 1 do
      let _,tp = Inductive.parameter i ind in
      cr := push_unnamed (Term.up_from np ni tp) !cr
    done;
    !cr
  in
  let is_positive_cargs (i:int) (j:int) (c:t): bool =
    let cargs = Inductive.cargs i j ind
    and ni = Inductive.ntypes ind
    and np = Inductive.nparams ind
    and cr = ref c in
    let indvar m v =
      m + np <= v && v < m + np + ni
    in
    try
      for k = 0 to Array.length cargs - 1 do
        let _,tp = cargs.(k) in
        if Term.has_variables (indvar k) tp then
          begin
              let tp = normalize tp !cr in
              let tpargs,tp0 = Term.split_product tp in
              let ntpargs = Array.length tpargs in
              let f,args = Term.split_application tp0 [] in
              let args = Array.of_list args in
              let nargs = Array.length args in
              assert (np <= nargs);
              if
                (* if the k-th argument is a function, then none of its
                   arguments contains an inductive type *)
                interval_for_all
                   (fun l ->
                     not (Term.has_variables
                            (indvar (k+l))
                            (snd tpargs.(l)))
                   )
                   0 ntpargs
                (* The final term constructs an inductive type *)
                && Term.has_variables (indvar (k+ntpargs)) f
                (*(* The first inductive arguments are the parameters *)
                && interval_for_all
                     (fun l ->
                       args.(l) = Term.Variable (k+np-1-l))
                     0 np*)
                (* The remaining arguments do not contain any inductive type
                 *)
                && interval_for_all
                     (fun l ->
                       not (Term.has_variables (indvar (k+ntpargs)) args.(l))
                     )
                     np nargs
              then
                ()
              else
                raise Not_found
          end;
        cr := push_unnamed tp !cr
      done;
      true
    with Not_found ->
      false
  in
  let check_constructors (c:t): unit option =
    try
      let cc = push_parameter (push_itypes c) in
      for i = 0 to Inductive.ntypes ind - 1 do
        for j = 0 to Inductive.nconstructors i ind - 1 do
          let _,tp = Inductive.ctype0 i j ind in
          if is_wellformed_type tp cc
             && Inductive.is_valid_iargs i j ind
             && is_positive_cargs i j cc
          then
            ()
          else
            raise Not_found
        done
      done;
      Some ()
    with Not_found ->
      None
  in
  Option.(
    check_parameter c >>= fun cp ->
    check_types cp
    >> check_constructors c
    >> Some ind
  )
