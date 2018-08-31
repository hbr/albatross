open Container
open Alba2_common
open Printf
open Gamma

module Term = Term2


let string_of_term (c:t) (t:Term.t): string =
  let module SP = Pretty_printer.String_printer in
  let module PP = Pretty_printer.Make (SP) in
  let module TP = Term_printer.Make (Gamma) (PP) in
  let open PP in
  SP.run 200 (make 30 () >>= TP.print t c)

let string_of_term2 (c:t) (t:Term.t): string =
  let module TP = Term_printer2.Make (Gamma) in
  Pretty_printer2.Layout.pretty 70 (TP.print t c)


let string_of_fixpoint (c:t) (fp:Term.fixpoint): string =
  let module TP = Term_printer2.Make (Gamma) in
  Pretty_printer2.Layout.pretty 70 (TP.print_fixpoint fp c)

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
              (snd cases.(constructor_offset cidx c))
              (args1 @ args)
         | _ ->
            f1, args1 @ args
       end
    | Term.Fix (idx,arr) ->
       assert false (* nyi *)

    (* error cases: shall not happen because the term is wellformed! *)
    | Term.Sort s when args <> [] ->
       assert false (* A sort cannot be applied *)
    | Term.Application _ ->
       assert false (* f cannot be an application, because of
                       'split_application. *)
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
     Sorts.equal sa sb
  | Variable i,  Variable j ->
     i = j
  | Lambda (nme,tpa,ta), Lambda (_,tpb,tb) when equivalent tpa tpb c ->
     equivalent ta tb (push_simple nme tpa c)
  | All (nme,tpa,ta), All (_,tpb,tb) when equivalent tpa tpb c ->
     equivalent ta tb (push_simple nme tpa c)
  | Inspect (ea,pa,casesa), Inspect (eb,pb,casesb)
       when equivalent ea eb c && equivalent pa pa c ->
     let ncases = Array.length casesa in
     assert(ncases <> Array.length casesb);
     interval_for_all
       (fun i ->
         let ca,fa = casesa.(i)
         and cb,fb = casesb.(i) in
         equivalent fa fb c)
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
     Sorts.sub sa sb (sort_variables c)
  | All (nme,tpa,ta), All(_,tpb,tb) ->
     equivalent tpa tpb c
     && is_subtype ta tb (push_simple nme tpa c)
  | _ ->
     equivalent_head ha hb c && equivalent_arguments argsa argsb c








let rec check (t:Term.t) (c:t): Term.typ option =
  (* Return the type of [t] in the context [c] if it is wellformed. *)
  let open Term in
  match t with
  | Sort s ->
     Option.(Sorts.type_of s (count_sorts c) >>= fun s -> Some (Sort s))

  | Variable i ->
     if  i < count c then
       Some (entry_type i c)
     else
       begin
         printf "variable (%d/%d) out of bounds\n" i (count c);
         None
       end

  | Application (f,a,_) ->
     (* Does the type of [a] fit the argument type of [f]? *)
     Option.(
      check f c >>= fun ftp ->
      check a c >>= fun atp ->
      (* Now f,ftp and a,atp are wellformed *)
      let hn = head_normal ftp c in
      match hn with
      | All (_, tp, res) (* tp, res are wellformed *)
           when is_subtype atp tp c  ->
         Some (Term.substitute res a)
      | _ ->
         None
     )
  | Lambda (nme,tp,t) ->
     (* check:
        - Is [tp] a wellformed type?
        - Is [t] a wellformed term in the context [c,tp]?
        - Is the corresponding product wellformed? *)
     Option.(
      check tp c >>= fun s ->
      Term.get_sort s
      >> check t (push_simple nme tp c) >>= fun ttp ->
      let lam_tp = All (nme,tp,ttp) in
      check lam_tp c
      >> Some lam_tp
     )
  | All (nme,arg_tp,res_tp) ->
     (* check:
        - Is [arg_tp] must be a wellformed type?
        - Is [res_tp] must be a wellformed type in the context with [c,arg_tp]?

        The sorts of [arg_tp] and [res_tp] determine the sort of the quantified
        expression. *)
     Option.(
      let open Term in
      check arg_tp c >>= fun arg_s ->
      check res_tp (push_simple nme arg_tp c) >>= fun res_s ->
      product arg_s res_s
     )
  | Inspect (e,res,cases) ->
     assert false (* nyi *)
  | Fix (idx, arr) ->
     assert false (* nyi *)



let check_with_sort (t:Term.t) (c:t): (Term.typ*Term.typ) option =
  Option.(
    check t c >>= fun tp ->
    check tp c >>= fun s ->
    Some (tp,s)
  )


let is_wellformed (t:Term.t) (c:t): bool =
  check t c <> None


let is_wellformed_type (tp:Term.t) (c:t): bool =
  Option.(
    check tp c >>= fun s ->
    Term.get_sort s
  ) <> None





let check_inductive (ind:Inductive.t) (c:t): Inductive.t option =
  (* Are all parameter types are valid? *)
  let check_parameter (c:t): t option =
    let np = Inductive.nparams ind in
    let rec checki i c =
      if i = np then
        Some c
      else
        let nme,tp = Inductive.parameter i ind in
        if is_wellformed tp c then
          checki (i+1) (push (some_feature_name_opt nme) tp c)
        else
          None
    in
    checki 0 c
  in
  (* Are all inductive types arities of some sort? *)
  let check_types (c:t): unit option =
    let ni = Inductive.ntypes ind in
    let rec checki i =
      if i = ni then
        Some ()
      else
        let _,tp = Inductive.itype0 i ind in
        let tp = normalize tp c in
        Option.(
          check tp c >>= fun s ->
          Term.get_sort s (* BUG, we need the inner sort!!! *)
          >> checki (i+1)
        )
    in
    checki 0
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
        let nme,tp = cargs.(k) in
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
        cr := push (some_feature_name_opt nme) tp !cr
      done;
      true
    with Not_found ->
      false
  in
  let check_constructors (c:t): unit option =
    try
      let cc = Gamma.push_ind_types_params ind c in
      for i = 0 to Inductive.ntypes ind - 1 do
        for j = 0 to Inductive.nconstructors i ind - 1 do
          let nme,tp = Inductive.ctype0 i j ind in
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





(* Some builtin types and functions *)
(* -------------------------------- *)


(* Predicate (A:Any): Any := A -> Proposition *)
let predicate (sv0:int): Gamma.Definition.t =
  let open Term in
  let v0 = sort_variable sv0 in
  let t = Lambda (Some "A", v0, arrow variable0 proposition)
  and typ = All (Some "A", v0, v0) in
  Definition.make_simple (Some "Predicate") typ t []


(* Relation (A,B:Any): Any := A -> Proposition *)
let binary_relation (sv0:int): Gamma.Definition.t =
  let open Term in
  let v0 = sort_variable sv0
  and v1 = sort_variable (sv0+1) in
  let t = Lambda
            (Some "A",v0,
             Lambda
               (Some "B",v1,
                arrow variable1 (arrow variable0 proposition)))
  and typ = All
              (Some "A",
               v0,
               All
                 (Some "B",
                  v1,
                  product1 v0 v1))
  in
  Definition.make_simple (Some "Relation") typ t []


(* Endo_relation (A:Any): Any := Relation(A,A) *)
let endorelation (sv0:int) (rel_idx:int) (rel_sv0:int): Definition.t =
  let open Term in
  let t =
    Lambda
      (Some "A",
       sort_variable sv0,
       apply_args (Variable (rel_idx+1)) [variable0;variable0])
  and typ =
    All
      (Some "A",
       sort_variable sv0,
       product1 (sort_variable rel_sv0) (sort_variable (rel_sv0+1)))
  in
  Definition.make_simple (Some "Endorelation") typ t
    [(sv0,rel_sv0,false); (sv0,rel_sv0+1,false)]




(* pred0 (a:Natural): Natural :=
        inspect
            a
        case
            0 := 0
            n.successor := n
        end
 *)
let nat_pred0 (nat_idx:int): Gamma.Definition.t =
  assert (2 <= nat_idx);
  let open Term in
  let nat_tp = Variable nat_idx
  and nat_succ = Variable (nat_idx - 2)
  and nat_zero = Variable (nat_idx - 1)
  in
  let nme = some_feature_operator Operator.Plusop
  and typ = arrow nat_tp nat_tp
  in
  let t =
    Lambda(
        (Some "a"),
        nat_tp,
        Inspect (
            variable0,
            Lambda (None, up 1 nat_tp, up 2 nat_tp),
            [|up 1 nat_zero, up 1 nat_zero;
              Lambda(Some "n", up 1 nat_tp, apply1 (up 2 nat_succ) variable0),
              Lambda(Some "n", up 1 nat_tp, variable0)
            |]))
  in
  Gamma.Definition.make nme typ t []


(* (+)(a,b:Natural): Natural :=
       inspect a case
           0 := b
           n.successor := n + b.successor
       end
 *)
let nat_add_fp (nat_idx:int): Term.fixpoint =
  assert (2 <= nat_idx);
  let open Term in
  let nat_tp = Variable nat_idx
  and nat_zero = Variable (nat_idx - 1)
  and nat_succ = Variable (nat_idx - 2)
  in
  let nme = some_feature_operator Operator.Plusop
  and typ =
    arrow nat_tp (arrow nat_tp nat_tp)
  in
  let t =
    lambda
      [Some "a", up 1 nat_tp;
       Some "b", up 2 nat_tp]
      (Inspect( (* inner context has 3 variables: (+) a b *)
           variable1,
           Lambda (None, up 3 nat_tp, up 4 nat_tp),
           [| up 3 nat_zero,
              variable0;

              Lambda(Some "n", up 3 nat_tp, apply1 (up 4 nat_succ) variable0),
              Lambda (Some "n",
                      up 3 nat_tp,
                      apply2
                        variable3
                        variable0
                        (apply1 (up 4 nat_succ) variable1))
           |]
      ))
  in
  [|nme,typ,0,t|]







let print_type_of (t:Term.t) (c:t): unit =
  match check t c with
  | None ->
     printf "not wellformed %s\n" (string_of_term c t);
  | Some tp ->
     printf "%s : %s\n" (string_of_term c t) (string_of_term c tp)

let test (): unit =
  let equal_opt a b =
    match a with
    | None ->
       false
    | Some a ->
       Term.equal a b
  in
  Printf.printf "test type checker\n";
  let open Term in
  let c = push_unnamed datatype
            (push_sorts 2 [0,1,false] empty) in
  let c1 = push_unnamed variable0 c in
  assert ( is_wellformed (sort_variable 0) c);
  assert ( is_wellformed (sort_variable 1) c);
  assert ( check (sort_variable 0) c = Some (sort_variable_type 0));
  assert ( check (sort_variable 2) c = None);
  assert ( check variable0 c = Some datatype);
  assert ( check variable1 c1 = Some datatype);
  assert ( is_wellformed variable0 c1);
  assert ( check variable0 c1 = Some variable1);
  assert
    begin
      Option.( check_with_sort variable0 c1 >>= fun (_,s) ->
               Some s
      ) = Some datatype
    end;

  (* Proposition -> Proposition *)
  assert ( check (arrow proposition proposition) c = Some any1);

  (* Natural -> Proposition *)
  assert ( check (arrow variable0 proposition) c = Some any1);

  (* (Natural -> Proposition) -> Proposition **)
  assert ( check (arrow
                    (arrow variable0 proposition)
                    proposition) c = Some any1);

  (* all(A:Prop) A -> A : Proposition *)
  assert ( product proposition proposition = Some proposition );
  assert ( product datatype proposition    = Some proposition );
  assert ( check (All (None,
                       proposition,
                       arrow variable0 variable0)) c
           = Some proposition);

  (* all(n:Natural) n -> n is illformed, n is not a type! *)
  assert ( check (All (None,
                       Variable 0,
                       arrow variable0 variable0)) c
           = None);

  (* Natural -> Natural : Datatype *)
  assert ( product datatype datatype    = Some datatype );
  assert ( check (arrow variable0 variable0) c
           = Some datatype);

  (* ((A:Prop,p:A) := p): all(A:Prop) A -> A *)
  assert ( check
             (Lambda (None,
                      proposition,
                      Lambda (None,
                              variable0,
                              variable0)
                ))
             c
           = Some (All (None,
                        proposition,
                        arrow variable0 variable0) )
    );

  (* All prover type:
         all(p:Proposition) p: Proposition
     is equivalent to false *)
  assert( check (All (Some "p", proposition, variable0)) empty
          = Some proposition);

  (* All inhabitor type:
         all(p:SV0) p:  SV0'
     is equivalent to false *)
  assert( check (All (Some "T", sort_variable 0, variable0)) c
          = Some (sort_variable_type 0));

  assert (check_inductive Inductive.make_natural empty <> None);
  assert (check_inductive Inductive.make_false empty <> None);
  assert (check_inductive Inductive.make_true empty <> None);
  assert (check_inductive Inductive.make_and empty <> None);
  assert (check_inductive Inductive.make_or empty <> None);
  assert (check_inductive (Inductive.make_equal 0) c <> None);
  assert (check_inductive (Inductive.make_list 0) c <> None);
  assert (check_inductive (Inductive.make_accessible 0) c <> None);

  (* class Natural create 0; successor(Natural) end *)
  ignore(
      let ind = Inductive.make_natural
      in
      assert (check_inductive ind empty <> None);
      let c = push_inductive ind empty in
      assert (check variable2 c = Some datatype);
      assert (check variable1 c = Some variable2);
      assert (check variable0 c = Some (arrow variable2 variable2))
    );


  (* Failed positivity:
     class C create
         _ (f:C->C): C
     end
   *)
  assert
    begin
      let ind =
        Inductive.make_simple
          (some_feature_name "C") [||] datatype
          [| Inductive.Constructor.make
               None [| None, arrow variable0 variable0 |] [||] |]
      in
      check_inductive ind empty = None
    end;


  (* Predicate, Relation, Endorelation *)
  assert
    begin
      let d = predicate 0 in
      equal_opt
        (check (Definition.term d) c)
        (Definition.typ d)
    end;
  assert
    begin
      let d = binary_relation 0 in
      equal_opt
        (check (Definition.term d) c)
        (Definition.typ d)
    end;
  begin
    let endo = endorelation 2 0 0 in
    let c =
      (push_sorts 3 (Definition.constraints endo) empty)
      |> push_definition (binary_relation 0)
    in
    assert (equal_opt (check (Definition.term endo) c) (Definition.typ endo));
    let c =
      push_definition endo c
      |> push_simple (Some "Natural") datatype in
    (* Endorelation(Natural) *)
    let endo_nat = Application(variable1,variable0,false) in
    (*print_type_of endo_nat c;*)
    assert (is_wellformed endo_nat c)
  end;

  (* Predecessor and addition of natural numbers *)
  begin
    let ind = Inductive.make_natural
    in
    let c = push_inductive ind empty in
    let pred = nat_pred0 2 in
    printf "%s\n" (string_of_term2 c (Definition.term pred));
    let plus_fp = nat_add_fp 2 in
    printf "%s\n" (string_of_fixpoint c plus_fp)
  end;
  ()
