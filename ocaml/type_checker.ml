open Container
open Alba2_common
open Printf
open Gamma

module Term = Term2




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
     Sorts.sub sa sb (sortvariable_le c)
  | All (_,tpa,ta), All(_,tpb,tb) ->
     equivalent tpa tpb c
     && is_subtype ta tb (push_unnamed tpa c)
  | _ ->
     equivalent_head ha hb c && equivalent_arguments argsa argsb c








let rec check (t:Term.t) (c:t): Term.typ option =
  (* Return the type of [t] in the context [c] if it is wellformed. *)
  let open Term in
  match t with
  | Sort s ->
     begin
       match s with
       | Sorts.Variable i | Sorts.Variable_type i
            when i < 0 || count_sorts c <= i ->
          None
       | _ ->
          Option.(
           Sorts.maybe_sort_of s >>= fun s ->
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
      check f c >>= fun ftp ->
      check a c >>= fun atp ->
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
      check tp c
      >> check t (push_unnamed tp c) >>= fun ttp ->
      let lam_tp = All (nme,tp,ttp) in
      check lam_tp c
      >> Some lam_tp
     )
  | All (_,arg_tp,res_tp) ->
     (* [arg_tp] must be a wellformed type. [res_tp] must be a wellformed type
        in the context with [arg_tp] pushed. The sorts of [arg_tp] and
        [res_tp] determine the sort of the quantified expression. *)
     Option.(
      let open Term in
      check arg_tp c >>= fun arg_s ->
      check res_tp (push_unnamed arg_tp c) >>= fun res_s ->
      maybe_product arg_s res_s
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
        let _,tp = Inductive.parameter i ind in
        if is_wellformed tp c then
          checki (i+1) (push_unnamed tp c)
        else
          begin
            printf "parameter %d not wellformed\n" i;
            None
          end
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
  let push_itypes (c:t): t =
    let cr = ref c in
    for i = 0 to Inductive.ntypes ind - 1 do
      let _,tp = Inductive.itype i ind in
      assert (check tp !cr <> None);
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





let test (): unit =
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

  (* all(A:Prop) A -> A : Proposition *)
  assert ( maybe_product proposition proposition = Some proposition );
  assert ( maybe_product datatype proposition    = Some proposition );
  assert ( check (All (None,
                               proposition,
                               arrow variable0 variable0)) c
           = Some proposition);

  (* all(n:Natural) n -> n is illformed *)
  assert ( check (All (None,
                               Variable 0,
                               arrow variable0 variable0)) c
           = None);

  (* Natural -> Natural : Datatype *)
  assert ( maybe_product datatype datatype    = Some datatype );
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

  (*printf "check accessible\n";
  assert (check_inductive (Inductive.make_accessible 0) c <> None);*)
  assert (check_inductive Inductive.make_natural empty <> None);
  assert (check_inductive Inductive.make_false empty <> None);
  assert (check_inductive Inductive.make_true empty <> None);
  assert (check_inductive Inductive.make_and empty <> None);
  assert (check_inductive Inductive.make_or empty <> None);
  assert (check_inductive (Inductive.make_equal 0) c <> None);
  assert (check_inductive (Inductive.make_list 0) c <> None);
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
          None [||] datatype
          [| Inductive.Constructor.make
               None [| None, arrow variable0 variable0 |] [||] |]
      in
      check_inductive ind empty = None
    end;
  ()
