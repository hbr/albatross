open Container
open Term
open Signature
open Support
open Printf


module Accu: sig

  type t
  val signature:         t -> Sign.t
  val signature_string:  t -> string
  val substitution_string: t -> string
  val ntvars:            t -> int
  val make:              type_term -> Context.t -> t
  val add_leaf:          int ->  TVars.t -> Sign.t ->  t -> t
  val expect_function:   int -> t -> unit
  val expect_argument:   int -> t -> unit
  val expect_lambda:     int -> t -> unit
  val complete_lambda:   int -> int array -> t -> unit
  val complete_function: int -> t -> unit
  val check_type_variables: info -> t -> unit
  val result:            t -> term * TVars_sub.t

end = struct

  type t = {mutable tlist: term list;
            mutable sign:  Sign.t;  (* expected *)
            mutable tvars: TVars_sub.t;
            c: Context.t}

  let signature (acc:t): Sign.t = Sign.substitute acc.sign acc.tvars

  let ntvars (acc:t): int = TVars_sub.count acc.tvars

  let string_of_signature (s:Sign.t) (acc:t): string =
    let ntvs    = ntvars acc
    and fgnames = Context.fgnames acc.c
    and ct      = Context.class_table acc.c in
    Class_table.string_of_signature s ntvs fgnames ct

  let signature_string (acc:t): string =
    let s       = signature acc in
    string_of_signature s acc

  let substitution_string (acc:t): string =
    let sub_lst  = Array.to_list (TVars_sub.args acc.tvars)
    and ntvs     = ntvars acc
    and fnames   = Context.fgnames acc.c
    and ct       = Context.class_table acc.c
    in
    "[" ^
    (String.concat
       ","
       (List.map
          (fun tp -> Class_table.type2string tp ntvs fnames ct)
          sub_lst)) ^
    "]"





  let add_sub (ok:bool) (i:int) (t:term) (acc:t): unit =
    if ok then
      TVars_sub.put_sub i t acc.tvars
    else
      raise Not_found



  let do_sub (i:int) (t:term) (acc:t): unit =
    (** Substitute the variable [i] by the term [t].
     *)
    let cnt     = TVars_sub.count acc.tvars
    and cnt_loc = TVars_sub.count_local acc.tvars
    in
    assert (i<cnt);
    match t with
      Variable j when j<cnt ->
        if i=j then ()
        else
          let lo,hi = if i<=j then i,j else j,i in
          let thi   = Variable hi in
          let ok =
            lo < cnt_loc ||
            Context.concept_satisfies_concept
              (TVars_sub.concept hi acc.tvars)
              (TVars_sub.concept lo acc.tvars)
              acc.c
          in
          add_sub ok lo thi acc
    | _ ->
        let ok =
          i < cnt_loc ||
          Context.type_satisfies_concept
            (try Term.down cnt t with Term_capture -> assert false)
            (TVars_sub.concept i acc.tvars)
            acc.c
        in
        add_sub ok i t acc




  let unify
      (t1:term)
      (t2:term)
      (acc:t)
      : unit =
    (** Unify the terms [t1] and [t2] using the substitution [tvars_sub] in the
        context [c] , i.e.  apply first the substitution [tvars_sub] to both
        terms and then add substitutions to [tvars_sub] so that when applied to
        both terms makes them identical.
     *)
    let nvars = TVars_sub.count acc.tvars
    in
    let rec uni (t1:term) (t2:term) (nb:int): unit =
      match t1,t2 with
        Variable i, _ when nb<=i && i<nb+nvars ->
          do_sub (i-nb) (Term.down nb t2) acc
      | _, Variable j when nb<=j && j<nb+nvars ->
          do_sub (j-nb) (Term.down nb t1) acc
      | Variable i, Variable j ->
          assert (i<nb||nb+nvars<=i);
          assert (j<nb||nb+nvars<=j);
          if i=j then
            ()
          else
            raise Not_found
      | Application(f1,args1), Application(f2,args2) ->
          if (Array.length args1) <> (Array.length args2) then
            raise Not_found;
          uni f1 f2 nb;
          Array.iteri (fun i t1 ->  uni t1 args2.(i) nb) args1
      | Lam (nb1,_,t1), Lam (nb2,_,t2) ->
          if nb1=nb2 then
            uni t1 t2 (nb+nb1)
          else
            raise Not_found
      | _ -> raise Not_found
    in
    (try
      uni t1 t2 0
    with Term_capture ->
      assert false);
    assert ((Term.sub t1 (TVars_sub.args  acc.tvars) nvars)
              = (Term.sub t2 (TVars_sub.args acc.tvars) nvars))



  let unify_sign_0
      (sig_req:Sign.t)
      (sig_act:Sign.t)
      (acc:t)
      : unit =
    let n         = (Sign.arity sig_req)
    and has_res   = (Sign.has_result sig_req) in
    if not (n = (Sign.arity sig_act) &&
            has_res = (Sign.has_result sig_act)) then
      raise Not_found;
    if has_res then
      unify (Sign.result sig_req) (Sign.result sig_act) acc;
    for i=0 to (Sign.arity sig_req)-1 do
      unify (Sign.arguments sig_req).(i) (Sign.arguments sig_act).(i) acc
    done



  let downgrade (tp:type_term) (nargs:int) (acc:t): Sign.t =
    let ntvs  = ntvars acc
    and nfgs  = Context.count_formal_generics acc.c
    and sign  = Sign.make_const tp
    in
    Class_table.downgrade_signature (ntvs+nfgs) sign nargs



  let to_dummy (sign:Sign.t) (acc:t): type_term =
    assert (Sign.has_result sign);
    let n = Sign.arity sign in
    assert (0 < n);
    let ntvs_all = ntvars acc + Context.count_formal_generics acc.c in
    let dum_idx  = ntvs_all + Class_table.dummy_index
    and tup_idx  = ntvs_all + Class_table.tuple_index
    and args     = Sign.arguments sign
    in
    let rec tuple (i:int) (tp:type_term): type_term =
      if i = 0 then
        tp
      else
        let i = i - 1 in
        let tp = Application(Variable tup_idx,[|args.(i);tp|]) in
        tuple (i-1) tp
    in
    let tup = tuple (n-1) args.(n-1) in
    Application(Variable dum_idx, [|tup;Sign.result sign|])




  let update_tv
      (sig_req:Sign.t)
      (sig_act:Sign.t)
      (itv:int)
      (acc:t)
      : unit =
    (** The required and actual signatures [sig_req,sig_act] are constant
        signatures, the type of the actual signature is the type variable
        [itv] which has already a substitution.

        Special case: The substitution of [itv] is callable (i.e. a dummy
        type) and the required type is either a function or a predicate and in
        case of a predicate the return type of [itv] is boolean:
        - unify the arguments
        - unify the return type for a function
        - update the substitution

        Otherwise: Do the usual unification *)
    assert (Sign.is_constant sig_req);
    assert (Sign.is_constant sig_act);
    let ntvs_all = ntvars acc + Context.count_formal_generics acc.c in
    let dum_idx  = ntvs_all + Class_table.dummy_index
    and pred_idx = ntvs_all + Class_table.predicate_index
    and fun_idx  = ntvs_all + Class_table.function_index
    and bool_tp  = Variable (ntvs_all + Class_table.boolean_index)
    and tp_req   = Sign.result sig_req
    and tp_act   = TVars_sub.get itv acc.tvars
    in
    match tp_req, tp_act with
      Application(Variable idx_req,args_req),
      Application(Variable idx_act,args_act)->
        if idx_req= pred_idx && idx_act = dum_idx then begin
          if args_act.(1) <> bool_tp then raise Not_found;
          unify args_req.(0) args_act.(0) acc;
          TVars_sub.update_sub
            itv
            (Application(Variable pred_idx, [|args_act.(0)|]))
            acc.tvars
        end else if idx_req = fun_idx && idx_act = dum_idx then begin
          unify args_req.(0) args_act.(0) acc;
          unify args_req.(1) args_act.(1) acc;
          TVars_sub.update_sub
            itv
            (Application(Variable fun_idx, [|args_act.(0);args_act.(1)|]))
            acc.tvars
        end else
          unify_sign_0 sig_req sig_act acc
    | _ ->
        unify_sign_0 sig_req sig_act acc




  let unify_sign
      (sig_req:Sign.t)
      (sig_act:Sign.t)
      (acc:t)
      : unit =
    (** Unify the signatures [sig_req] and [sig_act] by adding substitutions
        to [acc] *)
    let n         = (Sign.arity sig_req)
    and is_tv,itv =
      let ntvs = TVars_sub.count acc.tvars in
      if Sign.is_constant sig_act then
        match Sign.result sig_act with
          Variable i when i < ntvs ->
            true, i
        | _ ->
            false, -1
      else
        false, -1
    in
    if n > 0 && is_tv then
      if TVars_sub.has itv acc.tvars then
        let tp        = TVars_sub.get itv acc.tvars in
        let sig_act_1 = downgrade tp n acc
        in
        unify_sign_0 sig_req sig_act_1 acc
      else
        TVars_sub.add_sub itv (to_dummy sig_req acc) acc.tvars
    else if Sign.is_constant sig_req  && is_tv &&
      TVars_sub.has itv acc.tvars
    then
      update_tv sig_req sig_act itv acc
    else
      unify_sign_0 sig_req sig_act acc






  let make (e:type_term) (c:Context.t): t =
    (** New accumulator for an expression with the expected type [e] in the
        context with the type variables [tvars] *)
    {tlist = [];
     sign  = Sign.make_const e;
     tvars = (Context.type_variables c);
     c     = c}


  let add_global (cs:constraints) (acc:t): t =
    (** Add the constraints [cs] to the accumulator [acc] *)
    let n = Array.length cs
    and start = TVars_sub.count acc.tvars in
    {acc with
     sign  = Sign.up_from n start acc.sign;
     tvars = TVars_sub.add_global cs acc.tvars}


  let add_leaf
      (i:int)
      (tvs:TVars.t)
      (s:Sign.t)
      (acc:t): t =
    (** Add the term [i,tvs,s] of the context [c] to the accumulator [acc]
     *)
    assert (not (TVars.count_local tvs > 0 && TVars.count_global tvs > 0));
    let s =
      (* If [i] comes from a global environment, then it has no local type
         variables and space must be made for all type variables (locals and
         globals) of [acc.tvars].

         If [i] comes from a local environment then it has no global type
         variables. But the locals already in coincide with the locals of
         [acc.tvars]. Space has to be made for all type variables (globals
         and locals) of [acc.tvars] which are not yet in [tvs].
       *)
      let nglob = TVars_sub.count_global acc.tvars
      and nloc  = TVars_sub.count_local  acc.tvars - TVars.count_local tvs
      and start = TVars.count_local tvs
      in
      Sign.up nloc (Sign.up_from nglob start s)
    in
    let acc = add_global (TVars.constraints tvs) acc
    in
    unify_sign acc.sign s acc;
    {acc with tlist = (Variable i)::acc.tlist}




  let expect_function (nargs:int) (acc:t): unit =
    (** Convert the currently expected signature to a function signature
        with [nargs] arguments and add to the type variables [nargs] fresh
        type variables, one for each argument.
     *)
    acc.tvars <- TVars_sub.add_local nargs acc.tvars;
    let s = acc.sign in
    let s =
      if Sign.is_constant s then s
      else
        (* Convert the function signature into a constant signature with
           a function type as result type. This is always possible because
           we are strengthening the expectations.

           However the argument types of the function signature might be
           fresh type variables without concept. These cannot be used to
           form a function type and/or a tuple type (in case of more than
           one argument). In order to do this without problems we have to
           introduce the corresponding constraints for the fresh type
           variables.
         *)
        assert false (* nyi: conversion from a function signature
                        into a function object *)
    in
    acc.sign  <- Sign.to_function nargs s



  let expect_argument (i:int) (acc:t): unit =
    (** Expect the argument [i] as the next term.
     *)
    assert (i < (TVars_sub.count_local acc.tvars));
    acc.sign <- Sign.make_const (TVars_sub.get i acc.tvars)



  let complete_function (nargs:int) (acc:t): unit =
    (** Complete the current function with [nargs] arguments, i.e.

        a) Pop the [nargs] arguments and the function term off the term list
        and push the corresponding application to the term list.

        b) Remove the bottom [nargs] type variables from [acc.tvars] (all must
        have proper substitutions)

        Note: The signature is meaningless (it is just the expected signature
        of the last argument. If there are more arguments to come, then
        [expect_argument] will put a new expected signature into the
        accumulator.  *)
    let arglst = ref [] in
    for i = 1 to nargs do  (* pop arguments *)
      assert (acc.tlist <> []);
      let t = List.hd acc.tlist in
      acc.tlist <- List.tl acc.tlist;
      arglst := t :: !arglst;
    done;
    let f = List.hd acc.tlist in
    acc.tlist <- List.tl acc.tlist;
    acc.tlist <- (Application (f, Array.of_list !arglst)) :: acc.tlist;
    acc.tvars <- TVars_sub.remove_local nargs acc.tvars



  let expect_lambda (ntvs:int) (acc:t): unit =
    assert (Sign.is_constant acc.sign);
    assert (Sign.has_result acc.sign);
    acc.tvars <- TVars_sub.add_local ntvs acc.tvars;
    acc.sign  <- Sign.up ntvs acc.sign;
    let rt = Sign.result acc.sign in
    acc.sign <-
      try
        let ntvs = (ntvars acc) + (Context.count_formal_generics acc.c) in
        Sign.make_const (Class_table.result_type_of_compound rt ntvs)
      with Not_found ->
        assert false (* cannot happen *)



  let complete_lambda (ntvs:int) (names:int array) (acc:t): unit =
    assert (acc.tlist <> []);
    let nargs = Array.length names in
    assert (0 < nargs);
    acc.tvars <- TVars_sub.remove_local ntvs acc.tvars;
    let t = List.hd acc.tlist in
    acc.tlist <- List.tl acc.tlist;
    acc.tlist <- Lam (nargs, names, t) :: acc.tlist


  let check_type_variables (inf:info) (acc:t): unit =
    let ntvs_ctxt = Context.count_type_variables acc.c
    and ntvs_loc  = TVars_sub.count_local acc.tvars in
    assert (ntvs_ctxt = ntvs_loc);
    let ntvs_all = ntvars acc + Context.count_formal_generics acc.c in
    let dum_idx  = ntvs_all + Class_table.dummy_index
    in
    for i = 0 to Context.count_last_arguments acc.c - 1 do
      match Context.argument_type i acc.c with
        Variable j when j < ntvs_loc -> begin
          match TVars_sub.get j acc.tvars with
          Application(Variable idx,_) when idx = dum_idx ->
            error_info
              inf
              ("Cannot infer a complete type for " ^
               (ST.string (Context.argument_name i acc.c)))
          | _ -> ()
        end
      | _ -> ()
    done


  let result (acc:t): term * TVars_sub.t =
    (** Return the term and the calculated substitutions for the type
        variables *)
    assert (Mylist.is_singleton acc.tlist);
    List.hd acc.tlist, acc.tvars

end (* Accu *)







module Accus: sig

  type t
  exception Untypeable of (Sign.t*int) list

  val make:              type_term -> Context.t -> t
  val is_empty:          t -> bool
  val is_singleton:      t -> bool
  val ntvs_added:        t -> int
  val expected_arity:    t -> int
  val expected_signatures_string: t -> string
  val substitutions_string: t -> string
  val add_leaf:          (int*TVars.t*Sign.t) list -> t -> unit
  val expect_function:   int -> t -> unit
  val expect_argument:   int -> t -> unit
  val complete_function: int -> t -> unit
  val expect_lambda:     int -> t -> unit
  val complete_lambda:   int -> int array -> t -> unit
  val check_type_variables: info -> t -> unit
  val result:            t -> term * TVars_sub.t

end = struct

  type t = {mutable accus: Accu.t list;
            mutable ntvs_added: int;
            mutable arity:  int;
            c: Context.t}

  exception Untypeable of (Sign.t*int) list


  let make (exp: type_term) (c:Context.t): t =
    {accus           = [Accu.make exp c];
     ntvs_added      = 0;
     arity           = 0;
     c               = c}

  let is_empty     (accs:t): bool =   Mylist.is_empty     accs.accus

  let is_singleton (accs:t): bool =   Mylist.is_singleton accs.accus

  let ntvs_added (accs:t): int = accs.ntvs_added

  let expected_arity (accs:t): int = accs.arity

  let expected_signatures_string (accs:t): string =
    "{" ^
    (String.concat
      ","
      (List.map (fun acc -> Accu.signature_string acc) accs.accus)) ^
    "}"

  let substitutions_string (accs:t): string =
    "{" ^
    (String.concat
       ","
       (List.map (fun acc -> Accu.substitution_string acc) accs.accus)) ^
    "}"


  let expect_function (nargs:int) (accs:t): unit =
    accs.arity           <- nargs;
    accs.ntvs_added      <- nargs + accs.ntvs_added;
    List.iter (fun acc -> Accu.expect_function nargs acc) accs.accus


  let complete_function (nargs:int) (accs:t): unit =
    accs.ntvs_added <- accs.ntvs_added - nargs;
    List.iter
      (fun acc -> Accu.complete_function nargs acc)
      accs.accus



  let expect_argument (i:int) (accs:t): unit =
    (** Expect the next argument of the current application *)
    accs.arity <- 0;
    List.iter (fun acc -> Accu.expect_argument i acc) accs.accus


  let add_leaf
      (terms: (int*TVars.t*Sign.t) list)
      (accs:   t)
      : unit =
    (** Add the terms from the list [terms] of the context [c] to the
        accumulators [accs]
     *)
    let accus = accs.accus in
    accs.accus <-
      List.fold_left
        (fun lst acc ->
          List.fold_left
            (fun lst (i,tvs,s) ->
              try (Accu.add_leaf i tvs s acc) :: lst
              with Not_found -> lst)
            lst
          terms
        )
        []
        accus;
    if accs.accus = [] then
      raise (Untypeable
               (List.map
                  (fun acc -> Accu.signature acc, Accu.ntvars acc)
                  accus))

  let expect_lambda (ntvs:int) (accs:t): unit =
    List.iter (fun acc -> Accu.expect_lambda ntvs acc) accs.accus

  let complete_lambda (ntvs:int) (nms:int array) (accs:t): unit =
    List.iter (fun acc -> Accu.complete_lambda ntvs nms acc) accs.accus

  let check_type_variables (inf:info) (accs:t): unit =
    List.iter (fun acc -> Accu.check_type_variables inf acc) accs.accus

  let result (accs:t): term * TVars_sub.t =
    assert (is_singleton accs);
    Accu.result (List.hd accs.accus)
end (* Accus *)





let cannot_find (name:string) (nargs:int) (info:info) =
  let str = "Cannot find \"" ^ name
    ^ "\" with " ^ (string_of_int nargs) ^ " arguments"
  in
  error_info info str


let features (fn:feature_name) (nargs:int) (info:info) (c:Context.t)
    : (int * TVars.t * Sign.t) list =
  try
    Context.find_feature fn nargs c
  with Not_found ->
    cannot_find (feature_name_to_string fn) nargs info


let identifiers (name:int) (nargs:int) (info:info) (c:Context.t)
    : (int * TVars.t * Sign.t) list =
  try
    Context.find_identifier name nargs c
  with Not_found ->
    cannot_find (ST.string name) nargs info


let process_leaf
    (lst: (int*TVars.t*Sign.t) list)
    (e:expression)
    (c:Context.t)
    (info:info)
    (accs: Accus.t)
    : unit =
  try
    Accus.add_leaf lst accs
  with
    Accus.Untypeable exp_sign_lst ->
      let str = "The expression "
        ^ (string_of_expression e)
        ^ " does not satisfy any of the expected types in {"
        ^ (String.concat
             ","
             (List.map
                (fun (sign,ntvs) ->
                  printf "ntvs %d\n" ntvs;
                  let fgnames = Context.fgnames c
                  and ct      = Context.class_table c
                  in
                  Class_table.string_of_signature sign ntvs fgnames ct)
                exp_sign_lst))
        ^ "}"
      in
      error_info info str



let rec analyze_expression
    (ie:        info_expression)
    (expected:  type_term)
    (c:         Context.t)
    : term =
  (** Analyse the expression [ie] with the expected type [expected]
      in the context [context] and return the term.
   *)
  assert (not (Context.is_global c));
  let info, exp = ie.i, ie.v in

  let rec analyze
      (e:expression)
      (accs: Accus.t)
      : unit =
    let nargs = Accus.expected_arity accs
    in
    let feat (fn:feature_name) = features fn nargs info c
    and id   (name:int)        = identifiers name nargs info c
    and do_leaf (lst: (int*TVars.t*Sign.t) list): unit =
      process_leaf lst e c info accs
    in
    match e with
      Expproof (_,_,_)
    | Expquantified (_,_,Expproof (_,_,_)) ->
        error_info info "Proof not allowed here"
    | Identifier name     -> do_leaf (id name)
    | Expfalse            -> do_leaf (feat FNfalse)
    | Exptrue             -> do_leaf (feat FNtrue)
    | Expop op            -> do_leaf (feat (FNoperator op))
    | Binexp (op,e1,e2)   -> application (Expop op) [|e1; e2|] accs
    | Unexp  (op,e)       -> application (Expop op) [|e|] accs
    | Funapp (f,args)     ->
        let arg_array (e:expression): expression array =
          match e with
            Explist lst -> Array.of_list lst
          | _ -> [|e|]
        in
        application f (arg_array args) accs
    | Expparen e          -> analyze e accs
    | Taggedexp (label,e) -> analyze e accs
    | Expquantified (q,entlst,exp) ->
        quantified q entlst exp accs
    | Exppred (entlst,e) ->
        lambda entlst e accs
    | _ -> not_yet_implemented ie.i
          ("(others)Typing of expression " ^
           (string_of_expression e))
          (*assert false (* nyi: all alternatives *)*)

  and application
      (f:expression)
      (args: expression array) (* unreversed, i.e. as in the source code *)
      (accs: Accus.t)
      : unit =
    let nargs = Array.length args in
    assert (0 < nargs);
    Accus.expect_function nargs accs;
    analyze f accs;
    for i=0 to nargs-1 do
      Accus.expect_argument i accs;
      analyze args.(i) accs
    done;
    Accus.complete_function nargs accs

  and quantified
      (q:quantifier)
      (entlst:entities list withinfo)
      (e:expression)
      (accs: Accus.t)
      : unit =
    Accus.expect_function 1 accs;
    let qop = match q with Universal -> Allop | Existential -> Someop in
    process_leaf
      (features (FNoperator qop) 1 info c) e c info accs (*e is a dummy*);
    Accus.expect_argument 0 accs;
    lambda entlst e accs;
    Accus.complete_function 1 accs

  and lambda
      (entlst:entities list withinfo)
      (e:expression)
      (accs: Accus.t)
      : unit =
    let ntvs_gap = Accus.ntvs_added accs in
    Context.push_with_gap entlst None ntvs_gap c;
    let ntvs      = Context.count_local_type_variables c
    and fargnames = Context.local_fargnames c in
    Accus.expect_lambda (ntvs-ntvs_gap) accs;
    analyze e accs;
    Accus.check_type_variables entlst.i accs;
    Accus.complete_lambda (ntvs-ntvs_gap) fargnames accs;
    Context.pop c

  in

  let accs   = Accus.make expected c in
  analyze exp accs;
  assert (not (Accus.is_empty accs));

  if not (Accus.is_singleton accs) then
    error_info
      info
      ("The expression " ^ (string_of_expression exp) ^ " is ambiguous");

  Accus.check_type_variables ie.i accs;

  let term,tvars_sub = Accus.result accs in
  Context.update_type_variables tvars_sub c;
  term



and result_term
    (ie:  info_expression)
    (c:   Context.t)
    : term =
  (** Analyse the expression [ie] as the result expression of the
      context [context] and return the term.
   *)
  assert (not (Context.is_global c));
  analyze_expression ie (Context.result_type c) c


and boolean_term
    (ie: info_expression)
    (c:  Context.t)
    : term =
  (** Analyse the expression [ie] as a boolean expression in the
      context [context] and return the term.
   *)
  assert (not (Context.is_global c));
  analyze_expression ie (Context.boolean c) c
