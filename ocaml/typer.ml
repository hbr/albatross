open Container
open Term
open Signature
open Support



let add_substitution
    (i:int)
    (t:term)
    (tvars_sub:TVars_sub.t)
    (c:Context.t): unit =
    (** Substitute the type variable [i] by the term [t] in the substitution
        [tvars_sub] using the context [c].
     *)
  (*Printf.printf "add substitution %d -> %s\n" i (Term.to_string t);*)
  let ok =
    begin
      i < TVars_sub.count_local tvars_sub
    ||
      let cpt = TVars_sub.concept i tvars_sub in
      (*Printf.printf "Does term %s satisfy the concept %s[%d]?\n"
        (Term.to_string t)
        (Term.to_string cpt) i;*)
      let cnt = TVars_sub.count tvars_sub in
      match t with
        Variable i when i < cnt ->
          assert (TVars_sub.count_local tvars_sub <= i);
          let cpt_t = TVars_sub.concept i tvars_sub in
          Context.concept_satisfies_concept cpt_t cpt c
      | _ ->
          let t =
            try Term.down cnt t
            with Term_capture -> assert false (* should not happen! *)
          in
          Context.type_satisfies_concept t cpt c
    end in
  if ok then
    TVars_sub.add_substitution i t tvars_sub
  else
    raise Not_found


let unify
    (t1:term)
    (t2:term)
    (tvars_sub: TVars_sub.t)
    (c:Context.t): unit =
  (** Unify the terms [t1] and [t2] using the substitution [tvars_sub] in the
      context [c] , i.e.  apply first the substitution [tvars_sub] to both
      terms and then add substitutions to [tvars_sub] so that when applied to
      both terms makes them identical.
   *)
  let nvars = TVars_sub.count tvars_sub
  in
  let do_sub (i:int) (t:term) (nb:int): unit =
    (** Substitute the variable [i] by the term [t] in an environment with
        [nb] bound variables.
     *)
    assert (nb<=i); assert (i<nb+nvars);
    match t with
      Variable j when nb<=j && j<nb+nvars ->
        if i=j then ()
        else
          let lo,hi = if i<=j then i,j else j,i in
          add_substitution (lo-nb) (Variable (hi-nb)) tvars_sub c
    | _ ->
        let i,t =
          try i-nb, Term.down nb t
          with Term_capture -> raise Not_found
        in
        add_substitution i t tvars_sub c
  in
  let rec uni (t1:term) (t2:term) (nb:int): unit =
    match t1,t2 with
      Variable i, _ when nb<=i && i<nb+nvars ->
        do_sub i t2 nb
    | _, Variable j when nb<=j && j<nb+nvars ->
        do_sub j t1 nb
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
  uni t1 t2 0;
  assert ((Term.sub t1 (TVars_sub.args  tvars_sub) nvars)
            = (Term.sub t2 (TVars_sub.args tvars_sub) nvars))






let unify_sign
    (s1:Sign.t)
    (s2:Sign.t)
    (tvars_sub: TVars_sub.t)
    (c:Context.t)
    : unit =
  (** Unify the signatures [s1] and [s2] by adding substitutions to
      [tvars_sub] within the context [c] *)
  (*Printf.printf "unify signatures %s, %s\n" (Sign.to_string s1)
    (Sign.to_string s2);*)
  let n,has_res = (Sign.arity s1), (Sign.has_result s1) in
  if not (n = (Sign.arity s2) && has_res = (Sign.has_result s2)) then
    raise Not_found;
  if has_res then
    unify (Sign.result s1) (Sign.result s2) tvars_sub c;
  for i=0 to (Sign.arity s1)-1 do
    unify (Sign.arguments s1).(i) (Sign.arguments s2).(i) tvars_sub c
  done




module Accu: sig

  type t
  val signature:         t -> Sign.t
  val ntvars:            t -> int
  val make:              type_term -> TVars_sub.t -> t
  val add_term:          int ->  TVars.t -> Sign.t -> Context.t ->  t -> t
  val expect_function:   int -> t -> unit
  val expect_argument:   int -> t -> unit
  val complete_function: int -> t -> unit
  val result:            t -> term * TVars_sub.t

end = struct

  type t = {mutable tlist: term list;
            mutable sign:  Sign.t;  (* expected *)
            mutable tvars: TVars_sub.t}

  let signature (acc:t): Sign.t = acc.sign

  let ntvars (acc:t): int = TVars_sub.count acc.tvars

  let make (e:type_term) (tvars:TVars_sub.t): t =
    (** New accumulator for an expression with the expected type [e] in the
        context with the type variables [tvars] *)
    {tlist = [];
     sign  = Sign.make_const e;
     tvars = tvars}


  let add_global (cs:constraints) (acc:t): t =
    (** Add the constraints [cs] to the accumulator [acc]
     *)
    let n = Array.length cs
    and start = TVars_sub.count acc.tvars in
    (*Printf.printf "\tadd %d globals above %d\n" n start;*)
    {acc with
     sign  = Sign.up_from n start acc.sign;
     tvars = TVars_sub.add_global cs acc.tvars}




  let add_term
      (i:int)
      (tvs:TVars.t)
      (s:Sign.t)
      (c:Context.t)
      (acc:t): t =
    (** Add the term [i,tvs,s] of the context [c] to the accumulator [acc]
     *)
    assert (not (TVars.count_local tvs > 0 && TVars.count_global tvs > 0));
    (*Printf.printf "add_term %d sig %s\n" i (Sign.to_string s);*)
    let s =
      (* If [i] comes from a global environment, then it has no local type
         variables and space must be made for all type variables (locals and
         globals) of [acc.tvars].

         If [i] comes from a local environment then it has no global type
         variables. But the locals already in conincide with the locals of
         [acc.tvars]. Space has to be made for all type variables (globals
         and locals) of [acc.tvars] which are not yet in [tvs].
       *)
      let n = (TVars_sub.count acc.tvars) - TVars.count_local tvs
      in
      Sign.up n s
    in
    let acc = add_global (TVars.constraints tvs) acc
    in
    unify_sign s acc.sign acc.tvars c;
    {acc with tlist = (Variable i)::acc.tlist}




  let expect_function (nargs:int) (acc:t): unit =
    (** Convert the currently expected signature into a function signature
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
    (*Printf.printf "expect argument %d:%s\n"
      i
      (Term.to_string (TVars_sub.get i acc.tvars));*)
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
        accumulator.
     *)
    (*Printf.printf
      "Complete a function with %d arguments and %d terms on stack\n"
      nargs (List.length acc.tlist);*)
    let arglst = ref [] in
    for i = 1 to nargs do  (* pop arguments *)
      assert (not (Mylist.is_empty acc.tlist));
      let t = List.hd acc.tlist in
      acc.tlist <- List.tl acc.tlist;
      arglst := t :: !arglst;
    done;
    let f = List.hd acc.tlist in
    acc.tlist <- List.tl acc.tlist;
    acc.tlist <- (Application (f, Array.of_list !arglst)) :: acc.tlist;
    acc.tvars <- TVars_sub.remove_local nargs acc.tvars


  let result (acc:t): term * TVars_sub.t =
    (** Return the term and the calculated substitutions of the type variables
     *)
    assert (Mylist.is_singleton acc.tlist);
    List.hd acc.tlist, acc.tvars

end (* Accu *)







module Accus: sig

  type t
  exception Untypeable of (Sign.t*int) list

  val make:            type_term -> TVars_sub.t -> t
  val is_empty:        t -> bool
  val is_singleton:    t -> bool
  val is_complete:     t -> bool
  val expected_arity:  t -> int
  val add_leaf:        (int*TVars.t*Sign.t) list -> Context.t -> t -> unit
  val expect_function: int -> t -> unit
  val expect_argument: t -> unit
  val result:          t -> term * TVars_sub.t

end = struct

  type t = {mutable accus: Accu.t list;
            mutable nterms_expected: int;
            mutable nterms: int;
            mutable arity:  int;
            mutable stack:  (int*int) list}

  exception Untypeable of (Sign.t*int) list

  let nterms_missing (accs:t): int =
    accs.nterms_expected - accs.nterms

  let is_function_complete (accs:t): bool =
    (nterms_missing accs) = 0

  let is_stack_empty (accs:t): bool = Mylist.is_empty accs.stack

  let make (exp: type_term) (tvars:TVars_sub.t): t =
    {accus           = [Accu.make exp tvars];
     nterms_expected = 1;
     nterms          = 0;
     arity           = 0;
     stack           = []}

  let is_empty     (accs:t): bool =   Mylist.is_empty     accs.accus

  let is_singleton (accs:t): bool =   Mylist.is_singleton accs.accus

  let is_complete  (accs:t): bool =
    (is_function_complete accs) && (is_stack_empty accs)

  let expected_arity (accs:t): int = accs.arity

  let expect_function (nargs:int) (accs:t): unit =
    accs.stack <- (accs.nterms_expected,accs.nterms)::accs.stack;
    accs.nterms_expected <- nargs + 1;
    accs.nterms          <- 0;
    accs.arity           <- nargs;
    List.iter (fun acc -> Accu.expect_function nargs acc) accs.accus


  let expect_argument (accs:t): unit =
    (** Expect the next argument of the current application *)
    assert ((nterms_missing accs) > 0);
    assert (accs.nterms > 0);
    accs.arity <- 0;
    List.iter (fun acc -> Accu.expect_argument (accs.nterms-1) acc) accs.accus



  let rec pop (accs:t): unit =
    (** Pop pushed function application as long as possible *)
    if (is_function_complete accs) && not (is_stack_empty accs) then
      begin
        assert (accs.nterms > 1);
        List.iter
          (fun acc -> Accu.complete_function (accs.nterms-1) acc)
          accs.accus;
        let ne,n = List.hd accs.stack in
        accs.stack <- List.tl accs.stack;
        accs.nterms_expected <- ne;
        accs.nterms <- n+1;
        pop accs
      end
    else ()


  let add_leaf
      (terms: (int*TVars.t*Sign.t) list)
      (c:Context.t)
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
              try (Accu.add_term i tvs s c acc) :: lst
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
                  accus));
    accs.nterms <- accs.nterms + 1;
    pop accs

  let result (accs:t): term * TVars_sub.t =
    assert (is_complete accs);
    assert (is_singleton accs);
    Accu.result (List.hd accs.accus)
end (* Accus *)




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
    let cannot_find (name:string) =
      let str = "Cannot find \"" ^ name
        ^ "\" with " ^ (string_of_int nargs) ^ " arguments"
      in
      error_info info str
    in
    let feat_fun (fn:feature_name) =
      fun () ->
        try
          Context.find_feature fn nargs c
        with Not_found ->
          cannot_find (feature_name_to_string fn)
    and id_fun (name:int) =
      fun () ->
        try
          Context.find_identifier name nargs c
        with Not_found ->
          cannot_find (ST.string name)
    and do_leaf (f: unit -> (int*TVars.t*Sign.t) list): unit =
      try
        let lst = f () in
        Accus.add_leaf lst c accs
      with
        Accus.Untypeable exp_sign_lst ->
          let str = "The expression "
            ^ (string_of_expression e)
            ^ " does not satisfy any of the expected types in {"
            ^ (String.concat
                 ","
                 (List.map
                    (fun (sign,ntvs) ->
                      let fgnames = Context.fgnames c
                      and ct      = Context.class_table c
                      in
                      Class_table.string_of_signature sign ntvs fgnames ct)
                    exp_sign_lst))
            ^ "}"
          in
          error_info info str
    in
    match e with
      Expproof (_,_,_)
    | Expquantified (_,_,Expproof (_,_,_)) ->
        error_info info "Proof not allowed here"
    | Identifier name     -> do_leaf (id_fun name)
    | Expfalse            -> do_leaf (feat_fun FNfalse)
    | Exptrue             -> do_leaf (feat_fun FNtrue)
    | Expop op            -> do_leaf (feat_fun (FNoperator op))
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
        Context.push entlst None c;
        let t0 = boolean_term (withinfo entlst.i exp) c in
        let t  =
          match q with
            Universal -> Context.all_quantified_outer t0 c
          | Existential -> assert false (* nyi: *)
        in
        Printf.printf "inner term %s\n" (Context.string_of_term t0 c);
        Context.pop c;
        Printf.printf "outer term %s\n" (Context.string_of_term t  c);
        not_yet_implemented ie.i "typing of quantified expressions";

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
      Accus.expect_argument accs;
      analyze args.(i) accs
    done

  in

  let accs   = Accus.make expected (Context.type_variables c) in
  analyze exp accs;
  assert (Accus.is_complete accs);
  assert (not (Accus.is_empty accs));

  if not (Accus.is_singleton accs) then
    error_info
      info
      ("The expression " ^ (string_of_expression exp) ^ " is ambiguous");

  let term,tvars_sub = Accus.result accs in
  Context.update_type_variables tvars_sub c;
  (*Printf.printf "\tterm: %s\n"
    (Context.string_of_term term c);*)
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
