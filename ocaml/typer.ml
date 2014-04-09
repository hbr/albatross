open Container
open Term
open Signature
open Support




module Accu: sig

  type t
  val signature:         t -> Sign.t
  val ntvars:            t -> int
  val make:              type_term -> TVars_sub.t -> t
  val add_term:          int ->  TVars.t -> Sign.t -> t -> t
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
      (acc:t): t =
    (** Add the term [i,tvs,s] to the accumulator [acc]
     *)
    (*Printf.printf "\tadd term: sign %s, expected %s\n"
      (Sign.to_string s)
      (Sign.to_string acc.sign);*)
    let acc = add_global (TVars.constraints tvs) acc
    in
    let s =
      let n = (TVars_sub.count_local acc.tvars) - TVars.count_local tvs
      in
      Sign.up n s
    in
    (*Printf.printf "\tunify %s with expected %s\n"
      (Sign.to_string s)
      (Sign.to_string acc.sign);*)
    Sign.unify s acc.sign acc.tvars;
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
    acc.sign <- Sign.make_const (TVars_sub.get i acc.tvars)
    (*acc.sign <- Sign.make_const (Variable i)*)



  let complete_function (nargs:int) (acc:t): unit =
    (** Complete the current function with [nargs] arguments, i.e.

        a) Pop the [nargs] arguments and the function term off the term list
        and push the corresponding application to the term list.

        b) Remove the bottom [nargs] type variables from [acc.tvars] (all must
        have proper substitutions)

        Note: The signature is meaningless (it is just the expected signature
        of the last argument. If there are more arguments to come, then
        [expect_argument] will put a new expected signature into the accumulator
     *)
    (*Printf.printf
      "Complete a function with %d arguments and %d terms on stack\n"
      nargs (List.length acc.tlist);*)
    let arglst = ref [] in
    let rec pop_args (n:int): unit =
      if n=0 then ()
      else begin
        assert (not (Mylist.is_empty acc.tlist));
        let t = List.hd acc.tlist in
        acc.tlist <- List.tl acc.tlist;
        arglst := t :: !arglst;
        pop_args (n-1)
      end
    in
    pop_args nargs;
    let f = List.hd acc.tlist in
    acc.tlist <- List.tl acc.tlist;
    acc.tlist <- (Application (f,Array.of_list !arglst)) :: acc.tlist;
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
  val add_leaf:        (int*TVars.t*Sign.t) list -> t -> unit
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
      (accs:   t)
      : unit =
    (** Add the terms from the list [terms] to the accumulators [accs]
     *)
    let accus = accs.accus in
    accs.accus <-
      List.fold_left
        (fun lst acc ->
          List.fold_left
            (fun lst (i,tvs,s) ->
              try (Accu.add_term i tvs s acc) :: lst
              with Not_found -> lst)
            lst
          terms
        )
        []
        accus;
    if Mylist.is_empty accs.accus then
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




let analyze_expression
    (ie:        info_expression)
    (expected:  type_term)
    (loc:       Local_context.t)
    : term =
  (** Analyse the expression [ie] with the expected type [expected]
      in the context [context] and return the term.
   *)
  assert (not (Local_context.is_global loc));
  let info, exp = ie.i, ie.v in

  let arg_array (e:expression): expression array =
    match e with
      Explist lst -> Array.of_list lst
    | _ -> [|e|]
  in

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
          (*Printf.printf "Try to find \"%s\" with %d arguments\n"
            (feature_name_to_string fn) nargs;*)
          Local_context.find_feature fn nargs loc
        with Not_found ->
          cannot_find (feature_name_to_string fn)
    and id_fun (name:int) =
      fun () ->
        try
          Local_context.find_identifier name nargs loc
        with Not_found ->
          cannot_find (ST.string name)
    and do_leaf (f: unit -> (int*TVars.t*Sign.t) list): unit =
      try
        let lst = f () in
        (*Printf.printf "found %s with {%s}\n"
          (string_of_expression e)
          (String.concat
             ","
             (List.map
                (fun (i,tvs,s) ->
                  let ct      = Local_context.ct loc
                  and ntvs    = TVars.count tvs
                  in
                  Class_table.string_of_signature s ntvs [||] ct)
                lst));*)
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
                      let fgnames = Local_context.fgnames loc
                      and ct      = Local_context.ct loc
                      in
                      Class_table.string_of_signature sign ntvs fgnames ct)
                    exp_sign_lst))
            ^ "}"
          in
          error_info info str
    in
      match e with
        Identifier name     -> do_leaf (id_fun name)
      | Expfalse            -> do_leaf (feat_fun FNfalse)
      | Exptrue             -> do_leaf (feat_fun FNtrue)
      | Expop op            -> do_leaf (feat_fun (FNoperator op))
      | Binexp (op,e1,e2)   -> application (Expop op) [|e1; e2|] accs
      | Unexp  (op,e)       -> application (Expop op) [|e|] accs
      | Funapp (f,args)     -> application f (arg_array args) accs
      | Expparen e          -> analyze e accs
      | Taggedexp (label,e) -> analyze e accs

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
    let rec do_args_from (i:int): unit =
      if i=nargs then ()
      else (Accus.expect_argument accs;
            analyze args.(i) accs;
            do_args_from (i+1))
    in
    do_args_from 0

  in

  let accs   = Accus.make expected (Local_context.type_variables loc) in
  analyze exp accs;
  assert (Accus.is_complete accs);
  assert (not (Accus.is_empty accs));

  if not (Accus.is_singleton accs) then
    error_info
      info
      ("The expression " ^ (string_of_expression exp) ^ " is ambiguous");

  let term,tvars_sub = Accus.result accs in
  Local_context.update_type_variables tvars_sub loc;
  (*Printf.printf "\tterm: %s\n"
    (Local_context.string_of_term term loc);*)
  term



let result_term
    (ie:    info_expression)
    (loc:   Local_context.t)
    : term =
  (** Analyse the expression [ie] as the result expression of the
      context [context] and return the term.
   *)
  assert (not (Local_context.is_global loc));
  analyze_expression ie (Local_context.result_type loc) loc


let boolean_term
    (ie:   info_expression)
    (loc:  Local_context.t)
    : term =
  (** Analyse the expression [ie] as a boolean expression in the
      context [context] and return the term.
   *)
  assert (not (Local_context.is_global loc));
  analyze_expression ie (Local_context.boolean loc) loc
