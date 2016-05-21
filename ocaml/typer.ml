(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term
open Signature
open Support
open Printf


module Accus: sig

  type t
  exception Untypeable of Term_builder.t list

  val make:              Term_builder.t -> Context.t -> t
  val is_empty:          t -> bool
  val is_singleton:      t -> bool
  val is_tracing:        t -> bool
  val count:             t -> int
  val ntvs_added:        t -> int
  val first:             t -> Term_builder.t
  val expected_arity:    t -> int
  val expect_boolean:    t -> unit
  val expect_type:       term -> t -> unit
  val expect_boolean_expression:    t -> unit
  val expect_new_untyped:t -> unit
  val push_expected:     t -> unit
  val get_expected:      int -> t -> unit
  val drop_expected:     t -> unit
  val expect_if:         t -> unit
  val complete_if:       bool -> t -> unit
  val add_leaf:          (int*Tvars.t*Sign.t) list -> t -> unit
  val expect_function:   int -> t -> unit
  val expect_argument:   t -> unit
  val complete_function: t -> unit
  val expect_lambda:     bool -> Context.t -> t -> unit
  val complete_lambda:   int -> int array -> int -> bool -> t -> unit
  val expect_quantified: Context.t -> t -> unit
  val complete_quantified: bool -> t -> unit
  val expect_inductive:  Context.t -> t -> unit
  val complete_inductive:info -> int -> t -> unit
  val expect_case:       Context.t -> t -> unit
  val complete_case:     t -> unit
  val expect_inspect:    t -> unit
  val complete_inspect:  int ->  t -> unit
  val expect_as:         t -> unit
  val complete_as:       t -> unit
  val check_uniqueness:  info -> expression -> t -> unit
  val iter: (Term_builder.t->unit) -> t -> unit
end = struct

  type t = {mutable accus: Term_builder.t list;
            trace: bool;
            mutable c: Context.t}

  exception Untypeable of Term_builder.t list


  let make (tb:Term_builder.t) (c:Context.t): t =
    {accus           = [tb];
     trace           = (5 <= Context.verbosity c);
     c               = c}


  let is_empty     (accs:t): bool =   Mylist.is_empty     accs.accus

  let is_singleton (accs:t): bool =   Mylist.is_singleton accs.accus

  let is_unique (accs:t): bool =
    match accs.accus with
      [] -> assert false
    | [_] -> true
    | hd::tl ->
        let res = Term_builder.head_term hd in
        List.for_all (fun tb -> res = Term_builder.head_term tb) tl

  let is_tracing (accs:t): bool = accs.trace

  let count (accs:t): int = List.length accs.accus

  let first (accs:t): Term_builder.t =
    assert (accs.accus <> []);
    List.hd accs.accus


  let ntvs_added (accs:t): int =
    Term_builder.count_local_added (first accs)

  let expected_arity (accs:t): int =
    Term_builder.expected_arity (first accs)


  let trace_accus (accs:t): unit =
    let accus = accs.accus in
    List.iteri
      (fun i acc ->
        let t = Term_builder.last_term acc in
        printf "    %d: \"%s\"  \"%s\" %s%s %s\n"
          i
          (Term_builder.string_of_last_term acc) (Term.to_string t)
          (Term_builder.string_of_tvs acc)
          (Term_builder.string_of_substitutions acc)
          (Term_builder.string_of_last_signature acc))
      accus


  let expect_boolean_expression (accs:t): unit =
    List.iter
      (fun acc -> Term_builder.expect_boolean_expression acc)
      accs.accus


  let expect_new_untyped (accs:t): unit =
    List.iter Term_builder.expect_new_untyped accs.accus



  let expect_function (nargs:int) (accs:t): unit =
    List.iter (fun acc -> Term_builder.expect_function nargs (-1) acc) accs.accus



  let complete_function (accs:t): unit =
    List.iter
      Term_builder.complete_function
      accs.accus;
    if accs.trace then begin
      printf "  complete function\n";
      trace_accus accs
    end



  let expect_argument(accs:t): unit =
    (** Expect the next argument of the current application *)
    List.iter Term_builder.expect_argument accs.accus


  let add_leaf
      (terms: (int*Tvars.t*Sign.t) list)
      (accs:   t)
      : unit =
    (** Add the terms from the list [terms] of the context [c] to the
        accumulators [accs]
     *)
    assert (terms <> []);
    let accus = accs.accus in
    let rec add_lf terms acc lst =
      let add i tvs s acc lst =
        try Term_builder.add_leaf i tvs s acc; acc::lst
        with Not_found -> lst in
      match terms with
        [] -> assert false (* cannot happen *)
      | [i,tvs,s] ->
          add i tvs s acc lst
      | (i,tvs,s)::terms ->
          let lst = add i tvs s (Term_builder.clone acc) lst in
          add_lf terms acc lst
    in
    accs.accus <-
      List.fold_left
        (fun lst acc -> add_lf terms acc lst)
        []
        accus;
    if accs.trace && 1 < List.length terms then begin
      let ct = Context.class_table accs.c in
      printf "multiple leafs\n";
      List.iter
        (fun (i,tvs,sign) ->
          printf "  %d %s %s\n" i
            (Context.string_of_term0 (Variable i) true false 0 accs.c)
            (Class_table.string_of_complete_signature sign tvs ct))
        terms
    end;
    if accs.trace then begin
      printf "  add_leaf\n";
      trace_accus accs
    end;
    if accs.accus = [] then
      raise (Untypeable accus)



  let iter (f:Term_builder.t->unit) (accs:t): unit =
    let accus = accs.accus in
    accs.accus <-
      List.fold_left
        (fun lst acc ->
          try
            f acc;
            acc::lst
          with Not_found ->
            lst)
        []
        accs.accus;
    if accs.accus = [] then
      raise (Untypeable accus)



  let iter_save (f:Term_builder.t->unit) (accs:t): unit =
    try
      iter f accs
    with Untypeable _ ->
      assert false


  let map_accus (f:Term_builder.t->Term_builder.t) (accs:t): unit =
    let lst =
      List.fold_left
        (fun lst acc ->
          try
            (f acc)::lst
          with Not_found ->
            lst)
        []
        accs.accus
    in
    if lst = [] then
      raise (Untypeable accs.accus);
    accs.accus <- lst


  let expect_boolean (accs:t): unit =
    let accus = accs.accus in
    accs.accus <-
      List.fold_left
        (fun lst acc ->
          try
            Term_builder.expect_boolean acc;
            acc :: lst
          with Not_found ->
            lst)
        []
        accs.accus;
    if accs.accus = [] then
      raise (Untypeable accus)



  let expect_type (tp:type_term) (accs:t): unit =
    iter (fun acc -> Term_builder.expect_type tp acc) accs


  let push_expected (accs:t): unit =
    iter_save Term_builder.push_expected accs

  let get_expected (i:int) (accs:t): unit =
    iter_save (fun acc -> Term_builder.get_expected i acc) accs

  let drop_expected (accs:t): unit =
    iter_save Term_builder.drop_expected accs


  let expect_if (accs:t): unit =
    iter_save Term_builder.expect_if accs

  let complete_if (has_else:bool) (accs:t): unit =
    iter_save (fun acc -> Term_builder.complete_if has_else acc) accs


  let expect_lambda (is_pred:bool) (c:Context.t) (accs:t): unit =
    accs.c <- c;
    iter_save
      (fun acc -> Term_builder.expect_lambda is_pred c acc)
      accs


  let complete_lambda (n:int) (nms:int array) (npres:int) (is_pred:bool) (accs:t)
      : unit =
    iter
      (fun acc -> Term_builder.complete_lambda n nms npres is_pred acc) accs;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete lambda\n";
      trace_accus accs
    end




  let expect_quantified (c:Context.t) (accs:t): unit =
    accs.c <- c;
    iter
      (fun acc -> Term_builder.expect_quantified c acc)
      accs


  let complete_quantified (is_all:bool) (accs:t)
      : unit =
    iter
      (fun acc -> Term_builder.complete_quantified is_all acc) accs;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete quantified\n";
      trace_accus accs
    end



  let expect_inductive (c:Context.t) (accs:t): unit =
    accs.c <- c;
    iter
      (fun acc -> Term_builder.expect_inductive c acc)
      accs



  let complete_inductive (info:info) (nrules:int) (accs:t): unit =
    iter_save
      (fun tb -> Term_builder.complete_inductive info nrules tb)
      accs;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete inductive\n";
      trace_accus accs
    end


  let expect_case (c:Context.t) (accs:t): unit =
    accs.c <- c;
    iter_save (fun acc -> Term_builder.expect_case c acc) accs


  let complete_case (accs:t): unit =
    iter_save Term_builder.complete_case accs;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete case\n";
      trace_accus accs
    end


  let expect_inspect (accs:t): unit =
    iter_save Term_builder.expect_inspect accs

  let complete_inspect (ncases:int) (accs:t): unit =
    iter_save (fun acc -> Term_builder.complete_inspect ncases acc) accs;
    if accs.trace then begin
      printf "  complete inspect\n";
      trace_accus accs
    end


  let expect_as (accs:t): unit =
    iter_save Term_builder.expect_as accs


  let complete_as (accs:t): unit =
    iter_save Term_builder.complete_as accs;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete as\n";
      trace_accus accs
    end


  let get_diff (t1:term) (t2:term) (accs:t): string * string =
    let nargs = Context.count_variables accs.c
    and ft    = Context.feature_table accs.c
    in
    let vars1 = List.rev (Term.used_variables_from t1 nargs true)
    and vars2 = List.rev (Term.used_variables_from t2 nargs true) in
    let lst   = Mylist.combine vars1 vars2 in
    let i,j =
      try List.find (fun (i,j) -> i<>j) lst
      with Not_found -> assert false (* cannot happen *) in
    let str1 = Feature_table.string_of_signature (i-nargs) ft
    and str2 = Feature_table.string_of_signature (j-nargs) ft in
    str1, str2


  let check_uniqueness (inf:info) (e:expression) (accs:t): unit =
    match accs.accus with
      [] -> assert false
    | hd::tl ->
        let t1 = Term_builder.head_term hd in
        try
          let acc = List.find (fun acc -> Term_builder.head_term acc <> t1) tl in
          let t2 = Term_builder.head_term acc
          and estr = string_of_expression e in
          printf "ambiguous expression %s (%d)\n" (string_of_expression e)
            (List.length accs.accus);
          printf "    t1 %s\n" (Term.to_string t1);
          printf "    t2 %s\n" (Term.to_string t2);
          let str1, str2 = get_diff t1 t2 accs in
          error_info inf
            ("The expression " ^ estr ^ " is ambiguous\n    " ^
             str1 ^ "\n    " ^ str2)
        with Not_found ->
          ()
end (* Accus *)




let unfold_inspect (info:info) (t:term) (c:Context.t): term =
  let ft    = Context.feature_table c
  and nvars = Context.count_variables c
  and ntvs  = Context.ntvs c in
  let rec unfold t nb =
    let unfold_args args nb = Array.map (fun a -> unfold a nb) args
    and unfold_list lst  = List.map  (fun a -> unfold a nb) lst
    in
    match t with
      Variable i ->
        t
    | VAppl (i,args,ags) ->
        VAppl (i, unfold_args args nb,ags)
    | Application (f,args,pr) ->
        let f    = unfold f nb
        and args = unfold_args args nb in
        Application(f,args,pr)
    | Lam (n,nms,pres,t,pr,tp) ->
        let pres = unfold_list pres
        and t    = unfold t (1+nb) in
        Lam(n,nms,pres,t,pr,tp)
    | QExp (n,tps,fgs,t,is_all) ->
        QExp (n, tps, fgs, unfold t (n+nb), is_all)
    | Flow (Inspect,args) ->
        let args = unfold_args args nb in
        let args = Feature_table.inspect_unfolded info args (nb+nvars) ntvs ft in
        Flow(Inspect,args)
    | Flow (ctrl,args) ->
        Flow (ctrl, unfold_args args nb)
    | Indset (nme,tp,rs) ->
        Indset (nme,tp, unfold_args rs (1+nb))
  in
  unfold t 0



let cannot_find (name:string) (nargs:int) (info:info) =
  let str = "Cannot find \"" ^ name
    ^ "\" with " ^ (string_of_int nargs) ^ " arguments"
  in
  error_info info str


let features (fn:feature_name) (nargs:int) (info:info) (c:Context.t)
    : (int * Tvars.t * Sign.t) list =
  try
    Context.find_feature fn nargs c
  with Not_found ->
    cannot_find (feature_name_to_string fn) nargs info


let identifiers (name:int) (nargs:int) (info:info) (c:Context.t)
    : (int * Tvars.t * Sign.t) list =
  try
    Context.find_identifier name nargs c
  with Not_found ->
    cannot_find (ST.string name) nargs info


let string_of_signature (tvs:Tvars.t) (s:Sign.t) (c:Context.t): string =
  let ct = Context.class_table c  in
  (Class_table.string_of_complete_signature s tvs ct)


let string_of_signatures (lst:(int*Tvars.t*Sign.t) list) (c:Context.t): string =
  "{" ^
  (String.concat
     ","
     (List.map (fun (_,tvs,s) ->
       string_of_signature tvs s c) lst)) ^
  "}"



let process_leaf
    (lst: (int*Tvars.t*Sign.t) list)
    (c:Context.t)
    (info:info)
    (accs: Accus.t)
    : unit =
  assert (lst <> []);
  try
    Accus.add_leaf lst accs
  with
    Accus.Untypeable acc_lst ->
      let ct = Context.class_table c in
      let i,_,_ = List.hd lst in
      let nargs = Term_builder.expected_arity (List.hd acc_lst) in
      let str = "Type error \"" ^
        (Context.string_of_term0 (Variable i) true false 0 c) ^
        "\"\n  Actual type(s):\n\t"
      and actuals = String.concat "\n\t"
          (List.map
             (fun (_,tvs,s) ->
               Class_table.string_of_reduced_complete_signature s tvs ct)
             lst)
      and reqstr =
        if nargs = 0 then
          "\n  Required type(s):\n\t"
        else
          "\n  Expecting function with " ^ (string_of_int nargs) ^
          " arguments with the required return type(s):\n\t"
      and reqs = String.concat "\n\t"
          (List.map Term_builder.string_of_reduced_required_type acc_lst)
      in
      error_info info (str ^ actuals ^ reqstr ^ reqs)



let is_constant (nme:int) (c:Context.t): bool =
  let nvars = Context.count_variables c in
  try
    let lst   = Context.find_identifier nme 0 c in
    let lst = List.filter
        (fun (idx,_,_) -> nvars <= idx ) lst in
    lst <> []
  with Not_found ->
    false


let case_variables
    (info:info) (e:expression) (dups:bool) (c:Context.t)
    : expression * int array =
  let rec vars (e:expression) (nanon:int) (lst:int list)
      : expression * int * int list =
    let fvars f nanon lst =
      match f with
        Identifier nme -> f,nanon,lst
      | _ -> vars f nanon lst
    in
    match e with
      Expnumber _ | Exptrue | Expfalse | Expop _ ->
        e, nanon, lst
    | Identifier nme | Typedexp(Identifier nme,_)->
        let lst =
          if is_constant nme c then
            lst
          else if dups && List.mem nme lst then
            lst
          else
            nme :: lst in
        e,nanon,lst
    | Expanon ->
        let nme = ST.symbol ("$" ^ (string_of_int nanon)) in
        Identifier nme, 1+nanon, nme :: lst
    | Typedexp (Expanon,tp) ->
        let nme = ST.symbol ("$" ^ (string_of_int nanon)) in
        Typedexp(Identifier nme,tp), 1+nanon, nme :: lst
    | Unexp (op,exp) ->
        let e,nanon,lst = vars exp nanon lst in
        Unexp(op,e), nanon, lst
    | Binexp (op,e1,e2) ->
        let e1,nanon,lst = vars e1 nanon lst in
        let e2,nanon,lst = vars e2 nanon lst in
        Binexp(op,e1,e2), nanon, lst
    | Funapp(f,args) ->
        let args = expression_list args in
        let f,nanon,lst = fvars f nanon lst in
        let arglst,nanon,lst =
          List.fold_left
            (fun (arglst,nanon,lst) e ->
              let e,nanon,lst = vars e nanon lst in
              e::arglst, nanon, lst)
            ([],nanon,lst)
            args in
        Funapp(f,expression_of_list (List.rev arglst)), nanon, lst
    | Expdot (tgt,f) ->
        let tgt, nanon,lst = vars tgt nanon lst in
        let f, nanon, lst  = fvars f nanon lst in
        Expdot(tgt,f), nanon, lst
    | Tupleexp (e1,e2) ->
        let e1,nanon,lst = vars e1 nanon lst in
        let e2,nanon,lst = vars e2 nanon lst in
        Tupleexp (e1,e2), nanon, lst
    | Expparen e ->
        vars e nanon lst
    | _ ->
        printf "case_variables %s\n" (string_of_expression e);
        raise Not_found
  in
  try
    let e, nanon, lst = vars e 0 [] in
    if (not dups) && Mylist.has_duplicates lst then
      error_info info ("Duplicate variable in pattern \"" ^
                       (string_of_expression e) ^ "\"");
    let nms = Array.of_list (List.rev lst) in
    e, nms
  with Not_found ->
    error_info info ("Cannot extract variables from pattern \"" ^
                     (string_of_expression e) ^ "\"")




let validate_inductive_set (info:info) (rs:term array) (c:Context.t): unit =
  let nargs = Context.count_last_arguments c
  and nvars = Context.count_variables c in
  assert (nargs = 1); (* nyi: multiple inductive sets *)
  let imp_id = nvars + Feature_table.implication_index in
  let ind_set_name () = ST.string (Context.variable_name 0 c)
  in
  let check_rule (r:term): unit =
    let n,(nms,tps),ps_rev,tgt = Term.split_rule r imp_id in
    let check_element (t:term): bool =
      let check_inner t =
        try ignore(Term.down_from nargs n t)
        with Term_capture ->
          error_info info ("Variable \"" ^ (ind_set_name ()) ^
                           "\" only at the top allowed in rule\n  \"" ^
                           (Context.string_long_of_term r c) ^ "\"")
      in
      match t with
        Application(Variable i,args,pr)
        when n <= i && i < n+nargs -> (* [i] represents the inductive set *)
          Array.iter check_inner args;
          true
      | _ ->
          check_inner t;
          false
    in
    List.iter (fun t -> ignore(check_element t)) ps_rev;
    if not (check_element tgt) then
      error_info info ("The target must contain \"" ^ (ind_set_name ()) ^
                       "\" at the top in rule \n  \"" ^
                       (Context.string_of_term r c) ^ "\"")
  in
  Array.iter check_rule rs





let validate_term (info:info) (t:term) (c:Context.t): unit =
  (* Check that all pattern in inspect expressions have only constructors
     and variables *)
  let rec validate t c =
    let val_args args c = Array.iter (fun arg -> validate arg c) args in
    let val_lst  lst  c = List.iter  (fun t   -> validate t c)   lst  in
    match t with
      Variable i -> ()
    | VAppl(_,args,_) -> val_args args c
    | Application(f,args,pr) ->
        validate f c; val_args args c
    | Lam (n,nms,pres,t,pr,tp) ->
        let c = Context.push_untyped [|ST.symbol "$0"|] c in
        val_lst pres c; validate t c
    | QExp (n,(nms,tps),_,t,_) ->
        let c = Context.push_untyped nms c in
        validate t c
    |  Flow (flow,args) ->
        let len = Array.length args in
        let check_pattern pat c =
          if Context.is_case_match_expression pat c then
            ()
          else
            error_info info
              ("The term \"" ^ (Context.string_of_term pat c) ^
               "\" is not a valid pattern")
        in
        begin
          match flow with
            Ifexp ->
              val_args args c
          | Inspect ->
              assert (3 <= len);
              assert (len mod 2 = 1);
              let ncases = len / 2 in
              validate args.(0) c;
              for i = 0 to ncases - 1 do
                let n,tps,pat,res = Term.case_split args.(2*i+1) args.(2*i+2) in
                let c = Context.push_typed tps empty_formals c in
                validate res c;
                check_pattern pat c
              done
          | Asexp ->
              assert (len = 2);
              validate args.(0) c;
              let n,tps,pat = Term.pattern_split args.(1) in
              let c = Context.push_typed tps empty_formals c in
              check_pattern pat c
        end
    | Indset (nme,tp,rs) ->
        let c = Context.push_typed ([|nme|],[|tp|]) empty_formals c in
        validate_inductive_set info rs c;
        val_args rs c
  in
  validate t c


let validate_visibility (info:info) (t:term) (c:Context.t): unit =
  let ft = Context.feature_table c
  and nb = Context.count_variables c
  in
  Feature_table.validate_visibility t nb info ft

let push_context
    (entlst:  entities list withinfo)
    (is_pred: bool)
    (is_func: bool)
    (gap:     int)
    (c: Context.t)
    : Context.t =
  let c = Context.push_with_gap entlst None is_pred is_func false gap c in
  if Context.count_last_formal_generics c <> 0 then
    error_info entlst.i "Cannot introduce new formal generics in subexpression";
  c



let analyze_expression
    (ie:        info_expression)
    (tb:        Term_builder.t)
    (c:         Context.t)
    : term =
  (** Analyse the expression [ie] in the context [context] and return the term.
   *)
  assert (not (Context.is_global c));
  if 5 <= Context.verbosity c then
    printf "typer analyze %s\n" (string_of_expression ie.v);
  let info, exp = ie.i, ie.v in
  let rec analyze
      (e:expression)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let nargs = Accus.expected_arity accs
    in
    let feat (fn:feature_name) = features fn nargs info c
    and id   (name:int)        = identifiers name nargs info c
    and do_leaf (lst: (int*Tvars.t*Sign.t) list): unit =
      process_leaf lst c info accs
    in
    try
      match e with
        Expproof (_,_,_)
      | Expquantified (_,_,Expproof (_,_,_)) ->
          error_info info "Proof not allowed here"
      | Identifier name     -> do_leaf (id name)
      | Expanon             ->
          not_yet_implemented ie.i ("Expanon Typing of "^ (string_of_expression e))
      | Expfalse            -> do_leaf (feat FNfalse)
      | Exptrue             -> do_leaf (feat FNtrue)
      | Expnumber num       -> do_leaf (feat (FNnumber num))
      | Expop op            -> do_leaf (feat (FNoperator op))
      | Binexp (Asop,e1,mtch) ->
          exp_as ie.i e1 mtch accs c
          (*not_yet_implemented info  ("Typing of " ^ (string_of_expression e))*)
      | Binexp (op,e1,e2)   -> application (Expop op) [|e1; e2|] accs c
      | Unexp  (op,e)       -> application (Expop op) [|e|] accs c
      | Funapp (Expdot(tgt,f),args) ->
          let arg_lst = tgt :: (expression_list args) in
          let args = Array.of_list arg_lst in
          application f args accs c
      | Funapp (f,args)     ->
          application f (Array.of_list (expression_list args)) accs c
      | Expparen e          -> analyze e accs c
      | Expquantified (q,entlst,exp) ->
          quantified q entlst exp accs c
      | Exppred (entlst,e) ->
          lambda entlst None [] e true false accs c
      | Expindset (entlst,rules) ->
          inductive_set entlst rules accs c
      | Expdot (tgt,f) ->
          application f [|tgt|] accs c
      | Tupleexp (a,b) ->
          application (Identifier ST.tuple) [|a;b|] accs c
      | ExpResult ->
          do_leaf (id (ST.symbol "Result"))
      | Exparrow(entlst,e) ->
          lambda entlst None [] e false true accs c
      | Expagent (entlst,rt,pres,exp) ->
          lambda entlst rt pres exp false true accs c
      | Expif (thenlist,elsepart) ->
          exp_if thenlist elsepart accs c
      | Expinspect (inspexp,caselst) ->
          inspect ie.i inspexp caselst accs c
      | Typedexp (e0,tp) ->
          let tp = Context.get_type tp c in
          begin try
            Accus.expect_type tp accs
          with Accus.Untypeable lst ->
            let str    = "Type error \"" ^ (string_of_expression e) ^
              "\"\n  Actual type:\n\t"
            and actual = Context.string_of_type tp c
            and reqs = String.concat "\n\t"
                (List.map Term_builder.string_of_reduced_required_type lst) in
            error_info info (str ^ actual ^ "\n  Required types(s):\n\t" ^ reqs)
          end;
          analyze e0 accs c
      | Bracketapp (_,_) ->
          not_yet_implemented ie.i ("Bracketapp Typing of "^ (string_of_expression e))
      | Expset _ ->
          not_yet_implemented ie.i ("Expset Typing of "^ (string_of_expression e))
      | Expcolon (_,_) ->
          not_yet_implemented ie.i ("Expcolon Typing of "^ (string_of_expression e))
      | Expassign (_,_) ->
          not_yet_implemented ie.i ("Expassign Typing of "^ (string_of_expression e))
      | Cmdinspect (_,_) ->
          not_yet_implemented ie.i ("Expinspect Typing of command "^
                                    (string_of_expression e))
      | Cmdif (_,_) ->
          not_yet_implemented ie.i ("Expif Typing of command "
                                    ^ (string_of_expression e))
      | Proofinspect _ | Proofif _ | Proofgif _ ->
          assert false (* cannot happen *)
    with Accus.Untypeable _ ->
      error_info ie.i
        ("Type error in expression \"" ^ (string_of_expression e) ^ "\"")

  and application
      (f:expression)
      (args: expression array) (* unreversed, i.e. as in the source code *)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let nargs = Array.length args in
    assert (0 < nargs);
    Accus.expect_function nargs accs;
    analyze f accs c;
    for i=0 to nargs-1 do
      Accus.expect_argument accs;
      analyze args.(i) accs c
    done;
    Accus.complete_function accs

  and quantified
      (q:quantifier)
      (entlst:entities list withinfo)
      (e:expression)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let ntvs_gap = Accus.ntvs_added accs in
    let c = push_context entlst false false ntvs_gap c in
    Accus.expect_quantified c accs;
    analyze e accs c;
    let is_all = match q with Universal -> true | Existential -> false in
    Accus.complete_quantified is_all accs

  and lambda
      (entlst:entities list withinfo)
      (rt: return_type)
      (pres: compound)
      (e:expression)
      (is_pred: bool)
      (is_func: bool)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let ntvs_gap = Accus.ntvs_added accs in
    let c = push_context entlst is_pred is_func ntvs_gap c in
    let rec anapres (pres:compound) (npres:int): int =
      match pres with
        [] -> npres
      | p::pres ->
          Accus.expect_boolean_expression accs;
          analyze p.v accs c;
          anapres pres (1+npres)
    in
    Accus.expect_lambda is_pred c accs;
    analyze e accs c;
    let npres = anapres pres 0 in
    let nms = Context.local_argnames c in
    let n = Array.length nms in
    Accus.complete_lambda n nms npres is_pred accs


  and inductive_set
      (entlst: entities list withinfo)
      (rules: expression list)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let ntvs_gap = Accus.ntvs_added accs in
    let c1 = push_context entlst false false ntvs_gap c in
    let nargs = Context.count_last_arguments c1 in
    assert (0 < nargs);
    if 1 < nargs then
      not_yet_implemented entlst.i "Multiple inductive sets";
    let analyze_rule (r:expression): unit =
      Accus.expect_boolean_expression accs;
      analyze r accs c1
    in
    Accus.expect_inductive c1 accs;
    List.iter analyze_rule rules;
    Accus.complete_inductive entlst.i (List.length rules) accs


  and exp_if
      (thenlist: (expression * expression) list)
      (elsepart: expression option)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let rec do_exp_if (n:int) (thenlist:(expression * expression) list): unit =
      let terminate has_else n =
        if has_else then
          Accus.complete_if true accs
        else
          Accus.complete_if false accs;
        for i = 1 to n-1 do
          Accus.complete_if true accs
        done;
        Accus.drop_expected accs
      in
      match thenlist with
        [] ->
          begin
            match elsepart with
              None ->
                terminate false n
            | Some e ->
                Accus.get_expected 0 accs;
                analyze e accs c;
                terminate true n
          end
      | (cond,e)::lst ->
          Accus.expect_boolean_expression accs;
          analyze cond accs c;
          Accus.get_expected 0 accs;
          analyze e accs c;
          do_exp_if (n+1) lst
    in
    Accus.push_expected accs;
    Accus.expect_if accs;
    do_exp_if 0 thenlist

  and inspect (info:info)
      (insp:expression)
      (caselst:(expression*expression) list)
      (accs: Accus.t)
      (c:Context.t)
      :unit =
    let do_case (i:int) ((m,r):expression*expression): unit =
      let m,nms = case_variables info m false c
      and ntvs_gap = Accus.ntvs_added accs in
      let c1   = Context.push_untyped_gap nms ntvs_gap c in
      Accus.expect_case c1 accs;
      Accus.get_expected 0 accs;
      analyze m accs c1;
      Accus.get_expected 1 accs;
      analyze r accs c1;
      Accus.complete_case accs
    in
    let rec do_case_list i lst =
      match lst with
        [] -> i
      | c::lst ->
          do_case i c;
          do_case_list (1+i) lst
    in
    Accus.expect_inspect accs;
    Accus.push_expected accs;
    Accus.expect_new_untyped accs;
    Accus.push_expected accs;  (* stack = [match_type insp_type ...]*)
    analyze insp accs c;
    let ncases = do_case_list 0 caselst in
    assert (0 < ncases);
    Accus.complete_inspect ncases accs;
    Accus.drop_expected accs;
    Accus.drop_expected accs

  and exp_as
      (info:info)
      (e:expression)
      (mtch:expression)
      (accs:Accus.t)
      (c:Context.t): unit =
    Accus.expect_boolean accs;
    Accus.expect_as accs;
    Accus.push_expected accs;
    Accus.expect_new_untyped accs;
    Accus.push_expected accs;
    analyze e accs c;
    let mtch,nms = case_variables info mtch false c
    and ntvs_gap = Accus.ntvs_added accs in
    let c1 = Context.push_untyped_gap nms ntvs_gap c in
    Accus.expect_case c1 accs;
    Accus.get_expected 0 accs;
    analyze mtch accs c1;
    Accus.complete_as accs;
    Accus.drop_expected accs;
    Accus.drop_expected accs
  in

  let accs   = Accus.make tb c in
  analyze exp accs c;
  assert (not (Accus.is_empty accs));

  Accus.check_uniqueness info exp accs;

  let tb = Accus.first accs in
  if not (Term_builder.is_fully_typed tb) then begin
    let str =
      "The term \"" ^ (string_of_expression ie.v)
      ^ "\" has not enough variables to determine all formal generics"
    in
    error_info ie.i str
  end;
  Term_builder.update_context tb;

  let term = Term_builder.normalized_result tb in
  Term_builder.release tb;

  validate_term ie.i term c;
  validate_visibility ie.i term c;
  assert (Context.is_well_typed term c);
  let term = unfold_inspect ie.i term c in
  assert (Context.is_well_typed term c);
  (*assert (Term_builder.is_valid term c);*)
  term



let result_term
    (ie:  info_expression)
    (c:   Context.t)
    : term =
  (** Analyse the expression [ie] as the result expression of the
      context [context] and return the term.
   *)
  assert (not (Context.is_global c));
  let tb = Term_builder.occupy_context c in
  analyze_expression ie tb c


let boolean_term (ie: info_expression) (c:Context.t): term =
  assert (not (Context.is_global c));
  let tb = Term_builder.occupy_boolean c in
  analyze_expression ie tb c


let typed_term
    (ie:info_expression) (tp:type_term) (c:Context.t): term =
  assert (not (Context.is_global c));
  let tb = Term_builder.occupy_typed tp c in
  analyze_expression ie tb c

let untyped_term
    (ie:info_expression) (c:Context.t): term =
  assert (not (Context.is_global c));
  let tb = Term_builder.occupy_untyped c in
  analyze_expression ie tb c
