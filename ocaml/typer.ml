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

  val make:              bool -> Context.t -> t
  val is_empty:          t -> bool
  val is_singleton:      t -> bool
  val is_tracing:        t -> bool
  val count:             t -> int
  val ntvs_added:        t -> int
  val expected_arity:    t -> int
  val expected_signatures_string: t -> string
  val substitutions_string: t -> string
  val expect_boolean:    t -> unit
  val expect_type:       term -> t -> unit
  val expect_boolean_expression:    t -> unit
  val expect_new_untyped:t -> unit
  val remove_untyped:    t -> unit
  val push_expected:     t -> unit
  val get_expected:      int -> t -> unit
  val drop_expected:     t -> unit
  val complete_if:      bool -> t -> unit
  val add_leaf:          (int*Tvars.t*Sign.t) list -> t -> unit
  val expect_function:   int -> t -> unit
  val expect_argument:   int -> t -> unit
  val complete_function: int -> t -> unit
  val expect_lambda:     int -> bool -> Context.t -> t -> unit
  val complete_lambda:   int -> int -> int -> bool -> t -> unit
  val expect_quantified: int -> Context.t -> t -> unit
  val complete_quantified:   int -> int -> bool -> t -> unit
  val expect_case:       Context.t -> t -> unit
  val complete_case:     int -> t -> unit
  val complete_inspect:  int ->  t -> unit
  val complete_as:       int -> t -> unit
  val specialize_terms:  t -> unit
  val check_uniqueness:  info -> expression -> t -> unit
  val check_untyped_variables: info -> t -> unit
  val remove_dummies:    info_expression -> t -> unit
  val result:            t -> term * TVars_sub.t

end = struct

  type t = {mutable accus: Term_builder.t list;
            mutable ntvs_added: int;
            mutable arity:  int;
            trace: bool;
            mutable c: Context.t}

  exception Untypeable of Term_builder.t list


  let make (is_bool:bool) (c:Context.t): t =
    let tb =
      if is_bool then
        Term_builder.make_boolean c
      else
        Term_builder.make c
    in
    {accus           = [tb];
     ntvs_added      = 0;
     arity           = 0;
     trace           = (5 <= Context.verbosity c);
     c               = c}

  let is_empty     (accs:t): bool =   Mylist.is_empty     accs.accus

  let is_singleton (accs:t): bool =   Mylist.is_singleton accs.accus

  let is_unique (accs:t): bool =
    match accs.accus with
      [] -> assert false
    | [_] -> true
    | hd::tl ->
        let res,_ = Term_builder.result hd in
        List.for_all (fun tb -> res = fst (Term_builder.result tb)) tl

  let is_tracing (accs:t): bool = accs.trace

  let count (accs:t): int = List.length accs.accus

  let ntvs_added (accs:t): int = accs.ntvs_added

  let expected_arity (accs:t): int = accs.arity

  let expected_signatures_string (accs:t): string =
    "{" ^
    (String.concat
      ","
      (List.map (fun acc -> Term_builder.signature_string acc) accs.accus)) ^
    "}"

  let substitutions_string (accs:t): string =
    "{" ^
    (String.concat
       ","
       (List.map (fun acc -> Term_builder.substitution_string acc) accs.accus)) ^
    "}"


  let trace_accus (accs:t): unit =
    let accus = accs.accus in
    List.iteri
      (fun i acc ->
        let t = Term_builder.head_term acc in
        printf "    %d: \"%s\"  \"%s\" %s %s\n"
          i
          (Term_builder.string_of_head_term acc) (Term.to_string t)
          (Term_builder.string_of_tvs_sub acc)
          (Term_builder.string_of_head_signature acc))
      accus


  let expect_boolean_expression (accs:t): unit =
    List.iter
      (fun acc -> Term_builder.expect_boolean_expression acc)
      accs.accus


  let expect_new_untyped (accs:t): unit =
    accs.ntvs_added <- accs.ntvs_added + 1;
    List.iter Term_builder.expect_new_untyped accs.accus


  let remove_untyped (accs:t): unit =
    List.iter Term_builder.remove_untyped accs.accus;
    accs.ntvs_added <- accs.ntvs_added - 1


  let expect_function (nargs:int) (accs:t): unit =
    accs.arity           <- nargs;
    accs.ntvs_added      <- nargs + accs.ntvs_added;
    List.iter (fun acc -> Term_builder.expect_function nargs acc) accs.accus



  let complete_function (nargs:int) (accs:t): unit =
    accs.ntvs_added <- accs.ntvs_added - nargs;
    List.iter
      (fun acc -> Term_builder.complete_function nargs acc)
      accs.accus;
    if accs.trace then begin
      printf "  complete function with %d arguments\n" nargs;
      trace_accus accs
    end



  let expect_argument (i:int) (accs:t): unit =
    (** Expect the next argument of the current application *)
    accs.arity <- 0;
    List.iter (fun acc -> Term_builder.expect_argument i acc) accs.accus


  let add_leaf
      (terms: (int*Tvars.t*Sign.t) list)
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
              try (Term_builder.add_leaf i tvs s acc) :: lst
              with Not_found -> lst)
            lst
          terms
        )
        []
        accus;
    if accs.trace && 1 < List.length terms then begin
      let ct = Context.class_table accs.c in
      printf "multiple leafs\n";
      List.iter
        (fun (i,tvs,sign) ->
          printf "  %d %s %s\n" i
            (Context.string_of_term (Variable i) false 0 accs.c)
            (Class_table.string_of_complete_signature sign tvs ct))
        terms
    end;
    if accs.trace then begin
      printf "  add_leaf\n";
      trace_accus accs
    end;
    if accs.accus = [] then
      raise (Untypeable accus)



  let iter_accus (f:Term_builder.t->unit) (accs:t): unit =
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



  let iter_accus_save (f:Term_builder.t->unit) (accs:t): unit =
    try
      iter_accus f accs
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
    iter_accus (fun acc -> Term_builder.expect_type tp acc) accs


  let push_expected (accs:t): unit =
    iter_accus_save Term_builder.push_expected accs

  let get_expected (i:int) (accs:t): unit =
    iter_accus_save (fun acc -> Term_builder.get_expected i acc) accs

  let drop_expected (accs:t): unit =
    iter_accus_save Term_builder.drop_expected accs


  let complete_if (has_else:bool) (accs:t): unit =
    iter_accus_save (fun acc -> Term_builder.complete_if has_else acc) accs


  let expect_lambda
      (ntvs:int) (is_pred:bool) (c:Context.t) (accs:t)
      : unit =
    assert (0 <= ntvs);
    accs.arity      <- 0;
    accs.ntvs_added <- 0;
    accs.c          <- c;
    map_accus
      (fun acc -> Term_builder.expect_lambda ntvs is_pred c acc)
      accs


  let complete_lambda (ntvs:int) (ntvs_added:int) (npres:int) (is_pred:bool) (accs:t)
      : unit =
    iter_accus
      (fun acc -> Term_builder.complete_lambda ntvs npres is_pred acc) accs;
    accs.ntvs_added <- ntvs_added;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete lambda\n";
      trace_accus accs
    end




  let expect_quantified (ntvs:int) (c:Context.t) (accs:t): unit =
    assert (0 <= ntvs);
    accs.arity      <- 0;
    accs.ntvs_added <- 0;
    accs.c          <- c;
    iter_accus
      (fun acc -> Term_builder.expect_quantified ntvs c acc)
      accs


  let complete_quantified (ntvs:int) (ntvs_added:int) (is_all:bool) (accs:t)
      : unit =
    iter_accus
      (fun acc -> Term_builder.complete_quantified ntvs is_all acc) accs;
    accs.ntvs_added <- ntvs_added;
    accs.c <- Context.pop accs.c;
    if accs.trace then begin
      printf "  complete quantified\n";
      trace_accus accs
    end



  let expect_case (c:Context.t) (accs:t): unit =
    accs.c <- c;
    accs.ntvs_added <- 0;
    iter_accus_save (fun acc -> Term_builder.expect_case c acc) accs


  let complete_case (ntvs_added:int) (accs:t): unit =
    iter_accus_save Term_builder.complete_case accs;
    accs.ntvs_added <- ntvs_added;
    accs.c <- Context.pop accs.c


  let complete_inspect (ncases:int) (accs:t): unit =
    iter_accus_save (fun acc -> Term_builder.complete_inspect ncases acc) accs

  let complete_as (ntvs_added:int) (accs:t): unit =
    iter_accus_save Term_builder.complete_as accs;
    accs.ntvs_added <- ntvs_added;
    accs.c <- Context.pop accs.c


  let get_diff (t1:term) (t2:term) (accs:t): string * string =
    let nargs = Context.count_variables accs.c
    and ft    = Context.feature_table accs.c
    in
    let vars1 = List.rev (Term.used_variables_from t1 nargs)
    and vars2 = List.rev (Term.used_variables_from t2 nargs) in
    let lst   = Mylist.combine vars1 vars2 in
    let i,j = List.find (fun (i,j) -> i<>j) lst in
    let str1 = Feature_table.string_of_signature (i-nargs) ft
    and str2 = Feature_table.string_of_signature (j-nargs) ft in
    str1, str2


  let specialize_terms (accs:t): unit =
    List.iter (fun tb -> Term_builder.specialize_term tb) accs.accus;
    if accs.trace then begin
      printf "  update terms\n";
      trace_accus accs
    end

  let check_uniqueness (inf:info) (e:expression) (accs:t): unit =
    match accs.accus with
      [] -> assert false
    | hd::tl ->
        let t1,tvars2 = Term_builder.result hd in
        try
          let acc = List.find (fun acc -> fst (Term_builder.result acc) <> t1) tl in
          let t2,tvars2 = Term_builder.result acc
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

  let check_untyped_variables (inf:info) (accs:t): unit =
    List.iter
      (fun acc ->
        try
          Term_builder.check_untyped_variables acc;
          Term_builder.update_called_variables acc
        with Term_builder.Incomplete_type i ->
          error_info inf
            ("Cannot infer a type for " ^
             ST.string (Context.variable_name i accs.c)))
      accs.accus


  let remove_dummies (ie:info_expression) (accs:t): unit =
    accs.accus <-
      List.fold_left
        (fun lst acc ->
          if Term_builder.has_dummy acc then lst
          else acc::lst)
        []
        accs.accus;
    if accs.accus = [] then
      error_info ie.i ("Cannot type the expression \"" ^
                       (string_of_expression ie.v) ^
                       "\"")



  let result (accs:t): term * TVars_sub.t =
    assert (is_unique accs);
    Term_builder.result (List.hd accs.accus)
end (* Accus *)




let unfold_inspect (t:term) (c:Context.t): term =
  let ft    = Context.feature_table c
  and nvars = Context.count_variables c in
  let rec unfold t nb =
    let unfold_args args = Array.map (fun a -> unfold a nb) args
    and unfold_list lst  = List.map  (fun a -> unfold a nb) lst
    in
    match t with
      Variable i ->
        t
    | VAppl (i,args) ->
        VAppl (i, unfold_args args)
    | Application (f,args,pr) ->
        let f    = unfold f nb
        and args = unfold_args args in
        Application(f,args,pr)
    | Lam (n,nms,pres,t,pr) ->
        let pres = unfold_list pres
        and t    = unfold t (1+nb) in
        Lam(n,nms,pres,t,pr)
    | QExp (n,nms,t,is_all) ->
        QExp (n, nms, unfold t (n+nb), is_all)
    | Flow (Inspect,args) ->
        let args = unfold_args args in
        let args = Feature_table.inspect_unfold_catchall args (nb+nvars) ft in
        Flow(Inspect,args)
    | Flow (ctrl,args) ->
        Flow (ctrl, unfold_args args)
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
      let str = "Type error \"" ^ (Context.string_of_term (Variable i) false 0 c) ^
        "\"\n  Actual type(s):\n\t"
      and actuals = String.concat "\n\t"
          (List.map
             (fun (_,tvs,s) ->
               Class_table.string_of_reduced_complete_signature s tvs ct)
             lst)
      and reqs = String.concat "\n\t"
          (List.map Term_builder.string_of_reduced_substituted_signature acc_lst)
      in
      error_info info (str ^ actuals ^ "\n  Required type(s):\n\t" ^ reqs)



let term_builder (is_bool:bool) (c:Context.t): Term_builder.t =
  if is_bool then Term_builder.make_boolean c
  else Term_builder.make c


let is_constant (nme:int) (c:Context.t): bool =
  let nvars = Context.count_variables c in
  try
    let lst   = Context.find_identifier nme 0 c in
    let lst = List.filter
        (fun (idx,_,_) -> nvars <= idx ) lst in
    lst <> []
  with Not_found ->
    false


let case_variables (e:expression) (c:Context.t): expression * int list =
  let rec vars (e:expression) (nanon:int) (lst:int list): expression * int * int list =
    match e with
      Expnumber _ | Exptrue | Expfalse ->
        e, nanon, lst
    | Identifier nme | Typedexp(Identifier nme,_)->
        let lst =
          if is_constant nme c then
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
        let f,nanon,lst = vars f nanon lst in
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
        let f, nanon, lst  = vars f nanon lst in
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
  let e, nanon, lst = vars e 0 [] in
  e, List.rev lst


let validate_term (info:info) (t:term) (c:Context.t): unit =
  (* Check that all match expression in inspect expressions have only constructors
     and variables *)
  let rec validate t c =
    let val_args args c = Array.iter (fun arg -> validate arg c) args in
    let val_lst  lst  c = List.iter  (fun t   -> validate t c)   lst  in
    match t with
      Variable i -> ()
    | VAppl(_,args) -> val_args args c
    | Application(f,args,pr) ->
        validate f c; val_args args c
    | Lam (n,nms,pres,t,pr) ->
        let c = Context.push_untyped [|ST.symbol "$0"|] c in
        val_lst pres c; validate t c
    | QExp (n,nms,t,_) ->
        let c = Context.push_untyped nms c in
        validate t c
    |  Flow (flow,args) ->
        let len = Array.length args in
        let check_match mtch c =
          if Context.is_case_match_expression mtch c then
            ()
          else
            error_info info
              ("The term \"" ^ (Context.string_of_term mtch true 0 c) ^
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
                let n, nms, mtch,_ = Term.qlambda_split_0 args.(2*i+1)
                and n1,nms1,res ,_ = Term.qlambda_split_0 args.(2*i+2) in
                assert (n = n1);
                let c = Context.push_untyped nms c in
                validate res c;
                check_match mtch c
              done
          | Asexp ->
              assert (len = 2);
              validate args.(0) c;
              let n,nms,mtch,_ = Term.qlambda_split_0 args.(1) in
              let c = Context.push_untyped nms c in
              check_match mtch c
        end
  in
  validate t c


let analyze_expression
    (ie:        info_expression)
    (is_bool:   bool)
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
      | Expdot (tgt,f) ->
          application f [|tgt|] accs c
      | Tupleexp (a,b) ->
          application (Identifier ST.tuple) [|a;b|] accs c
      | ExpResult ->
          do_leaf (id (ST.symbol "Result"))
      | Exparrow(entlst,e) ->
          lambda entlst None [] e false true accs c
      | Expagent (entlst,rt,pres,posts) ->
          begin match posts with
            [ie0] ->
              begin match ie0.v with
                Binexp (Eqop, ExpResult, exp) ->
                  lambda entlst rt pres exp false true accs c
              | _ ->
                  not_yet_implemented ie.i "Agents defined with properties"
              end
          | _ ->
              not_yet_implemented ie.i "Agents defined with properties"
          end
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
                (List.map Term_builder.string_of_reduced_substituted_signature lst) in
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
      Accus.expect_argument i accs;
      analyze args.(i) accs c
    done;
    Accus.complete_function nargs accs

  and quantified
      (q:quantifier)
      (entlst:entities list withinfo)
      (e:expression)
      (accs: Accus.t)
      (c:Context.t)
      : unit =
    let ntvs_gap = Accus.ntvs_added accs in
    let c = Context.push_with_gap entlst None false false false ntvs_gap c in
    let ntvs      = Context.count_local_type_variables c in
    Accus.expect_quantified (ntvs-ntvs_gap) c accs;
    analyze e accs c;
    Accus.check_untyped_variables entlst.i accs;
    let is_all = match q with Universal -> true | Existential -> false in
    Accus.complete_quantified (ntvs-ntvs_gap) ntvs_gap is_all accs

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
    let c = Context.push_with_gap entlst None is_pred is_func false ntvs_gap c in
    let ntvs      = Context.count_local_type_variables c in
    let rec anapres (pres:compound) (npres:int): int =
      match pres with
        [] -> npres
      | p::pres ->
          Accus.expect_boolean_expression accs;
          analyze p.v accs c;
          anapres pres (1+npres)
    in
    Accus.expect_lambda (ntvs-ntvs_gap) is_pred c accs;
    analyze e accs c;
    let npres = anapres pres 0 in
    Accus.check_untyped_variables entlst.i accs;
    Accus.complete_lambda (ntvs-ntvs_gap) ntvs_gap npres is_pred accs

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
    do_exp_if 0 thenlist

  and inspect (info:info)
      (insp:expression)
      (caselst:(expression*expression) list)
      (accs: Accus.t)
      (c:Context.t)
      :unit =
    let do_case (i:int) ((m,r):expression*expression): unit =
      let m,nmslst =
        try case_variables m c
        with Not_found ->
          error_info info ("Cannot extract variables from \"case " ^
                           (string_of_expression m) ^ " then " ^
                           (string_of_expression r) ^ "\"")
      and ntvs_gap = Accus.ntvs_added accs in
      if Mylist.has_duplicates nmslst then
        error_info info "Duplicate variable in inspect expression";
      let nms = Array.of_list nmslst in
      let c1   = Context.push_untyped_gap nms ntvs_gap c in
      Accus.expect_case c1 accs;
      Accus.get_expected 0 accs;
      if i = 0 then
        begin match m with
          Identifier id when List.mem id nmslst ->
            error_info info "First case cannot match all"
        | _ -> ()
        end;
      analyze m accs c1;
      Accus.get_expected 1 accs;
      analyze r accs c1;
      Accus.complete_case ntvs_gap accs
    in
    let rec do_case_list i lst =
      match lst with
        [] -> i
      | c::lst ->
          do_case i c;
          do_case_list (1+i) lst
    in
    Accus.push_expected accs;
    Accus.expect_new_untyped accs;
    Accus.push_expected accs;  (* stack = [match_type insp_type ...]*)
    analyze insp accs c;
    let ncases = do_case_list 0 caselst in
    assert (0 < ncases);
    Accus.remove_untyped accs;
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
    Accus.push_expected accs;
    Accus.expect_new_untyped accs;
    Accus.push_expected accs;
    analyze e accs c;
    let mtch,nmslst = case_variables mtch c
    and ntvs_gap = Accus.ntvs_added accs in
    if Mylist.has_duplicates nmslst then
      error_info info "Duplicate variable in as expression";
    let nms = Array.of_list nmslst in
    let c1 = Context.push_untyped_gap nms ntvs_gap c in
    Accus.expect_case c1 accs;
    Accus.get_expected 0 accs;
    analyze mtch accs c1;
    Accus.complete_as ntvs_gap accs;
    Accus.remove_untyped accs;
    Accus.drop_expected accs;
    Accus.drop_expected accs
  in

  let accs   = Accus.make is_bool c in
  analyze exp accs c;
  assert (not (Accus.is_empty accs));

  Accus.remove_dummies ie accs;
  Accus.specialize_terms accs;
  (*Accus.check_untyped_variables ie.i accs;*)
  Accus.check_uniqueness info exp accs;

  let term,tvars_sub = Accus.result accs in
  validate_term ie.i term c;
  Context.update_type_variables tvars_sub c;
  let term = unfold_inspect term c in
  assert (Term_builder.is_valid term is_bool c);
  term



let result_term
    (ie:  info_expression)
    (c:   Context.t)
    : term =
  (** Analyse the expression [ie] as the result expression of the
      context [context] and return the term.
   *)
  assert (not (Context.is_global c));
  analyze_expression ie false c


let boolean_term (ie: info_expression) (c:Context.t): term =
  assert (not (Context.is_global c));
  analyze_expression ie true c


let specialized (t:term) (c: Context.t): term =
  Term_builder.specialized t c
