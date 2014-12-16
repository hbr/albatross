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

  val make:              Context.t -> t
  val is_empty:          t -> bool
  val is_singleton:      t -> bool
  val count:             t -> int
  val ntvs_added:        t -> int
  val expected_arity:    t -> int
  val expected_signatures_string: t -> string
  val substitutions_string: t -> string
  val add_leaf:          (int*Tvars.t*Sign.t) list -> t -> unit
  val expect_function:   int -> t -> unit
  val expect_argument:   int -> t -> unit
  val complete_function: int -> t -> unit
  val expect_lambda:     int -> bool -> bool -> t -> unit
  val complete_lambda:   int -> int -> int array -> t -> unit
  val check_uniqueness:  info -> expression -> t -> unit
  val check_type_variables: info -> t -> unit
  val result:            t -> term * TVars_sub.t

end = struct

  type t = {mutable accus: Term_builder.t list;
            mutable ntvs_added: int;
            mutable arity:  int;
            c: Context.t}

  exception Untypeable of Term_builder.t list


  let make (c:Context.t): t =
    {accus           = [Term_builder.make c];
     ntvs_added      = 0;
     arity           = 0;
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


  let expect_function (nargs:int) (accs:t): unit =
    accs.arity           <- nargs;
    accs.ntvs_added      <- nargs + accs.ntvs_added;
    List.iter (fun acc -> Term_builder.expect_function nargs acc) accs.accus


  let complete_function (nargs:int) (accs:t): unit =
    accs.ntvs_added <- accs.ntvs_added - nargs;
    List.iter
      (fun acc -> Term_builder.complete_function nargs acc)
      accs.accus



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
    if accs.accus = [] then
      raise (Untypeable accus)



  let expect_lambda (ntvs:int) (is_quant:bool) (is_pred:bool) (accs:t): unit =
    assert (0 <= ntvs);
    accs.arity      <- 0;
    accs.ntvs_added <- 0;
    accs.accus <-
      List.fold_left
        (fun lst acc ->
          try
            Term_builder.expect_lambda ntvs is_quant is_pred acc;
            acc::lst
          with Not_found ->
            lst)
        []
        accs.accus;
    if accs.accus = [] then
      assert false (* must be handled *)
    (*List.iter
      (fun acc ->
        try Term_builder.expect_lambda ntvs is_quant is_pred acc
        with Not_found -> assert false (* must be handled*))
      accs.accus*)


  let complete_lambda (ntvs:int) (ntvs_added:int) (nms:int array) (accs:t): unit =
    List.iter (fun acc -> Term_builder.complete_lambda ntvs nms acc) accs.accus;
    accs.ntvs_added <- ntvs_added




  let get_diff (t1:term) (t2:term) (accs:t): string * string =
    let nargs = Context.count_arguments accs.c
    and ft    = Context.feature_table accs.c
    in
    let vars1 = Term.used_variables_from t1 nargs
    and vars2 = Term.used_variables_from t2 nargs in
    let lst =
      try List.combine vars1 vars2
      with Invalid_argument _ -> assert false (* cannot happen *)
    in
    let i,j = List.find (fun (i,j) -> i<>j) (List.rev lst) in
    let str1 = Feature_table.string_of_signature (i-nargs) ft
    and str2 = Feature_table.string_of_signature (j-nargs) ft in
    str1, str2




  let check_uniqueness (inf:info) (e:expression) (accs:t): unit =
    List.iter (fun tb -> Term_builder.update_term tb) accs.accus;
    if is_singleton accs then
      ()
    else begin
      let estr = string_of_expression e
      in
      let t1,tvars1 = Term_builder.result (List.hd accs.accus)
      and t2,tvars2 = Term_builder.result (List.hd (List.tl accs.accus))
      in
      let str1, str2 = get_diff t1 t2 accs in
      error_info inf
        ("The expression " ^ estr ^ " is ambiguous \"" ^
        str1 ^ "\" or \"" ^ str2 ^ "\""  )
    end

  let check_type_variables (inf:info) (accs:t): unit =
    List.iter (fun acc -> Term_builder.check_type_variables inf acc) accs.accus

  let result (accs:t): term * TVars_sub.t =
    assert (is_unique accs);
    Term_builder.result (List.hd accs.accus)
end (* Accus *)





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
  (Class_table.string_of_tvs tvs ct) ^
  (Class_table.string_of_signature s tvs ct)


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
      let i,_,_ = List.hd lst in
      let str = "The expression \""
        ^ (Context.string_of_term (Variable i) 0 c)
        ^ "\" with types "
        ^ (string_of_signatures lst c)
        ^ " does not satisfy any of the expected types in {"
        ^ (String.concat
             ","
             (List.map
                (fun acc ->
                  (*(string_of_int (Term_builder.count_local acc)) ^
                  "[" ^ (Term_builder.concepts_string acc) ^ "]" ^
                  (Term_builder.substitution_string acc) ^*)
                  (Term_builder.string_of_tvs_sub acc) ^
                  (Term_builder.signature_string acc))
                acc_lst))
        ^ "}"
      in
      Context.print_local_contexts c;
      error_info info str



let analyze_expression
    (ie:        info_expression)
    (c:         Context.t)
    : term =
  (** Analyse the expression [ie] in the context [context] and return the term.
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
    and do_leaf (lst: (int*Tvars.t*Sign.t) list): unit =
      process_leaf lst c info accs
    in
    let rec arg_list (e:expression): expression list =
      match e with
        Explist lst -> lst
      | Tupleexp (a,b) ->
          a :: arg_list b
      | _ -> [e]
    in
    match e with
      Expproof (_,_,_)
    | Expquantified (_,_,Expproof (_,_,_)) ->
        error_info info "Proof not allowed here"
    | Identifier name     -> do_leaf (id name)
    | Expfalse            -> do_leaf (feat FNfalse)
    | Exptrue             -> do_leaf (feat FNtrue)
    | Expnumber num       -> do_leaf (feat (FNnumber num))
    | Expop op            -> do_leaf (feat (FNoperator op))
    | Binexp (op,e1,e2)   -> application (Expop op) [|e1; e2|] accs
    | Unexp  (op,e)       -> application (Expop op) [|e|] accs
    | Funapp (Expdot(tgt,f),args) ->
        let arg_lst = tgt :: (arg_list args) in
        let args = Array.of_list arg_lst in
        application f args accs
    | Funapp (f,args)     ->
        application f (Array.of_list (arg_list args)) accs
    | Expparen e          -> analyze e accs
    | Expquantified (q,entlst,exp) ->
        quantified q entlst exp accs
    | Exppred (entlst,e) ->
        lambda entlst e false true false accs
    | Expdot (tgt,f) ->
        application f [|tgt|] accs
    | ExpResult ->
        not_yet_implemented ie.i ("ExpResult Typing of "^ (string_of_expression e))
    | Exparrow(entlst,e) ->
        not_yet_implemented ie.i ("Exparrow Typing of "^ (string_of_expression e))
    | Expbracket _ ->
        not_yet_implemented ie.i ("Expbracket Typing of "^ (string_of_expression e))
    | Bracketapp (_,_) ->
        not_yet_implemented ie.i ("Bracketapp Typing of "^ (string_of_expression e))
    | Expset _ ->
        not_yet_implemented ie.i ("Expset Typing of "^ (string_of_expression e))
    | Explist _ ->
        not_yet_implemented ie.i ("Explist Typing of "^ (string_of_expression e))
    | Tupleexp (_,_) ->
        not_yet_implemented ie.i ("Tupleexp Typing of "^ (string_of_expression e))
    | Expcolon (_,_) ->
        not_yet_implemented ie.i ("Expcolon Typing of "^ (string_of_expression e))
    | Expassign (_,_) ->
        not_yet_implemented ie.i ("Expassign Typing of "^ (string_of_expression e))
    | Expif (_,_) ->
        not_yet_implemented ie.i ("Expif Typing of "^ (string_of_expression e))
    | Expinspect (_,_) ->
        not_yet_implemented ie.i ("Expinspect Typing of "^ (string_of_expression e))
    | Typedexp (_,_) ->
        not_yet_implemented ie.i ("Typedexp Typing of "^ (string_of_expression e))

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
    process_leaf (features (FNoperator qop) 1 info c) c info accs;
    Accus.expect_argument 0 accs;
    lambda entlst e true true false accs;
    Accus.complete_function 1 accs

  and lambda
      (entlst:entities list withinfo)
      (e:expression)
      (is_quant: bool)
      (is_pred: bool)
      (is_func: bool)
      (accs: Accus.t)
      : unit =
    let ntvs_gap = Accus.ntvs_added accs in
    Context.push_with_gap entlst None is_pred is_func ntvs_gap c;
    let ntvs      = Context.count_local_type_variables c
    and fargnames = Context.local_fargnames c in
    Accus.expect_lambda (ntvs-ntvs_gap) is_quant is_pred accs;
    analyze e accs;
    Accus.check_type_variables entlst.i accs;
    Accus.complete_lambda (ntvs-ntvs_gap) ntvs_gap fargnames accs;
    Context.pop c

  in

  let accs   = Accus.make c in
  analyze exp accs;
  assert (not (Accus.is_empty accs));

  Accus.check_uniqueness info exp accs;
  Accus.check_type_variables ie.i accs;

  let term,tvars_sub = Accus.result accs in
  Context.update_type_variables tvars_sub c;
  term



let result_term
    (ie:  info_expression)
    (c:   Context.t)
    : term =
  (** Analyse the expression [ie] as the result expression of the
      context [context] and return the term.
   *)
  (*printf "trying to type %s\n" (string_of_expression ie.v);*)
  assert (not (Context.is_global c));
  analyze_expression ie c
