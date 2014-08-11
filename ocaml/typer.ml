open Container
open Term
open Signature
open Support
open Printf


module Accus: sig

  type t
  exception Untypeable of Term_builder.t list

  val make:              type_term -> Context.t -> t
  val is_empty:          t -> bool
  val is_singleton:      t -> bool
  val ntvs_added:        t -> int
  val expected_arity:    t -> int
  val expected_signatures_string: t -> string
  val substitutions_string: t -> string
  val add_leaf:          (int*Tvars.t*Sign.t) list -> t -> unit
  val expect_function:   int -> t -> unit
  val expect_argument:   int -> t -> unit
  val complete_function: int -> t -> unit
  val expect_lambda:     int -> t -> unit
  val complete_lambda:   int -> int array -> t -> unit
  val check_uniqueness:  info -> expression -> t -> unit
  val check_type_variables: info -> t -> unit
  val result:            t -> term * TVars_sub.t

end = struct

  type t = {mutable accus: Term_builder.t list;
            mutable ntvs_added: int;
            mutable arity:  int;
            c: Context.t}

  exception Untypeable of Term_builder.t list


  let make (exp: type_term) (c:Context.t): t =
    {accus           = [Term_builder.make exp c];
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


  let expect_lambda (ntvs:int) (accs:t): unit =
    assert (0 <= ntvs);
    accs.arity <- 0;
    List.iter (fun acc -> Term_builder.expect_lambda ntvs acc) accs.accus

  let complete_lambda (ntvs:int) (nms:int array) (accs:t): unit =
    List.iter (fun acc -> Term_builder.complete_lambda ntvs nms acc) accs.accus

  let check_uniqueness (inf:info) (e:expression) (accs:t): unit =
    List.iter (fun tb -> Term_builder.update_term tb) accs.accus;
    if is_singleton accs then
      ()
    else begin
      let estr = string_of_expression e
      in
      printf "Ambiguous expression %s\n" estr;
      List.iter
        (fun acc ->
          let t,_ = Term_builder.result acc in
          printf "\t%s, %s\n"
            (Context.string_of_term t accs.c)
            (Term.to_string t))
        accs.accus;
      error_info inf ("The expression " ^ estr ^ " is ambiguous")
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
  let ntvs = Tvars.count tvs
  and fgnames = Tvars.fgnames tvs in
  Class_table.string_of_signature s ntvs fgnames (Context.class_table c)


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
        ^ (Context.string_of_term (Variable i) c)
        ^ "\" with types "
        ^ (string_of_signatures lst c)
        ^ " does not satisfy any of the expected types in {"
        ^ (String.concat
             ","
             (List.map
                (fun acc ->
                  (string_of_int (Term_builder.ntvars acc)) ^
                  (Term_builder.concepts_string acc) ^
                  (Term_builder.substitution_string acc) ^
                  (Term_builder.signature_string acc))
                acc_lst))
        ^ "}"
      in
      Context.print_local_contexts c;
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
    and do_leaf (lst: (int*Tvars.t*Sign.t) list): unit =
      process_leaf lst c info accs
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
    process_leaf (features (FNoperator qop) 1 info c) c info accs;
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

  Accus.check_uniqueness info exp accs;
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
