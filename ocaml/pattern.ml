open Term
open Signature
open Container
open Support
open Printf

module FT = Feature_table

let is_pattern (n:int) (t:term) (nb:int) (ft:FT.t): bool =
  (* Is the term [t] with [n] variables a pattern i.e. does it contain only variables
     or constructors?

     All variables below [n] must occur only once in a pattern.
   *)
  let is_constr i = (n+nb) <= i && FT.is_constructor (i-n-nb) ft
  in
  let free = Term.free_variables t n
  and bnd  = Term.bound_variables t n
  and bnd_lst = Term.used_variables t n in
  let nbnd = IntSet.cardinal bnd
  in
  IntSet.for_all is_constr free &&
  n = nbnd &&
  nbnd = List.length bnd_lst



let recognizer (t:term) (co:int) (ags:agens) (c:Context.t): term =
  (* A recognizer expression which expresses the fact that term [t] has been
     constructed by the constructor [co] using [ags] to substitute the formal
     generics of [co]. Raise [Not_found] if [co] has no recognizer.*)
  try
    let open Context in
    let nvars = count_variables c
    and tvs = tvars c
    and ft = feature_table c
    in
    assert (nvars <= co);
    let reco = Feature_table.recognizer (co-nvars) ft in
    let res =
      Feature_table.substituted reco 1 0 0 [|t|] nvars ags tvs ft
    in
    (*printf "recognizer\n";
      printf "    constr %s\n" (Feature_table.string_of_signature (co-nvars) c.ft);
      printf "    reco   %s\n" (string_of_term res c);*)
      res
  with Not_found ->
    assert false (* Illegal call *)



let project (t:term) (co:int) (n:int) (ags:agens) (c:Context.t): arguments =
  (* The term [t] projected onto the arguments of the constructor [co] with
     [n] arguments with the actual generics [ags]. *)
  try
    let open Context in
    let nvars = count_variables c
    and tvs = tvars c
    and ft = feature_table c
    in
    assert (nvars + n <= co);
    let tvs_co,sign_co = Feature_table.signature0 (co-n-nvars) ft
    and nfgs_c = Tvars.count_fgs tvs
    and projs = Feature_table.projectors (co-n-nvars) ft in
    assert (Sign.arity sign_co = n);
    assert (Tvars.count_fgs tvs_co = Array.length ags);
    let res =
    Array.map
      (fun proj ->
        let ags_new =
          let tvs_pr,sign_pr = Feature_table.signature0 proj ft in
          assert (Sign.arity sign_pr = 1);
          assert (Tvars.count_fgs tvs_pr = Tvars.count_fgs tvs_co);
          let subs =
            Type_substitution.make_equal
              (Sign.arg_type 0 sign_pr) tvs_pr
              (Sign.result sign_co) tvs_co
              (Context.class_table c)
          in
          Term.subst_array subs nfgs_c ags
        in
        VAppl(proj+nvars, [|t|], ags_new, false)
      )
      projs
    in
    printf "project %s\n" (Context.string_of_term t c);
    printf "  onto constructor %s\n"
           (Feature_table.string_of_signature (co-n-nvars) ft);
    printf "  %s\n" (Context.string_of_term_array "," res c);
    res
  with Not_found ->
    assert false (* Illegal call *)






let unify_with_pattern
      (t:term) (n:int) (pat:term) (c:Context.t)
    : arguments * term list =
  (* Match the term [t] against the pattern [pat] with [n] pattern variables.

     Return a substitution for the pattern variables and a list of recognizer
     conditions to be satisfied.

     Exceptions:

     a) Reject: Conflicting constructors if inductive classes present
     b) Undecidable: For some constructors of inductive classes there is not
                     enough information in the term [t] to decide the case.

     Pseudo inductive types: For each constructor of a pseudo inductive class
     the corresponding recognizer is added to the list and either the corresponding
     part of the term [t] can be matched or a projector is used to substitute
     the variable.

   *)
  let args = Array.make n empty_term
  in
  let term_args (i1:int) (nargs:int) (ags:agens) (pseudo:bool) (t:term): arguments =
    match t with
    | VAppl(i2,args2,_,_) when i2 + n = i1 ->
       args2
    | VAppl(i2,args2,_,_) when not pseudo ->
       if i2 + n <> i1 && Context.is_constructor i2 c then
         raise Reject
       else
         raise Undecidable
    | _ when pseudo ->
       if nargs = 0 then
         [||]
       else
         project t i1 nargs ags c
    | _ ->
       raise Undecidable
  and do_sub i t =
    assert (i < n);
    assert (args.(i) = empty_term); (* No duplicate pattern variables possible *)
    args.(i) <- t
  and args_complete () =
    Array.for_all (fun t -> t <> empty_term) args
  in
  let rec pmatch (pat:term) (t:term) (rlst): term list =
    let match_args pargs targs rlst =
      let len = Array.length pargs in
      assert (len = Array.length targs);
      interval_fold
        (fun lst i ->
          pmatch pargs.(i) targs.(i) lst
        )
        rlst 0 len
    in
    match pat with
    | Variable i ->               (* A pattern variable *)
       assert (i < n);
       do_sub i t;
       rlst
    | VAppl(i1,args1,ags1,_) ->      (* A constructor *)
       let n1 = Array.length args1 in
       if Context.is_pseudo_constructor (i1-n) c then
         begin
           try
             let rlst =
               let reco = recognizer t (i1-n) ags1 c in
               if List.mem reco rlst then
                 rlst
               else
                 reco :: rlst
             in
             match_args args1 (term_args i1 n1 ags1 true t) rlst
           with Not_found ->
             printf "        recognizer not found\n";
             assert false (* There must be a recognizer *)
         end
       else
         match_args args1 (term_args i1 n1 ags1 false t) rlst
    | _ ->
       assert false (* [pat] consists only of variables and constructors. *)
  in
  let rlst = pmatch pat t [] in
  assert (args_complete ());
  args, List.rev rlst




let evaluated_primary_as_expression
      (e:term) (n:int) (tps:types) (pat:term) (c:Context.t): term =
  (* The as expression is [e as pat] where [e] cannot be matched neither
     partially against the pattern.

     The as expression has the evaluation

         all(pvars) e = pat

   *)
  let nms = anon_argnames n in
  let e = Term.up n e
  and c1 = Context.push_typed0 (nms,tps) empty_formals c in
  Term.some_quantified n (nms,tps) (Context.equality_term e pat c1)


let make_as_expression
      (e:term) (tps:formals) (pat:term) (c:Context.t): term =
  (* Construct the as expression [e as pat] and eliminate all unused variables
     from (nms,tps).
   *)
  assert (Context.has_no_type_variables c);
  let (nms,tps),fgs,pat = Term.remove_unused tps 0 empty_formals pat in
  Asexp(e,tps,pat)



let evaluated_as_expression (t:term) (c:Context.t): term =
  (*
    If an as expression allows a partial match e.g.

        (a,b) as (0, successor(_))

    then the evaluation returns the splitted as expression

        a as 0  and  b as successor(_)

    instead of evaluating it directly to

        some(n) (a,b) = (0, successor(n))
   *)
  match t with
  | Asexp(e,tps,pat) ->
     let n = Array.length tps in
     let nms = anon_argnames n in
     let rec collect
               (e:term) (pat:term) (lst:(term*term) list): (term*term) list =
       match e, pat with
       | VAppl(i,args1,_,_), VAppl(j,args2,_,_) when i +  n = j ->
          let len = Array.length args1 in
          assert (len = Array.length args2);
          if len = 0 then
            (e,pat)::lst
          else
          interval_fold
            (fun lst k -> collect args1.(k) args2.(k) lst)
            lst 0 len
       | _ ->
          (e,pat)::lst
     in
     begin
       match collect e pat [] |> List.rev with
       | [] ->
          assert false (* cannot happen; at least one pair must be present *)
       | [e0,pat0] ->
          assert (Term.equivalent e e0);
          assert (Term.equivalent pat pat0);
          evaluated_primary_as_expression e n tps pat c
       | (e0,pat0) :: rest ->
          List.fold_left
            (fun res (e0,pat0) ->
              Context.and_term
                res
                (make_as_expression e0 (nms,tps) pat0 c)
                c
            )
            (make_as_expression e0 (nms,tps) pat0 c)
            rest
     end
  | _ ->
     assert false (* Not an as expression *)
