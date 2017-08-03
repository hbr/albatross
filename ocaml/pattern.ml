open Term
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



let unify_with_pattern
    (t:term) (n:int) (pat:term) (nb:int) (ft:FT.t)
    : arguments =
  (* Unify the term [t] with the pattern [n,pat]. The term and pattern above
     its pattern variables come from an environment with [nb] variables.

     Three cases are possible:

     (a) The term can be matched with the pattern. Then a substitution is
     returned which applied to the pattern makes it equivalent to the
     term. The term is then an instance of the pattern.

     (b) The term can definitely not matched with the pattern because there
     are conflicting constructors at the corresponding positions. The
     Exception [Reject] is raised

     (c) The term might match the pattern, but it cannot be decided because
     there is not enough information in the term. The exception [Undecidable]
     is raised.
   *)
  let args = Array.make n empty_term
  in
  let is_constr i =
    assert (nb <= i);
    FT.is_constructor (i-nb) ft
  in
  let do_sub i t =
    if args.(i) = empty_term then
      args.(i) <- t
    else if not (Term.equivalent args.(i) t) then
      raise Reject
  in
  let rec uni (t:term) (pat:term): unit =
    let uniargs args1 args =
      let nargs = Array.length args1 in
      assert (nargs = Array.length args);
      let undecidable =
        Container.interval_fold
          (fun undec i ->
            try
              uni args1.(i) args.(i);
              undec
            with Undecidable ->
              true
          )
          false 0 nargs
      in
      if undecidable then raise Undecidable
    in
    match t, pat with
      _, Variable i ->
        assert (i < n);
        do_sub i t
    | VAppl(i1,args1,ags1,_), VAppl(i,args,ags,_) when is_constr i1 ->
        if i1 + n <> i then
          raise Reject;
        uniargs args1 args
    | _ ->
        raise Undecidable
  in
  uni t pat;
  args


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
