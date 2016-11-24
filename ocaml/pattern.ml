open Term
open Container
open Support

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
  (* Unify the term [t] with the pattern [n,pat]. The term an pattern above its
     pattern variables come from an environment with [nb] variables.

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
