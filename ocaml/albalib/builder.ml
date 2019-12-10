open Fmlib
open Common


module Parser     = Parser_lang
module Expression = Parser.Expression
module Position   = Character_parser.Position


type pos = Position.t

type range = pos * pos

module Located =
  Character_parser.Located




module GSub =
  (* Gamma with substitions *)
  struct
    type t = {gamma: Gamma.t; substitutions: (Term.t * int) option array}

    let make (gamma:Gamma.t): t =
      {gamma; substitutions = [||]}


    let gamma (c:t): Gamma.t = c.gamma

    let count (c:t) = Gamma.count c.gamma

    let count_substitutions (c:t): int =
      Array.length c.substitutions

    let base_count (c:t): int =
      count c - count_substitutions c

    let level_of_index (i:int) (c:t): int =
      Term.bruijn_convert i (count c)

    let index_of_level (i:int) (c:t): int =
      Term.bruijn_convert i (count c)


    let push_substitutable (typ: Term.typ) (c:t): t =
      let name = "<" ^ string_of_int (count c) ^ ">" in
      {gamma =
         Gamma.push_local name typ c.gamma;
       substitutions =
         Array.push None c.substitutions}


    (* [push_signature c1 nargs t c2] pushes the last [nargs] entries of [c1]
       into [c2] and transforms [t] into the new [c2].

       It is required that [c1] without the last [nargs] entries is an initial
       segment of [c2].  *)
    let push_signature
          (c0:t) (nargs:int) (t:Term.t)
          (c:t)
        : t * Term.t
      =
      let cnt0 = count c0 - nargs
      and cnt  = count c in
      assert (0 <= cnt0);
      assert (cnt0 <= cnt);
      let convert = Term.up_from (cnt - cnt0) in
      let c1 =
        Interval.fold
          c
          (fun i c ->
            let tp = Gamma.raw_type_at_level (cnt0 + i) c0.gamma in
            push_substitutable (convert i tp) c
          )
          0 nargs
      in
      c1, convert nargs t



    let has_substitution_at_level (level:int) (c:t): bool =
      let lsub = level - base_count c in
      assert (0 <= lsub);
      c.substitutions.(lsub) <> None



    let substitute_at_level (level:int) (t:Term.t) (c:t): t =
      (* [substitute_at_level i t c]. Substitute the variable at level [i] with
     the term [t] in the context [c].

     Precondition: It has to be a substitutable at level [i] which does not
     yet have any substitution.
       *)
      assert (not (has_substitution_at_level level c));
      let cnt = count c
      and cnt0 = base_count c
      in
      let idx = Term.bruijn_convert level cnt
      and lsub = level - cnt0
      in
      assert (0 <= lsub);
      let subs = Array.copy c.substitutions in
      for i = 0 to Array.length subs - 1 do
        if i = lsub then
          subs.(i) <- Some (t, cnt)
        else
          subs.(i) <-
            Option.map
              (fun (ti,n) ->
                Term.substitute
                  (fun j ->
                    let j1 = j + cnt - n in
                    if j1 = idx then
                      t
                    else
                      Term.Variable j1)
                  ti,
                cnt (* substitution valid in the outer context. *)
              )
              subs.(i)
      done;
      {c with substitutions = subs}



    let substitution_at_level (level:int) (c:t): Term.t =
      (* in the base context, all variables must be substituted. *)
      let cnt = count c
      and cnt0 = base_count c
      in
      assert (cnt0 <= level);
      assert (level < cnt);
      match c.substitutions.(level - cnt0) with
      | None ->
         assert false (* Illegal call *)
      | Some (t,n) ->
         assert (cnt0 <= n);
         match Term.down (n - cnt0) t with
         | None ->
            assert false (* Illegal call *)
         | Some t ->
            t


    let is_all_substituted (c:t): bool =
      let csub = count_substitutions c in
      let res = ref true
      and i = ref 0 in
      while !res && !i < csub do
        if c.substitutions.(!i) = None then
          res := false
        else
          i := !i + 1
      done;
      !res


    let substitution_at_index (i:int) (c:t): Term.t option =
      (* in the current context *)
      let n_subs = Array.length c.substitutions
      and cnt = count c
      in
      assert (i < n_subs);
      Option.map
        (fun (t,n) ->
          assert (n <= cnt);
          Term.up (cnt - n) t)
        c.substitutions.(Term.bruijn_convert i n_subs)



    let substitute_at_index (i:int) (t:Term.t) (c:t): t =
      substitute_at_level (level_of_index i c) t c



    (* [unify t u c] unifies the term [t] with the term [u] and generates
       substitutions such that [t] and [u] with the substitutions applied are
       equivalent terms. Return a new context containing new substitutions if
       the terms are unifiable, otherwise return [None]. *)
    let unify (t:Term.t) (u:Term.t) (c:t): t option =
      let rec unify t u exact c =
        let n_subs = Array.length c.substitutions
        in
        let open Term
        in
        match t, u with
        | Variable i, _ when i < n_subs ->
           Option.(
            unify
              (Gamma.type_at_level (level_of_index i c) c.gamma)
              (Gamma.type_of_term u c.gamma)
              false
              c
            >>= fun c ->
            match
              substitution_at_index i c
            with
            | None ->
               Some (substitute_at_index i u c)
            | Some t_sub ->
               unify t_sub u exact c)

        | _, Variable i when i < n_subs ->
           unify u t exact c

        | Sort s1, Sort s2
             when (exact && s1 = s2) || (not exact && Sort.is_super s1 s2) ->
           Some c

        | Variable i, Variable j when i = j ->
           Some c

        | Appl (_, _, _ ), Appl (_, _, _ ) ->
           assert false (* nyi *)

        | Pi (_, _, _), Pi (_, _, _) ->
           assert false (* nyi *)

        | _, _ ->
           None
      in
      unify t u true c

  end (* GSub *)











type required =
  GSub.t     (* Context with placeholders with required types *)

  * int list  (* Positions of the placeholders for not yet built arguments. *)


type actual =
  GSub.t     (* Context with placeholders for the arguments (there might be
                 zero arguments). The context below the arguments is the base
                 context. *)

  * int list  (* Positions of the placeholders for the arguments *)

  * Term.t    (* Term of the form [<0> + <1>] or [f <0> <1> <2> ... ]
                 representing the expression to be built where placeholders
                 are used instead of the arguments because the arguments are
                 not yet built.  *)


(* Problems:

   Function expression:

   - More actual arguments than formal arguments.

   - Required type is not a function type with sufficient arguments.

 *)


module Problem =
  struct
    type t =
      | Overflow of range
      | No_name of range
      | Not_enough_args of range * int * actual list
      | None_conforms of range * required list * actual list
      | Not_yet_implemented of range * string
  end


module Result = Monad.Result (Problem)


module Print  (P:Pretty_printer.SIG) =
  struct
    let required ((c,lst):required): P.t
      (* Print the required type of the next argument (type of the topmost
         placeholder). *)
      =
      let c = GSub.gamma c in
      match lst with
      | [] ->
         assert false (* cannot happen *)
      | i :: _ ->
         let module PP = Gamma.Pretty (P) in
         PP.print (Gamma.type_at_level i c) c

    let actual ((c,_,t):actual): P.t
      (* Print the actual term and its type [t:T] where the term contains
         placeholders for the arguments. *)
      =
      let c = GSub.gamma c in
      let module PP = Gamma.Pretty (P) in
      P.(PP.print t c
         <+> string ": "
         <+> PP.print
               (Gamma.type_of_term t c)
               c)
  end



(* Function Expression "\ x y ... := exp"

   a) Required type is a placeholder without value:

   - Push A:Any, x:A, B:Any, y:B, ..., E:Any, e:E into the context - e is
   placeholder for "exp"

   - build [exp] and unify with [e]

   - make function expression and unify with the placeholder for the
   expression. References to types in the context must be kept.


   b) Required type has value:

   - Extract argtypes and result type and push x:A, y:B, ..., e:RT onto the
   context

   - build [exp] and unify with [e]

   - make function expression and unify with the placeholder for the
   expression. References to types in the context must be kept.


   Note: Substitutions are always done immediately, therefore type variables
   which have substitutions do no longer occur in other substitutions.

   If the arguments [x,y,...] with their types remain in the context, then the
   variables might occur in other types because we have dependent types.

*)


let find_name (name:string) (range:range) (c:Context.t): int list Result.t =
  match Context.find_name name c with
  | [] ->
     Error (Problem.No_name range)
  | lst ->
     Ok lst



let extract_args
      (nargs:int)                      (* Name is applied to [nargs] arguments
                                          *)
      (mode: Term.appl)                (* Mode of the application *)
      (base:Context.t)
      (range:range)                    (* Position of the name *)
      (lst: int list)                  (* Indices of the name (name might not
                                          be unique) *)
    : (actual list, Problem.t) result
  =
  let cnt = Context.count base
  in
  match
    List.map_and_filter
      (fun i ->
        Gamma.(
         Option.map
           (fun (gamma,_) ->
             GSub.make gamma,
             (Interval.fold
                []
                (fun i lst -> cnt + nargs - 1 - i :: lst)
                0 nargs),
             Term.(
               application
                 (Variable (index_of_level i gamma))
                 nargs
                 mode))
           (push_arguments
              nargs
              (type_at_level i (Context.gamma base))
              (Context.gamma base))))
      lst
  with
  | [] ->
     Error (Problem.Not_enough_args
              (range, nargs,
               List.map
                 (fun i ->
                   GSub.make (Context.gamma base),
                   [],
                   Gamma.term_at_level i (Context.gamma base))
                 lst
       ))
  | lst ->
     Ok lst


let unify
      (range: range)
      (base:Context.t)
      (reqs: required list)
      (actuals: actual list)
    : (required list, Problem.t) result
  =
  match
    List.(
    reqs >>= fun (gamma_req, req_lst) ->
    match req_lst with
    | [] ->
       assert false (* cannot happen *)
    | i_req :: req_lst ->
       actuals >>= fun (gamma_act, act_args, t) ->
       let cnt0 = Context.count base
       and cnt = GSub.count gamma_req
       in
       assert (cnt0 <= cnt);
       assert (cnt0 <= GSub.count gamma_act);
       let nargs = GSub.count gamma_act - cnt0 in
       let gsub, t =
         GSub.push_signature
           gamma_act nargs t
           gamma_req
       and req_lst =
         (List.map (fun i -> i + (cnt - cnt0)) act_args)
         @ req_lst
       in
       match
         GSub.(unify
                 (Term.Variable (index_of_level i_req gsub))
                 t
                 gsub)
       with
       | None ->
          []
       | Some gsub1 ->
          assert GSub.(count gsub = count gsub1);
          [gsub1, req_lst]
    )
  with
  | [] ->
     Error (Problem.None_conforms (range, reqs, actuals))
  | lst ->
     Ok lst


let term_of_name
      (name: string)
      (range: range)
      (nargs: int)
      (mode: Term.appl)
      (base: Context.t)
      (reqs: required list)
    : (required list, Problem.t) result
  =
  Result.(
    find_name name range base
    >>= extract_args nargs mode base range
    >>= unify range base reqs
  )


let term_of_number
      (number: string)
      (range: range)
      (base: Context.t)
      (reqs: required list)
    : (required list, Problem.t) result
  =
  let lst =
    Term.Value.number_values number
  in
  match lst with
  | [] ->
     Error (Problem.Overflow range)
  | _ ->
     unify
       range base reqs
       (List.map
          (fun v ->
            match v with
            | Term.Value.Int _ ->
               GSub.make (Context.gamma base),
               [],
               Term.Value v
            | _ ->
               assert false (* Cannot happen. *)
          )
          lst)


let rec build0
          (base:Context.t)
          (reqs: required list)
          (nargs:int)                (* [expr] has [nargs] actual arguments *)
          (mode: Term.appl)
          (expr:Parser.Expression.t) (* expression to be built *)
        : (required list, Problem.t) result
  =
  (* Build the term for [expr]. [reqs] is a list of contexts where the
     toplevel placeholder represents the expression [expr]. The expression
     [expr] must be able to receive [nargs] arguments. *)
  let open Parser.Expression in
  let range = Located.range expr
  in
  let gsub_base = GSub.make (Context.gamma base)
  in
  match
    Located.value expr
  with
  | Proposition ->
     unify range base reqs [gsub_base, [], Term.proposition]

  | Any ->
     unify
       range base reqs
       [gsub_base, [], Term.any]

  | Identifier name | Operator (name,_) ->
     term_of_name name range nargs mode base reqs

  | Number str ->
     assert (nargs = 0);
     term_of_number str range base reqs

  | Char code ->
     assert (nargs = 0);
     unify range base reqs
       [gsub_base, [], (Term.char code)]

  | String str ->
     assert (nargs = 0);
     unify range base reqs [gsub_base, [], (Term.string str)]

  | Binary (e1, op, e2) ->
     let name, _ = Located.value op
     and range  = Located.range op in
     Result.(
       term_of_name name range 2 Term.Binary base reqs
       >>= fun reqs ->
       build0 base reqs 0 Term.Normal e1
       >>= fun reqs ->
       build0 base reqs 0 Term.Normal e2
     )

  | Typed (_, _) ->
     Error (Problem.Not_yet_implemented (range, "typed expression"))

  | Function (_, _) ->
     Error (Problem.Not_yet_implemented (range, "function expression"))

  | Parenthesized e ->
     build0 base reqs nargs mode e


let build
      (expr:Parser.Expression.t)
      (c:Context.t)
    : ((Term.t*Term.typ) list, Problem.t) result
  =
  let cnt = Context.count c
  in
  Result.map
    (fun lst ->
      List.map
        (fun (gsub, req_lst) ->
          assert (req_lst = []);
          assert (cnt + 2 <= GSub.count gsub);
          assert (GSub.is_all_substituted gsub);
          GSub.(substitution_at_level (cnt + 1) gsub,
                 substitution_at_level cnt gsub)
        )
        lst
    )
    (build0
       c
       [GSub.(Context.gamma c
              |> make
              |> push_substitutable (Term.Sort (Term.Sort.Any 2))
              |> push_substitutable (Term.Variable 0))
       , [cnt + 1]]
       0
       Term.Normal
       expr)
