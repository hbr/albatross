(* Term building function

   Input: syntactic term + context

   Output: list of (term, type) pairs or an error message.

   Examples:

      3 + 5: Int, 3 + 5: Natural, ...

      "h": String

      'c': Character

      List: Any -> Any

      []: all (A: Any): List A

      (^): all (A: Any): A -> List A -> List A

      identity: all (A: Any): A -> A

   We reject all terms with bound variables where the type of the bound
   variables cannot be inferred.

   Example:

      \ a b := a = b

      Must be rejected, because (=) has the type

         all (A: Any): A -> A -> Proposition

   The term \ (a:Int) b := a = b is accepted.
 *)





(* Principles of Term Building

   Each (sub)term gets a placeholder which represents the term.

   Each bound variable gets one placeholder for its type and an entry for the
   variable.

   If the type of any (sub)term / bound variable is known, its placeholder for
   the type gets an immediate substitution.

   Internal builder function:

   Input:

   - syntactic expression to be built

   - number of explicit arguments to which the expression is applied

   - name map to find the index / indices of names

   - list of pairs (ptr, substitution gamma) where ptr points to the
   placeholder representing the term to be constructed.

   Output:

   - list of pairs (ptr array, substitution gamma) where the pointer array
   points to the placeholders for the explicit arguments

   - or an error indication

 *)


(* Possible Errors:

   - A number is to large or to small to be represented by a number type.

   - A function or operator name cannot be found in the name map.

   - The types of all constructed terms, before applying them to the
   arguments, are not function types with enough arguments.

   - The types of all constructed terms, after applying them to the arguments,
   are not unifiable with the expected result type.
 *)

(*
    I was expecting a term which returns after application to n arguments a
    value of one of the types

        R1, R2, ....

    but the term has one of the types

        f _ _ _ :T1, f _ _ _ :T2, ...


    I was expecting a term which returns after application to n arguments a
    certain type. But none of the following combinations work:

       Return type:    R1
       Term type:      all (x:A) (y:B) ... : T1

       Return type:    R2
       Term type:      all (x:A) (y:B) ... : T2

       ...

       or
       Return type:    R3
       Term            f _ _ _ _ : T3


    I was expecting a function which can accept n arguments, but the term has
    the types

        T1, T2,  ...

 *)




(* Identifier or operator

   Input:

   - pointer to placeholder

   - [n] explicit arguments

   Output:

   - placeholder substituted by f <a0> <a1> ... <am-1> where m is the number
   of explicit and implict arguments.

   - array of pointers to the placeholders of the n explicit arguments


   Algorithm:

   From the name map we get a list of indices (or levels).

   Each index represents a global or local variable which has a type according
   to the context gamma.

   The type in key normal form must look like

     all (x1:A1) ... (xk:Ak): Rk

   where n <= k and k include all implicit arguments which occur before the n
   explicit arguments.

   Compare Rk with the required type R. If R is not a placeholder and starts
   with fewer implicit arguments than Rk we extract the difference from Rk to
   get

     all (x1:A1) ... (xk:Ak) ... (xm:Am): Rm

   Otherwise we set m = k.

   Form the new context

      Gamma, x1:A1, ... , xm:Am

   with the new placeholders x1,..., xm.

   Unify Rm with R. And do the substitution

     e := f <x1> ... <xm>

   where e is the placeholder for the expression and f is a variable for the
   function name.

   and return an array pointing to the placeholders representing explicit
   arguments.  *)




(* Function Expression "(\ x y ... := exp) a1 a2 ... an"

   Some arguments are typed, some are untyped. The result type of the lambda
   abstraction might be there or not.

   There are [nargs] arguments to which the function term is applied.

   A fully typed lambda abstraction looks like

     \ (x:A) (y:B) ... : RT := exp

   First the signature is analyzed. The untyped arguments get placeholders for
   their types without substitutions, the typed arguments get placeholders with
   substitutions.

     gamma, A:U, x:A, B:U, y:B ...

   Type variables which occur in other types which are not propositions are
   implicit. However if they occur in other types, their types get
   substitutions i.e. can be treated as typed variables.

   The expected type of the lambda abstraction applied to the arguments cannot
   give any information for the types of formal arguments which correspond to
   the arguments to which the lambda abstraction is applied. Task: Find the
   number of formal arguments which correspond to actual arguments.

   Number of formal arguments corresponding to actual arguments:

   - Number of actual arguments + Number of implicit arguments (type args +
   proof args)

   - Scan from left to right, not counting implicit args until sufficient
   formal args have been found.

   - Error if there are not sufficient formal args to cover all actual args.


   After covering all actual args there are remaining args (>= 0)

      \ u v ... := exp

   The expected type E of the whole lambda term applied to the actual
   arguments must be the expected type of the remaining lambda abstraction. If
   E is a dummy, then we cannot gain any information. If E is not a dummy, its
   signature must have sufficient arguments for the remaining formal
   arguments. The argument types derived from E must be unifiable with the
   types of the formal arguments.

*)

open Fmlib
open Common


module Parser     = Parser_lang
module Expression = Parser.Expression
module Position   = Character_parser.Position


type pos = Position.t

type range = pos * pos

module Located =
  Character_parser.Located




module Explicits =
  struct
    type t =
      | No
      | Normal of int

    let normal (nargs: int): t =
      Normal nargs

    let empty: t =
      No

    let count (e: t): int =
      match e with
      | No ->
         0
      | Normal n ->
         n

    let has (e: t): bool =
      0 < count e
  end







module GSub =
  (* Gamma with substitions *)
  struct
    type t = {base: Gamma.t; substitutions: (Term.t * int) option array}

    let make (base: Gamma.t): t =
      {base; substitutions = [||]}


    let base (c:t): Gamma.t = c.base

    let count (c:t) = Gamma.count c.base

    let count_substitutions (c:t): int =
      Array.length c.substitutions

    let is_placeholder (c: t) (idx: int): bool =
      idx < count_substitutions c  (* must be changed for bound variables!!! *)

    let base_count (c:t): int =
      count c - count_substitutions c

    let level_of_index (i:int) (c:t): int =
      Term.bruijn_convert i (count c)

    let index_of_level (i:int) (c:t): int =
      Term.bruijn_convert i (count c)


    let type_of_term (t: Term.t) (c: t): Term.typ =
      Gamma.type_of_term t c.base

    let type_at_level (i: int) (c:t): Term.typ =
      Gamma.type_at_level i c.base



    let push_substitutable (typ: Term.typ) (c:t): t =
      let name = "<" ^ string_of_int (count c) ^ ">" in
      {base =
         Gamma.push_local name typ c.base;
       substitutions =
         Array.push None c.substitutions}


    let push_bound (_: string) (_: Term.typ) (_: t): t =
      assert false (* nyi *)


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
            let tp = Gamma.raw_type_at_level (cnt0 + i) c0.base in
            push_substitutable (convert i tp) c
          )
          0 nargs
      in
      c1, convert nargs t



    let has_substitution_at_level (level:int) (c:t): bool =
      let lsub = level - base_count c in
      assert (0 <= lsub);
      c.substitutions.(lsub) <> None



    let add_substitution_at_level (level:int) (t:Term.t) (c:t): t =
      (* [add_substitution_at_level i t c]. Substitute the variable at level
         [i] with the term [t] in the context [c].

         Precondition: It has to be a substitutable at level [i] which does
         not yet have any substitution.  *)
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


    let add_substitution_at_index (i:int) (t:Term.t) (c:t): t =
      add_substitution_at_level (level_of_index i c) t c



    let substitution_at_level (level:int) (c:t): Term.t option =
      (* require: there is a substitutable at [level] *)
      let cnt = count c
      and cnt0 = base_count c
      in
      if level < cnt0 then
        assert false (* Illegal call, [level] is not a placeholder *)
      else
        Option.map
          (fun (t, n) ->
            assert (n <= cnt);
            Term.up (cnt - n) t)
          (c.substitutions.(level - cnt0))


    let substitution_at_level_in_base (level:int) (c:t): Term.t =
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


    let to_base (t: Term.t) (c: t): Term.t option =
      (* Transform [t] into the base context. Only possible if it does not
         contain any placeholders or new local variables. *)
      Term.down (count c - base_count c) t


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


    let substitution (c:t) (i:int): Term.t option =
      (* in the current context *)
      let n_subs = Array.length c.substitutions
      and cnt = count c
      in
      if i < n_subs then
        Option.map
          (fun (t,n) ->
            assert (n <= cnt);
            Term.up (cnt - n) t)
          c.substitutions.(Term.bruijn_convert i n_subs)
      else
        Some (Variable i)


    let substitute (c: t) (term: Term.t): Term.t =
      Term.substitute
        (fun i ->
          match substitution c i with
          | None ->
             Variable i
          | Some t ->
             t)
        term




    let unify (t:Term.t) (u:Term.t) (c:t): t option =
      (* [unify t u c] unifies the term [t] with the term [u] and generates
         substitutions such that [t] and [u] with the substitutions applied
         are equivalent terms. Return a new context containing new
         substitutions if the terms are unifiable, otherwise return [None]. *)
      let rec unify t u exact c =
        let n_subs = Array.length c.substitutions
        in
        let open Term
        in
        match t, u with
        | Variable i, _ when i < n_subs ->
           Option.(
            unify
              (Gamma.type_at_level (level_of_index i c) c.base)
              (Gamma.type_of_term u c.base)
              false
              c
            >>= fun c ->
            match
              substitution c i
            with
            | None ->
               Some (add_substitution_at_index i u c)
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



    let signature (c: t) (tp: Term.typ): Signature.t =
      Gamma.signature c.base tp


    let push_explicits
          (explicits: Explicits.t) (term: Term.t) (sign: Signature.t) (c: t)
        : Term.t * Signature.t * t * int list
      =
      let push explicits term sign c ptr_lst =
        if Explicits.has explicits then
          assert false
        else
          term, sign, c, ptr_lst
      in
      let term, sign =
        let n_up = count c - Signature.base_count sign in
        assert (0 <= n_up);
        Term.up n_up term,
        Signature.up n_up sign
      in
      push explicits term sign c []



    let push_implicits
          (_: int) (_: Term.t) (_: Signature.t) (_: t)
        : Term.t * Signature.t * t
      =
      assert false (* nyi *)

    let count_first_implicits (sign: Signature.t) (c: t): int option =
      let n = Signature.count_first_implicits sign in
      if n = 0 then
        match substitute c (Signature.typ sign) with
        | Term.Variable i when is_placeholder c i ->
           None
        | _ ->
           Some 0
      else
        Some n


    let push_argument_placeholders
          (explicits: Explicits.t)
          (term: Term.t)    (* valid in the context of [act_sign] *)
          (act_sign: Signature.t)
          (req_sign: Signature.t)
          (c: t)
        : Term.t * Signature.t * int list * t
      (* The returned term is valid in the returned context *)
      =
      let term, act_sign, c, ptr_array =
        push_explicits explicits term act_sign c
      in
      let term, act_sign, c =
        let n_req = Signature.count_first_implicits req_sign
        in
        match
          count_first_implicits act_sign c
        with
        | Some n_act when n_req < n_act ->
           push_implicits (n_act - n_req) term act_sign c
        | _ ->
           term, act_sign, c
      in
      term, act_sign, ptr_array, c


    let remove_last (n: int) (c: t): t =
      { base = Gamma.remove_last n c.base;
        substitutions = Array.remove_last n c.substitutions}


    let unify_signatures
          (act_sign: Signature.t)
          (req_sign: Signature.t)
          (c: t): t option
      =
      if Signature.count_arguments act_sign
         = Signature.count_arguments req_sign
      then
        let rec uni act req n c =
          match Signature.pop act, Signature.pop req with
          | None, None ->
            (* Result type found. *)
            Option.map
              (remove_last n)
              (unify (Signature.typ act) (Signature.typ req) c)
          | Some (act_arg, act), Some (req_arg, req) ->
            Option.(
              unify act_arg req_arg c >>= fun c ->
              uni act req (n + 1) (push_bound "_" act_arg c)
            )
          | _ ->
            assert false (* cannot happen, both signatures have the
                            same number of arguments *)
        in
        uni act_sign req_sign 0 c
      else
        None

  end (* GSub *)









(***************** New Builder ******************************************)



type typ = Term.typ * Gamma.t

type required_type = typ
type candidate_type = typ


type problem =
  | Overflow of range
  | No_name of range
  | Not_enough_args of range * int * candidate_type list
  | None_conforms of range * int * required_type list * candidate_type list


module Required =
  struct
    type t = {
        stack: int list;
        gamma:  GSub.t
      }

    let base (c: t): GSub.t =
      c.gamma


    let top (c: t): int =
      match c.stack with
      | h :: _ ->
         h
      | _ ->
         assert false (* Illegal call! *)


    let top_type (c:t): Term.typ =
      GSub.type_at_level (top c) c.gamma


    let count (c: t): int =
      GSub.count c.gamma


    let make (gamma: GSub.t): t =
      {gamma =
         GSub.(gamma
               |> push_substitutable (Term.Sort (Term.Sort.Any 2))
               |> push_substitutable (Term.Variable 0));
       stack = [GSub.count gamma + 1]}


    let unify_candidate
          (c: t)
          (term: Term.t)      (* Valid in the same context as [act_sign] *)
          (act_sign: Signature.t)
          (explicits: Explicits.t)
        : t option
      =
      (* before: stack = ptr rest
                 ptr without substitution

         after:  stack =  arg1 ... argn ptr rest
                 ptr substituted *)
      let ptr = top c
      in
      let req_sign = GSub.(signature c.gamma (type_at_level ptr c.gamma))
      in
      let term, act_sign, ptrs_rev, gsub =
        GSub.push_argument_placeholders
          explicits
          term
          act_sign
          req_sign
          c.gamma
      in
      let open Option in
      let open GSub in
      unify_signatures act_sign req_sign gsub >>= fun gsub ->
      Some
        {gamma =
           add_substitution_at_level ptr term gsub;
         stack =
           List.rev_append ptrs_rev c.stack}


    let start_typed_term (c: t): t =
      let ptr = top c
      and cnt = count c
      in
      let sort =
        GSub.(type_of_term (type_at_level ptr c.gamma) c.gamma) in
      let gam = GSub.push_substitutable sort c.gamma in
      let gam = GSub.push_substitutable (Term.Variable 0) gam in
      {gamma =
         GSub.add_substitution_at_level
           ptr
           Term.(Typed (Variable 0, Variable 1)) gam;
       stack = cnt + 1 :: cnt :: c.stack}


    let unify_typed_term (_: t): t option =
      (* A typed term is an expression of the form [exp_inner: tp]. Its
         placeholder at [exp] is not yet substituted.

         stack: tp exp_inner exp ...

         - unify the type at [tp] with the required type of the placeholder
         [exp].

         - substitute [exp] by [Typed (exp_inner, tp)]

         - pop tp

         stack: exp_inner exp ...

       *)
      assert false (* nyi *)


    let end_typed_term (_: t): t =
      (* typed term [exp_inner: tp]

         stack: exp_inner exp ...

         - pop exp_inner

         stack: exp ...
       *)
      assert false (* nyi *)


    let substitution_in_base (level:int) (c: t): Term.t option =
      (* At [level] there must be a substitutable which has a substitution.
         Transform the substitution to the base context or return [None],
         if it still contains placeholders. *)
      GSub.(
        match substitution_at_level level c.gamma with
        | None ->
          assert false (* Illegal call, [level] does not have a
                          substitution. *)
        | Some term ->
          to_base term c.gamma
      )
  end (* Required *)





module Build_context =
  struct
    module Name_map = Context.Name_map
    module Result = Monad.Result (struct type t = problem end)

    type t = {
        names: Name_map.t;
        base:  Gamma.t;
        explicits: Explicits.t;
        reqs:  Required.t list;
      }

    let make (c:Context.t): t =
      {names = Context.name_map c;
       base  = Context.gamma c;
       explicits = Explicits.empty;
       reqs  = [Required.make (GSub.make (Context.gamma c))]}



    let pop_top (_: t): t =
      assert false (* nyi *)

    let required_types (c: t): typ list =
      List.map
        (fun req ->
          Required.top_type req,
          GSub.base (Required.base req)
        )
        c.reqs


    let unify_base_candidates
          (range: range)
          (candidates: (Term.t * Signature.t) list)
          (c: t)
        : (t, problem) result
      =
      let reqs =
        List.(
          c.reqs >>= fun req ->
          let uni = Required.unify_candidate req in
          candidates >>= fun (term, act_sign) ->
          Option.to_list (uni term act_sign c.explicits)
        )
      in
      if reqs = [] then
        Error
          (None_conforms
             (range,
              Explicits.count c.explicits,
              required_types c,
              List.map
                (fun (_,sign) -> Signature.typ sign, c.base)
                candidates))
      else
        Ok {c with reqs}




    let check_base_terms
          (range: range)
          (terms: Term.t list) (* all valid in the base context *)
          (c: t)
        : (t, problem) result
      =
      assert (terms <> []);
      let gam = GSub.make c.base
      in
      let candidates =
        List.map_and_filter
          (fun t ->
            let s  =
              GSub.(signature gam (type_of_term t gam)) in
            let n  = Signature.count_explicit_args s in
            if n < Explicits.count c.explicits then
              None
            else
              Some (t, s))
          terms
      in
      if candidates = [] then
        let tps =
          List.map (fun t -> Gamma.type_of_term t c.base, c.base) terms
        in
        Error
          (Not_enough_args (range, Explicits.count c.explicits, tps))
      else
        unify_base_candidates range candidates c


    let build_proposition (range: range) (c: t): (t, problem) result
      =
      check_base_terms
        range
        [Term.proposition]
        c


    let build_any (range: range) (c: t): (t, problem) result =
      check_base_terms
        range
        [Term.any]
        c


    let build_name (range: range) (name: string) (c:t): (t, problem) result =
      match
        Name_map.find name c.names
      with
      | [] ->
         Error (No_name range)

      | [i] when Gamma.count c.base <= i ->
         assert false (* nyi *)

      | level_lst ->
         check_base_terms
           range
           (List.map (fun i -> Gamma.term_at_level i c.base) level_lst)
           c


    let build_number (range: range) (str: string) (c:t): (t, problem) result =
      match Term.number_values str with
      | [] ->
         Error (Overflow range)
      | terms ->
         check_base_terms
           range
           terms
           c


    let build_string (range: range) (str: string) (c:t): (t, problem) result =
      check_base_terms
        range
        [Term.string str]
        c


    let build_char (range: range) (code: int) (c:t): (t, problem) result =
      check_base_terms
        range
        [Term.char code]
        c


    let start_typed_term (c: t): t =
      {c with
        reqs =
          List.map Required.start_typed_term c.reqs
      }


    let unify_typed_term (c: t): (t, problem) result =
      match
        List.map_and_filter Required.unify_typed_term c.reqs
      with
      | [] ->
         assert false (* nyi error message *)
      | reqs ->
         Ok {c with reqs}


    let end_typed_term (c: t): t =
      {c with
        reqs =
          List.map Required.end_typed_term c.reqs
      }


    let rec build0_new
              (exp:Parser.Expression.t)
              (explicits: Explicits.t)
              (c: t)
            : (t, problem) result
      =
      (* Build the expression [exp] according to the type of the top
         placeholder.

         After successful build, the expression is stored in the top
         placeholder.  The stack of placeholders is not modified, only the top
         one has got a substitution. *)
      let open Parser.Expression
      in
      let range = Located.range exp
      in
      match Located.value exp with
      | Proposition ->
         build_proposition range c

      | Any ->
         build_any range c

      | Identifier name | Operator (name, _) ->
         build_name range name c

      | Number str ->
         build_number range str c

      | Char code ->
         build_char range code c

      | String str ->
         build_string range str c

      | Binary (_, _, _) ->
         assert false (* nyi *)

      | Typed (inner, tp) ->
         let c = start_typed_term c
         in
         Result.(
           map
             end_typed_term
             (return (start_typed_term c)
              >>= build0_new tp Explicits.empty
              >>= unify_typed_term
              >>= build0_new inner Explicits.empty)
         )

      | Application (f, args) ->
         assert (args <> []);
         let module Fold = List.Monadic_fold (Result) in
         Result.(
           build0_new
             f
             (Explicits.normal (List.length args))
             c
           >>= Fold.fold_left
                 (fun arg c ->
                   map
                     pop_top
                     (build0_new arg Explicits.empty c))
                 args
         )

      | Function (_, _, _) ->
         assert false (* nyi *)

      | Parenthesized exp ->
         build0_new exp explicits c


    let to_base_context
          (c: t)
        : ((Term.t * Term.typ) list, problem) result
      =
      assert (c.reqs <> []);
      let cnt0 = Gamma.count c.base
      in
      let lst =
        List.map_and_filter
          (fun req ->
            assert (cnt0 + 2 <= Required.count req);
            Option.(
              Required.(
                substitution_in_base (cnt0 + 1) req >>= fun t ->
                Printf.printf "term found %s\n" (Gamma.string_of_term t c.base);
                substitution_in_base cnt0 req >>= fun tp ->
                Printf.printf "type found %s\n" (Gamma.string_of_term tp c.base);
                Some (t, tp))))
          c.reqs
      in
      if lst = [] then
        assert false (* nyi *)
      else
        Ok lst


let build
          (exp:Parser.Expression.t)
          (c:Context.t)
        : ((Term.t * Term.typ) list, problem) result
      =
      Result.( build0_new exp Explicits.empty (make c)
               >>= to_base_context )
  end (* Build_context *)













let build_new
      (exp:Parser.Expression.t)
      (c:Context.t)
    : ((Term.t * Term.typ) list, problem) result
  =
  Build_context.build exp c









(***************** Old Builder ******************************************)

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
    module PP = Gamma.Pretty (P)

    let required ((c,lst):required): P.t
      (* Print the required type of the next argument (type of the topmost
         placeholder). *)
      =
      let c = GSub.base c in
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
      let c = GSub.base c in
      let module PP = Gamma.Pretty (P) in
      P.(PP.print t c
         <+> string ": "
         <+> PP.print
               (Gamma.type_of_term t c)
               c)

      let typ ((tp,gamma): typ): P.t =
        PP.print tp gamma

      let required_type = typ
      let candidate_type = typ
  end



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

  | Application _ ->
     Error (Problem.Not_yet_implemented (range, "function application"))

  | Function (_, _, _) ->
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
          GSub.(substitution_at_level_in_base (cnt + 1) gsub,
                 substitution_at_level_in_base cnt gsub)
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
