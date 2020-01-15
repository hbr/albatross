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
    type t = {
      args: (Expression.t * Expression.argument) list;
      nargs: int
    }

    let to_term_appl arg_appl =
      match arg_appl with
      | Expression.Normal ->
          Term.Normal
      | Expression.Operand ->
          Term.Binary

    let empty: t =
      {args = []; nargs = 0}

    let make args: t =
      {args; nargs = List.length args}

    let count (e: t): int =
      e.nargs

    let has (e: t): bool =
      0 < count e

    let pop (e: t): Term.appl * t =
      match e.args with
      | [] ->
        assert false (* Illegal call! *)
      | (_, arg_appl) :: args ->
        to_term_appl arg_appl,
        { args; nargs = e.nargs - 1}
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

    let is_placeholder (idx: int) (c: t): bool =
      idx < count_substitutions c  (* must be changed for bound variables!!! *)


    let base_count (c:t): int =
      count c - count_substitutions c


    let index_of_level (i:int) (c:t): int =
      Term.bruijn_convert i (count c)


    let level_of_index (i:int) (c:t): int =
      Term.bruijn_convert i (count c)


    let variable_of_level (level: int) (gsub: t): Term.t =
      Term.Variable (index_of_level level gsub)


    let type_of_term (t: Term.t) (c: t): Term.typ =
      Gamma.type_of_term t c.base


    let type_at_level (i: int) (c:t): Term.typ =
      Gamma.type_at_level i c.base


    let string_of_term (t: Term.t) (c: t): string =
      let module P = Term_printer.String_print (Gamma) in
      P.string_of_term t c.base

    let _ = string_of_term


    let push_substitutable (typ: Term.typ) (c:t): t =
      let name = "<" ^ string_of_int (count_substitutions c) ^ ">" in
      {base =
         Gamma.push_local name typ c.base;
       substitutions =
         Array.push None c.substitutions}


    let push_bound (_: string) (_: Term.typ) (_: t): t =
      assert false (* nyi *)



    let has_substitution_at_level (level:int) (c:t): bool =
      let lsub = level - base_count c in
      assert (0 <= lsub);
      c.substitutions.(lsub) <> None


    let has_substitution (idx: int) (c: t): bool =
      assert (is_placeholder idx c);
      has_substitution_at_level (level_of_index idx c) c


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


    let substitution_at_level_safe (level: int) (gsub: t): Term.t =
      (* precondition: There is a substitutable at [level] which has a
      substitution. *)
      match substitution_at_level level gsub with
      | None ->
          assert false (* Illegal call! *)
      | Some term ->
          term


    let to_base (t: Term.t) (c: t): Term.t option =
      (* Transform [t] into the base context. Only possible if it does not
         contain any placeholders or new local variables. *)
      Term.down (count c - base_count c) t


    let substitution (i:int) (c:t): Term.t option =
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


    let substitute (term: Term.t) (c: t): Term.t =
      Term.substitute
        (fun i ->
          match substitution i c with
          | None ->
             Variable i
          | Some t ->
             t)
        term




    let unify (t:Term.t) (is_super: bool) (u:Term.t) (c:t): t option =
      (* [unify t u c] unifies the term [t] with the term [u] and generates
         substitutions such that [t] and [u] with the substitutions applied
         are equivalent terms. Return a new context containing new
         substitutions if the terms are unifiable, otherwise return [None]. *)
      let rec unify t is_super u c =
        let type_of_variable i = Gamma.type_of_variable i c.base
        in
        let unify_variable i term =
          Option.(unify (type_of_variable i) true
                        (Gamma.type_of_term term c.base)
                        c
                  >>= fun c ->
                  Some (add_substitution_at_index i term c))
        in
        let open Term
        in
        match t, u with
        | Variable i, Variable j
          when is_placeholder i c && is_placeholder j c
          ->
            assert (not (has_substitution i c));
            assert (not (has_substitution j c));
            ( match unify_variable i u with
              | None ->
                  unify_variable j t
              | Some c ->
                  Some c )

        | Variable i, _ when is_placeholder i c ->
            assert (not (has_substitution i c));
            unify_variable i u

        | _, Variable j when is_placeholder j c ->
            assert (not (has_substitution j c));
            unify_variable j t

        | Sort s1, Sort s2
             when (not is_super && s1 = s2) || (is_super && Sort.is_super s1 s2) ->
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
      unify (substitute t c) is_super (substitute u c) c



    let signature (c: t) (tp: Term.typ): Signature.t =
      Gamma.signature c.base tp


    let push_implicits
          (n: int)
          (term: Term.t)
          (sign: Signature.t)
          (c: t)
        : Term.t * Signature.t * t
      =
      assert (n <= Signature.count_first_implicits sign);
      let push_one (term, sign, c) =
        let arg_tp, sign = Signature.pop_safe sign in
        Term.(Appl (up1 term, Variable 0, Implicit)),
        sign,
        push_substitutable arg_tp c
      in
      Int.iterate n push_one (term, sign, c)


    let push_explicits
          (explicits: Explicits.t)
          (term: Term.t)
          (sign: Signature.t)
          (c: t)
        : Term.t * Signature.t * t * int list
      =
      assert (Explicits.count explicits
              <= Signature.count_explicits sign);
      let rec push explicits term sign c ptr_lst =
        if Explicits.has explicits then
          let term, sign, c =
            push_implicits
              (Signature.count_first_implicits sign)
              term sign c
          in
          let arg_tp, sign = Signature.pop_safe sign in
          let appl, explicits = Explicits.pop explicits in
          let cnt = count c in
          push
            explicits
            (Term.( Appl (up1 term, Variable 0, appl) ))
            sign
            (push_substitutable arg_tp c)
            (cnt :: ptr_lst)
        else
          term, sign, c, ptr_lst
      in
      let term, sign =
        let n_up = count c - Signature.base_context_size sign in
        assert (0 <= n_up);
        Term.up n_up term,
        Signature.up n_up sign
      in
      push explicits term sign c []



    let count_first_implicits (sign: Signature.t) (c: t): int option =
      let n = Signature.count_first_implicits sign in
      if n = 0 then
        match substitute (Signature.typ sign) c with
        | Term.Variable i when is_placeholder i c ->
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
      let req_sign = Signature.to_context_size (count c) req_sign
      in
      let term, act_sign, c =
        match
          count_first_implicits req_sign c,
          count_first_implicits act_sign c
        with
        | Some n_req, Some n_act ->
            push_implicits (n_act - n_req) term act_sign c
        | _, _ ->
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
      let cnt = count c in
      assert (cnt = Signature.context_size act_sign);
      assert (cnt = Signature.context_size req_sign);
      let rec uni act req n c =
        match Signature.pop act, Signature.pop req with
        | Some (act_arg, act), Some (req_arg, req) ->
          Option.(
            unify act_arg false req_arg c >>= fun c ->
            uni act req (n + 1) (push_bound "_" act_arg c)
          )
        | _ ->
          (* One or both signatures has no more arguments. *)
          Option.map
            (remove_last n)
            (unify (Signature.typ req) true (Signature.typ act) c)
      in
      uni act_sign req_sign 0 c

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
  | Not_yet_implemented of range * string


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


    let pop_top (c: t): t =
      {c with stack =
        match c.stack with
        | [] ->
            assert false (* Illegal call! *)
        | _ :: rest ->
            rest}


    let count (c: t): int =
      GSub.count c.gamma


    let make (gamma: GSub.t): t =
      {gamma =
         GSub.(gamma
               |> push_substitutable (Term.Sort (Term.Sort.Any 2))
               |> push_substitutable (Term.Variable 0));
       stack = [GSub.count gamma + 1]}


    let unify_candidate
          (bc: t)
          (term: Term.t)      (* Valid in the same context as [act_sign] *)
          (act_sign: Signature.t)
          (explicits: Explicits.t)
        : t option
      =
      (* before: stack = ptr rest
                 ptr without substitution

         after:  stack =  arg1 ... argn ptr rest
                 ptr substituted *)
      let ptr = top bc
      in
      let req_sign = GSub.(signature bc.gamma (type_at_level ptr bc.gamma))
      in
      let term, act_sign, ptrs_rev, gsub =
        GSub.push_argument_placeholders
          explicits
          term
          act_sign
          req_sign
          bc.gamma
      in
      let open Option in
      let open GSub in
      let req_sign = Signature.to_context_size (count gsub) req_sign in
      unify_signatures act_sign req_sign gsub >>= fun gsub ->
      Some
        {gamma =
           add_substitution_at_level ptr term gsub;
         stack =
           List.rev_append ptrs_rev bc.stack}


    let start_typed_term (bc: t): t =
      (* A typed term has the form [exp_inner: tp]. First we need a placeholder
      for the type, because the type is the first expression to be analyzed.

      before: stack = exp: ?, ...       -- exp is the placeholder for the
                                        -- whole expression
      after:  stack = tp: Any(1), exp: ?, ...

      *)
      {gamma =
        GSub.push_substitutable Term.(Sort (Sort.Any 1)) bc.gamma;
       stack =
        (count bc) :: bc.stack}


    let variable_of_level (level: int) (bc: t): Term.t =
      GSub.variable_of_level level bc.gamma
    let _ = variable_of_level


    let unify_typed_term (bc: t): t option =
      (* The type part of the typed expression [exp_inner: tp] has been built
      and stored in the top placeholder.

      before: stack = tp: Any(1), exp: ?, ...

      - unify the type stored in the top placeholder with the type of exp.

      - create a new placeholder of the inner expression.
      *)
      match bc.stack with
      | tp_ptr :: exp_ptr :: _ ->
          Option.map
            (fun gsub ->
              let open GSub in
              let exp_inner_ptr = count gsub in
              let gsub =
                push_substitutable
                  (substitution_at_level_safe tp_ptr gsub)
                  gsub
              in
              let tp = substitution_at_level_safe tp_ptr gsub in
              let exp = Term.(Typed (Variable 0, tp)) in
              let gsub =
                add_substitution_at_level exp_ptr exp gsub
              in
              {gamma = gsub; stack = exp_inner_ptr :: bc.stack})
            GSub.(
              unify
                (type_at_level exp_ptr bc.gamma)
                true
                (variable_of_level tp_ptr bc.gamma)
                bc.gamma
            )
      | _ ->
          assert false (* Cannot happen, there are at least two pointers on the
          stack. *)


    let end_typed_term (bc: t): t =
      (* typed term [exp_inner: tp]

         before: stack = exp_inner tp exp  ...
         after   stack = exp ...
       *)
      pop_top (pop_top bc)


    let substitution_in_base (level:int) (bc: t): Term.t option =
      (* At [level] there must be a substitutable which has a substitution.
         Transform the substitution to the base context or return [None],
         if it still contains other placeholders. *)
      GSub.(
        match substitution_at_level level bc.gamma with
        | None ->
          assert false (* Illegal call, [level] does not have a
                          substitution. *)
        | Some term ->
          to_base term bc.gamma
      )
  end (* Required *)





module Build_context =
  struct
    module Name_map = Context.Name_map
    module Result = Monad.Result (struct type t = problem end)

    type t = {
        names: Name_map.t;
        base:  Gamma.t;
        reqs:  Required.t list;
      }

    let make (c:Context.t): t =
      {names = Context.name_map c;
       base  = Context.gamma c;
       reqs  = [Required.make (GSub.make (Context.gamma c))]}



    let pop_top (c: t): t =
      {c with reqs = List.map Required.pop_top c.reqs}


    let required_types (c: t): typ list =
      List.map
        (fun req ->
          GSub.(
            let gsub = Required.base req in
            substitute (Required.top_type req) gsub,
            base gsub)
        )
        c.reqs


    let unify_base_candidates
          (range: range)
          (candidates: (Term.t * Signature.t) list)
          (explicits: Explicits.t)
          (c: t)
        : (t, problem) result
      =
      let reqs =
        List.(
          c.reqs >>= fun req ->
          let uni = Required.unify_candidate req in
          candidates >>= fun (term, act_sign) ->
          Option.to_list (uni term act_sign explicits)
        )
      in
      if reqs = [] then
        Error
          (None_conforms
             (range,
              Explicits.count explicits,
              required_types c,
              List.map
                (fun (_,sign) -> Signature.typ sign, c.base)
                candidates))
      else
        Ok {c with reqs}




    let check_base_terms
          (range: range)
          (terms: Term.t list) (* all valid in the base context *)
          (explicits: Explicits.t)
          (c: t)
        : (t, problem) result
      =
      assert (terms <> []);
      let gam = GSub.make c.base
      in
      let candidates =
        List.map_and_filter
          (fun t ->
            let s  = GSub.(signature gam (type_of_term t gam)) in
            if Signature.count_explicits s
              < Explicits.count explicits
            then
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
          (Not_enough_args (range, Explicits.count explicits, tps))
      else
        unify_base_candidates range candidates explicits c


    let build_proposition
      (range: range)
      (explicits: Explicits.t)
      (c: t)
      : (t, problem) result
      =
      check_base_terms
        range
        [Term.proposition]
        explicits
        c


    let build_any
      (range: range)
      (explicits: Explicits.t)
      (c: t)
      : (t, problem) result
      =
      check_base_terms
        range
        [Term.any]
        explicits
        c


    let build_name
      (range: range)
      (name: string)
      (explicits: Explicits.t)
      (c: t)
      : (t, problem) result
      =
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
           explicits
           c


    let build_number
      (range: range)
      (str: string)
      (explicits: Explicits.t)
      (c: t)
      : (t, problem) result
      =
      match Term.number_values str with
      | [] ->
         Error (Overflow range)
      | terms ->
         check_base_terms
           range
           terms
           explicits
           c


    let build_string
      (range: range)
      (str: string)
      (explicits: Explicits.t)
      (c: t)
      : (t, problem) result
      =
      check_base_terms
        range
        [Term.string str]
        explicits
        c


    let build_char
      (range: range)
      (code: int)
      (explicits: Explicits.t)
      (c: t)
      : (t, problem) result
      =
      check_base_terms
        range
        [Term.char code]
        explicits
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


    let rec build0
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
         build_proposition range explicits c

      | Any ->
         build_any range explicits c

      | Identifier name | Operator (name, _) ->
         build_name range name explicits c

      | Number str ->
         build_number range str explicits c

      | Char code ->
         build_char range code explicits c

      | String str ->
         build_string range str explicits c

      | Typed (inner, tp) ->
          (* Error (Not_yet_implemented (range, "<Typed term>"))*)
         Result.(
           map
             end_typed_term
             (return (start_typed_term c)
              >>= build0 tp Explicits.empty
              >>= unify_typed_term
              >>= build0 inner Explicits.empty)
         )

      | Application (f, args) ->
         assert (args <> []);
         let module Fold = List.Monadic_fold (Result) in
         Result.(
           build0
             f
             (Explicits.make args)
             c
           >>= Fold.fold_left
                 (fun (arg,_) c ->
                   map
                     pop_top
                     (build0 arg Explicits.empty c))
                 args
         )

      | Function (_, _, _) ->
          Error (Not_yet_implemented (range, "<Function term>"))


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
                substitution_in_base cnt0 req >>= fun tp ->
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
      Result.( build0 exp Explicits.empty (make c)
               >>= to_base_context )
  end (* Build_context *)













let build
      (exp:Parser.Expression.t)
      (c:Context.t)
    : ((Term.t * Term.typ) list, problem) result
  =
  Build_context.build exp c

module Print  (P:Pretty_printer.SIG) =
  struct
    module PP = Term_printer.Pretty (Gamma) (P)

    let typ ((tp,gamma): typ): P.t =
      PP.print tp gamma

    let required_type = typ
    let candidate_type = typ
  end

