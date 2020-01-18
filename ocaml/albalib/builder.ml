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

(* Placeholders
   ------------

   - Terms and subterms
   - Types of bound variables and the toplevel expression
   - Implicit arguments (inferable type variables and proof arguments)

    We start with

        Gamma, E: Any 2, e: E


   All placeholders for terms and subterms are guaranteed to get a substitution.
   Typed bound variables are guaranteed to get a substitution. The types of
   annotated terms are guaranteed to get a substitution.



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
module Expression = Ast.Expression
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
    module Local =
      struct
        type t =
          | Bound
          | Placeholder of (Term.t * int) option

        let bound =
          Bound
        let placeholder =
          Placeholder None
        let is_placeholder l =
          l <> Bound
        let optional_value = function
          | Placeholder v ->
              v
          | _ ->
              assert false (* Illegal call! *)
        let put term = function
          | Placeholder None ->
              Placeholder (Some term)
          | _ ->
              assert false (* Illegal call! *)
        let map f = function
          | Placeholder (Some term) ->
              Placeholder (Some (f term))
          | loc ->
              loc
      end

    type t = {base: Gamma.t;
              locals: Local.t array;
              bounds: int array;
              }

    let make (base: Gamma.t): t =
      {base; locals = [||]; bounds = [||]}


    let base (c:t): Gamma.t = c.base

    let count (c:t) = Gamma.count c.base


    let count_locals (c:t): int =
      Array.length c.locals


    let is_placeholder (idx: int) (gsub: t): bool =
      let nlocs = count_locals gsub in
      idx < nlocs
      && Local.is_placeholder gsub.locals.(Term.bruijn_convert idx nlocs)


    let base_count (c:t): int =
      count c - count_locals c


    let index_of_level (i:int) (c:t): int =
      Term.bruijn_convert i (count c)


    let level_of_index (i:int) (c:t): int =
      Term.bruijn_convert i (count c)


    let variable_of_level (level: int) (gsub: t): Term.t =
      Term.Variable (index_of_level level gsub)


    let variable_of_bound (level: int) (gsub: t): Term.t =
      let cnt0 = base_count gsub in
      assert (cnt0 <= level);
      variable_of_level gsub.bounds.(level - cnt0) gsub


    let type_of_term (t: Term.t) (c: t): Term.typ =
      Gamma.type_of_term t c.base


    let type_at_level (i: int) (c:t): Term.typ =
      Gamma.type_at_level i c.base


    let string_of_term (t: Term.t) (c: t): string =
      let module P = Term_printer.String_print (Gamma) in
      P.string_of_term t c.base

    let _ = string_of_term


    let push_substitutable (typ: Term.typ) (c:t): t =
      let name = "<" ^ string_of_int (count_locals c) ^ ">" in
      {c with
        base =
          Gamma.push_local name typ c.base;
        locals =
          Array.push Local.placeholder c.locals}


    let push_bound (name: string) (tp: Term.typ) (gsub: t): t =
      { base   = Gamma.push_local name tp gsub.base;
        locals = Array.push Local.bound gsub.locals;
        bounds = Array.push (count gsub) gsub.bounds}



    let has_substitution_at_level (level:int) (gsub: t): bool =
      let lsub = level - base_count gsub in
      assert (0 <= lsub);
      match gsub.locals.(lsub) with
      | Bound ->
          assert false (* Illegal call! *)
      | Placeholder sub ->
          sub <> None


    let has_substitution (idx: int) (c: t): bool =
      assert (is_placeholder idx c);
      has_substitution_at_level (level_of_index idx c) c


    let add_substitution_at_level (level:int) (t:Term.t) (c:t): t =
      (* [add_substitution_at_level i t c]. Substitute the variable at level
         [i] with the term [t] in the context [c].

         Precondition: It has to be a substitutable at level [i] which does
         not yet have any substitution.  *)
      let cnt = count c
      and cnt0 = base_count c
      in
      let idx = Term.bruijn_convert level cnt
      and lsub = level - cnt0
      in
      assert (is_placeholder idx c);
      assert (not (has_substitution_at_level level c));
      assert (0 <= lsub);
      let locals =
        Array.mapi
          (fun i local ->
            if i = lsub then
              Local.put (t,cnt) local
            else
              Local.map
                (fun (ti, n) ->
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
                local
          )
          c.locals
      in
      {c with locals}


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
        ( let local = c.locals.(level - cnt0) in
          assert (Local.is_placeholder local);
          Option.map
            (fun (t, n) ->
              assert (n <= cnt);
              Term.up (cnt - n) t)
            (Local.optional_value local)
        )


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


    let substitution (idx: int) (gsub:t): Term.t option =
      (* in the current context *)
      let n_locs = Array.length gsub.locals
      and cnt = count gsub
      in
      if idx < n_locs then
        Option.map
          (fun (t,n) ->
            assert (n <= cnt);
            Term.up (cnt - n) t)
          (Local.optional_value
             gsub.locals.(Term.bruijn_convert idx n_locs))
      else
        Some (Variable idx)


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
        let t = Gamma.key_normal t c.base
        and u = Gamma.key_normal u c.base
        in
        match t, u with
        | Sort s1, Sort s2
          when (not is_super && s1 = s2)
                || (is_super && Sort.is_super s1 s2)
          ->
           Some c

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


    let is_valid_signature (sign: Signature.t) (gsub: t): bool =
      Signature.context_size sign = count gsub


    let update_signature (sign: Signature.t) (gsub: t): Signature.t =
      let cnt = count gsub in
      assert (Signature.context_size sign <= cnt);
      Signature.to_context_size cnt sign


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
          (term: Term.t)        (* valid in the context of [sign] *)
          (sign: Signature.t)   (* might come from a lower context *)
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
        let n_up = count c - Signature.context_size sign in
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
          (term: Term.t)          (* valid in the context of [act_sign] *)
          (act_sign: Signature.t) (* might come from a lower context *)
          (req_sign: Signature.t)
          (c: t)
        : Term.t * Signature.t * int list * t
      (* The returned term is valid in the returned context *)
      =
      let term, act_sign, c, ptr_array =
        push_explicits explicits term act_sign c
      in
      let req_sign = update_signature req_sign c
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
      let cnt = count c in
      let cnt0 = base_count c in
      assert (cnt0 + n <= cnt);
      { base =
          Gamma.remove_last n c.base;
        locals =
          Array.remove_last n c.locals;
        bounds =
          let bsize = Array.find (fun i -> cnt0 + n <= i) c.bounds in
          Array.sub c.bounds 0 bsize
        }


    let unify_signatures
          (act_sign: Signature.t)
          (req_sign: Signature.t) (* might come from a lower context *)
          (c: t): t option
      =
      assert (is_valid_signature act_sign c);
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
            (remove_last n) (* only bound variables have been introduced. *)
            (unify (Signature.typ req) true (Signature.typ act) c)
      in
      uni act_sign (update_signature req_sign c) 0 c

  end (* GSub *)











module BuildC =
  (* Build context:
      A context for unification and a stack of pointers pointing to placeholders
      for terms.
  *)
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


    let empty (gamma: GSub.t): t =
      {gamma; stack = []}


    let required_signature (bc: t): Signature.t =
      GSub.(
        signature
          bc.gamma
          (type_at_level (top bc) bc.gamma))


    let unify_candidate
          (bc: t)
          (term: Term.t)          (* Valid in the same context as [act_sign] *)
          (act_sign: Signature.t) (* might come from a lower context *)
          (explicits: Explicits.t)
        : t option
      =
      (* before: stack = ptr rest
                 ptr without substitution

         after:  stack =  arg1 ... argn ptr rest
                 ptr substituted
                 placeholders added for all explicit and implicit arguments *)
      let ptr = top bc in
      let req_sign = required_signature bc in
      let open GSub in
      let term, act_sign, ptrs_rev, gsub =
        push_argument_placeholders
          explicits
          term
          act_sign
          req_sign
          bc.gamma
      in
      Option.map
        (fun gsub ->
          {gamma =
             add_substitution_at_level ptr term gsub;
           stack =
             List.rev_append ptrs_rev bc.stack})
        (unify_signatures act_sign req_sign gsub )


    let build_bound (level: int) (explicits: Explicits.t) (bc: t): t option =
      (* before: stack = ptr rest
                 ptr without substitution

         after:  stack =  arg1 ... argn ptr rest
                 ptr substituted *)
      let open GSub
      in
      let term = variable_of_bound level bc.gamma in
      let typ  = type_of_term term bc.gamma in
      let act_sign = signature bc.gamma typ in
      unify_candidate bc term act_sign explicits


    let push_type (universe: int) (bc: t): t =
      {gamma =
        GSub.push_substitutable Term.(Sort (Sort.Any universe)) bc.gamma;
       stack =
        (count bc) :: bc.stack}


    let push_term (bc: t): t =
      {gamma =
        GSub.push_substitutable Term.(Variable 0) bc.gamma;
       stack =
        (count bc) :: bc.stack}


    let push_bound (name: string) (bc: t): t =
      {bc with
        gamma =
          GSub.push_bound name Term.(Variable 0) bc.gamma}


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
  end (* BuildC *)











(* -------------------------------------------------------------------

   Builder

   ------------------------------------------------------------------- *)

type typ = Term.typ * Gamma.t

type required_type = typ
type candidate_type = typ


type problem =
  | Overflow of range
  | No_name of range
  | Not_enough_args of range * int * candidate_type list
  | None_conforms of range * int * required_type list * candidate_type list
  | Unused_bound of range
  | Not_yet_implemented of range * string



module Name_map = Context.Name_map
module Result = Monad.Result (struct type t = problem end)

module Bounds =
    struct
        type t = {
            map: bool list String_map.t; (* usage flag for each bound var *)
        }

        let empty: t =
            {map = String_map.empty}

        let push(name: string) (bnds: t): t =
            {map =
                match String_map.maybe_find name bnds.map with
                | None ->
                    String_map.add name [false] bnds.map
                | Some lst ->
                    String_map.add name (false :: lst) bnds.map}

        let use (name: string) (bnds: t): t =
            {map =
                match String_map.maybe_find name bnds.map with
                | None ->
                    bnds.map
                | Some [] ->
                    assert false (* Illegal call! *)
                | Some (_ :: rest) ->
                    String_map.add name (true :: rest) bnds.map}

        let pop (name: string) (bnds: t): bool * t =
            match String_map.find name bnds.map with
            | [] ->
                assert false (* Illegal call! *)
            | [flag] ->
                flag,
                {map = String_map.remove name bnds.map}
            | flag :: flags ->
                flag,
                {map = String_map.add name flags bnds.map}
    end



type t = {
    names: Name_map.t;
    base:  Gamma.t;
    bcs :  BuildC.t list;
    bounds: Bounds.t;
  }


module List_fold = List.Monadic_fold (Result)


type build_function =
  Expression.t -> Explicits.t -> t -> (t, problem) result




let make (c:Context.t): t =
      {names = Context.name_map c;
       base  = Context.gamma c;
       bounds = Bounds.empty;
       bcs =
        let gsub = GSub.make (Context.gamma c) in
        [BuildC.(empty gsub |> push_type 2 |> push_term)];
       }


let map (f: BuildC.t -> BuildC.t) (builder: t): t =
  {builder with bcs = List.map f builder.bcs}

let pop_top (builder: t): t =
  map BuildC.pop_top builder


let required_types (c: t): typ list =
  List.map
    (fun req ->
      GSub.(
        let gsub = BuildC.base req in
        substitute (BuildC.top_type req) gsub,
        base gsub)
    )
    c.bcs


let unify_base_candidates
      (range: range)
      (candidates: (Term.t * Signature.t) list)
      (explicits: Explicits.t)
      (c: t)
    : (t, problem) result
  =
  let bcs  =
    List.(
      c.bcs  >>= fun bc ->
      let uni = BuildC.unify_candidate bc in
      candidates >>= fun (term, act_sign) ->
      Option.to_list (uni term act_sign explicits)
    )
  in
  if bcs  = [] then
    Error
      (None_conforms
         (range,
          Explicits.count explicits,
          required_types c,
          List.map
            (fun (_,sign) -> Signature.typ sign, c.base)
            candidates))
  else
    Ok {c with bcs }




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



let build_bound
  (_: range)
  (name: string)
  (level: int)
  (explicits: Explicits.t)
  (builder: t)
  : (t, problem) result
  =
  (*
  ----------------------------------------------------------------------
  MISSING: Check, if term can be applied to sufficient arguments like in
  [check_base_terms]!!!!
  ----------------------------------------------------------------------*)
  let bcs =
    List.map_and_filter
      (BuildC.build_bound level explicits)
      builder.bcs
  in
  if bcs = [] then
    assert false
  else
    Ok {builder with
        bcs;
        bounds = Bounds.use name builder.bounds}



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
      build_bound range name i explicits c

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


let push_type (universe: int) (builder: t): t =
  map (BuildC.push_type universe) builder


let push_term: t -> t =
  map BuildC.push_term


let push_bound (name: string) (untyped: bool) (builder: t): t =
  {builder with
    names =
      Name_map.add_local name builder.names;
    bcs =
      List.map (BuildC.push_bound name) builder.bcs;
    bounds =
        if untyped then
            Bounds.push name builder.bounds
        else
            builder.bounds}


let unify_typed_term (c: t): (t, problem) result =
  match
    List.map_and_filter BuildC.unify_typed_term c.bcs
  with
  | [] ->
     assert false (* nyi error message *)
  | bcs  ->
     Ok {c with bcs }


let end_typed_term (builder: t): t =
  map (fun bc -> BuildC.(pop_top (pop_top bc))) builder



let build_type
  (tp: Expression.t)
  (buildf: build_function)
  (builder: t)
  : (t, problem) result
  =
  buildf tp Explicits.empty (push_type 1 builder)



let build_optional_type
  (tp: Expression.t option)
  (buildf: build_function)
  (builder: t)
  : (t, problem) result
  =
  match tp with
  | None ->
      Ok (push_type 1 builder)
  | Some tp ->
      build_type tp buildf builder


let build_formal_arguments
  (args: (string Located.t * Expression.t option) list)
  (buildf: build_function)
  (builder: t)
  : (t, problem) result
  =
  List_fold.fold_left
    (fun (name, tp) builder ->
      Result.map
        (push_bound (Located.value name) (tp = None))
        (build_optional_type tp buildf builder))
    args
    builder



let check_formal_arguments_usage
    (args: (string Located.t * Expression.t option) list)
    (builder: t)
    : (t, problem) result
    =
    List_fold.fold_right
        (fun (name, tp) builder ->
            if tp <> None then
                Ok builder
            else
                let flag, bounds =
                    Bounds.pop (Located.value name) builder.bounds in
                if flag then
                    Ok {builder with bounds}
                else
                    Error (Unused_bound (Located.range name))
        )
        args
        builder



let rec build0
          (exp:Ast.Expression.t)
          (explicits: Explicits.t)
          (c: t)
        : (t, problem) result
  =
  (* Build the expression [exp] according to the type of the top
     placeholder.

     After successful build, the expression is stored in the top
     placeholder.  The stack of placeholders is not modified, only the top
     one has got a substitution. *)
  let open Ast.Expression
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
         (return (push_type 1 c)
          >>= build0 tp Explicits.empty
          >>= unify_typed_term
          >>= build0 inner Explicits.empty)
     )

  | Application (f, args) ->
     assert (args <> []);
     Result.(
       build0
         f
         (Explicits.make args)
         c
       >>= List_fold.fold_left
             (fun (arg,_) c ->
               map
                 pop_top
                 (build0 arg Explicits.empty c))
             args
     )

  | Product (formal_args, result_tp) ->
        let open Result in
        build_formal_arguments formal_args build0 c
        >>= build_type result_tp build0
        >>= check_formal_arguments_usage formal_args
        >>= fun _ ->
        (* We have to verify that all types depend only on placeholders before
        the building of the product.

        *)
        Error (Not_yet_implemented (range, "<complete product term>"))

  | Function (formal_args, result_tp, exp_inner) ->
      let open Result
      in
      build_formal_arguments formal_args build0 c
      >>= build_optional_type result_tp build0
      >>= fun b -> Ok (push_term b)
      >>= build0 exp_inner Explicits.empty
      >>= fun _ ->
      Error (Not_yet_implemented (range, "<complete function term>"))



let to_base_context
      (c: t)
    : ((Term.t * Term.typ) list, problem) result
  =
  assert (c.bcs  <> []);
  let cnt0 = Gamma.count c.base
  in
  let lst =
    List.map_and_filter
      (fun req ->
        assert (cnt0 + 2 <= BuildC.count req);
        Option.(
          BuildC.(
            substitution_in_base (cnt0 + 1) req >>= fun t ->
            substitution_in_base cnt0 req >>= fun tp ->
            Some (t, tp))))
      c.bcs
  in
  if lst = [] then
    assert false (* nyi *)
  else
    Ok lst


let build
      (exp: Ast.Expression.t)
      (c: Context.t)
    : ((Term.t * Term.typ) list, problem) result
  =
  Result.( build0 exp Explicits.empty (make c)
           >>= to_base_context )











module Print  (P:Pretty_printer.SIG) =
  struct
    module PP = Term_printer.Pretty (Gamma) (P)

    let typ ((tp,gamma): typ): P.t =
      PP.print tp gamma

    let required_type = typ
    let candidate_type = typ
  end


















(* ----------------------------------------------------------------------- *)
(* Unit Test *)
(* ----------------------------------------------------------------------- *)



module Pretty_printer = Pretty_printer.Pretty (String_printer)

module Term_print = Context.Pretty (Pretty_printer)

module Expression_parser = Parser_lang.Make (Expression)



let standard_context: Context.t =
    Context.standard ()



let string_of_term_type (term: Term.t) (typ: Term.t): string
    =
    String_printer.run (
        Pretty_printer.run 0 80 80
            (Term_print.print (Term.Typed (term,typ)) standard_context))



let build_expression
    (str: string)
    : ((Term.t * Term.typ) list, problem) result
    =
    let open Expression_parser in
    let p = run (expression ()) str in
    assert (has_ended p);
    assert (has_succeeded p);
    build Option.(value (result p)) standard_context





let%test _ =
    match build_expression "1:Int" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "(1: Int): Int"
    | _ ->
        false



let%test _ =
    match build_expression "identity" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "identity: all (A: Any): A -> A"
    | _ ->
        false



let%test _ =
    match build_expression "identity 'a'" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "identity 'a': Character"
    | _ ->
        false



let%test _ =
    match build_expression "'a'= 'b'  " with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "'a' = 'b': Proposition"
    | _ ->
        false



let%test _ =
    match build_expression "abc" with
    | Error (No_name _) ->
        true
    | _ ->
        false



let%test _ =
    match build_expression "(+) 1 2 3" with
    | Error (Not_enough_args _) ->
        true
    | _ ->
        false



let%test _ =
    match build_expression "all (a:Int) b: a = b" with
    | Error (Not_yet_implemented _) ->
        true
    | _ ->
        false
