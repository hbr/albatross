open Fmlib
open Common


module Parser     = Parser_lang
module Expression = Ast.Expression
module Position   = Character_parser.Position


type pos = Position.t

type range = pos * pos

module Located =
  Character_parser.Located



(* The explicitly given actual arguments of a function call. *)
module Explicits: sig
    type t

    val empty: t
    val make: (Expression.t * Expression.argument_type) list -> t

    val count: t -> int
    val has: t -> bool
    val pop: t -> Term.appl * t
end
=
struct
    type t = {
      args: (Expression.t * Expression.argument_type) list;
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
          if not (Local.is_placeholder local) then
          assert (Local.is_placeholder local);
          Option.map
            (fun (t, n) ->
              assert (n <= cnt);
              Term.up (cnt - n) t)
            (Local.optional_value local)
        )


    let substitution_at_level_unsafe (level: int) (gsub: t): Term.t =
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
      (* [unify t u c] unifies the term [t] with the term [u] and generate
         substitutions such that [t] and [u] with the substitutions applied are
         equivalent terms or [t] is a supertype of [u]. Return a new context
         containing new substitutions if the terms are unifiable, otherwise
         return [None]. *)
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
      assert (Explicits.count explicits
              <= Signature.count_explicits act_sign);
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


    let top_of_stack (stack: int list): int =
        match stack with
        | [] ->
            assert false (* Illegal call! *)
        | top :: _ ->
            top


    let pop_stack (stack: int list): int * int list =
        match stack with
        | [] ->
            assert false (* Illegal call! *)
        | hd :: tl ->
            hd, tl

    let pop_n_stack (n: int) (stack: int list): int list * int list =
        let rec pop_n n stack result =
            if n = 0 then
                result, stack
            else
                let top, stack = pop_stack stack in
                pop_n (n - 1) stack (top :: result)
        in
        pop_n n stack []



    let top (c: t): int =
        top_of_stack c.stack


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


    let string_of_term (term: Term.t) (bc: t): string =
        GSub.string_of_term term bc.gamma
    let _ = string_of_term



    let required_type (bc: t): Term.typ =
        GSub.substitute (top_type bc) bc.gamma



    let required_signature (bc: t): Signature.t =
        GSub.signature bc.gamma (required_type bc)



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
      assert (Explicits.count explicits
              <= Signature.count_explicits act_sign);
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


    let build_candidate
        (term: Term.t) (explicits: Explicits.t) (bc: t): t option
        =
        let act_sign =
            GSub.(signature bc.gamma (type_of_term term bc.gamma))
        in
        if Signature.count_explicits act_sign
            < Explicits.count explicits
        then
            None
        else
            unify_candidate bc term act_sign explicits



    let push_type (universe: int) (bc: t): t =
      {gamma =
        GSub.push_substitutable Term.(Sort (Sort.Any universe)) bc.gamma;
       stack =
        (count bc) :: bc.stack}


    let push_term (idx: int) (bc: t): t =
      {gamma =
        GSub.push_substitutable Term.(Variable idx) bc.gamma;
       stack =
        (count bc) :: bc.stack}


    let push_term_last (bc: t): t =
        let level = top bc in
        let idx = GSub.index_of_level level bc.gamma in
        push_term idx bc



    let push_bound (name: string) (bc: t): t =
      {bc with
        gamma =
          GSub.push_bound name Term.(Variable 0) bc.gamma}


    let variable_of_level (level: int) (bc: t): Term.t =
      GSub.variable_of_level level bc.gamma

    let _ = variable_of_level



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


    let has_nontrivial_substitution (level: int) (bc: t): bool =
        match GSub.substitution_at_level level bc.gamma with
        | None ->
            false
        | Some (Variable i) when level <= GSub.level_of_index i bc.gamma ->
            false
        | _ ->
            true



    let find_untyped_argument (nargs: int) (bc: t): int option =
    (* stack = rt argn ... arg1
    *)
        let check i level =
            if has_nontrivial_substitution level bc then
                None
            else
                Some (nargs - i - 1)
        in
        let rec find i  stack =
            if i = nargs then
                None
            else
                match stack with
                | [] ->
                    assert false (* cannot happen *)
                | level :: rest ->
                    match find (i + 1) rest with
                    | None ->
                        if 0 <= i then
                            check i level
                        else
                            None
                    | res ->
                        res
        in
        find (-1) bc.stack



    let placeholder_into
        (level: int)
        (nb: int)
        (base_level: int)
        (level_to_bound: int option array)
        (bc: t)
        : Term.t
        =
        (* return the content of the placeholder at [level] transformed into a
        context with [nb] bound variables.

        [level_to_bound.(i)] returns the number of the bound variable which is
        encountered at level [base_level + i].

        Precondition: There is a placeholder at [level] with a substitution.
        *)
        let term = GSub.substitution_at_level_unsafe level bc.gamma
        and len = Array.length level_to_bound
        in
        Term.(substitute
            (fun i ->
                let level = GSub.level_of_index i bc.gamma in
                if level < base_level || base_level + len <= level then
                   Variable (i + nb)
                else
                    match level_to_bound.(level - base_level) with
                    | None ->
                        assert false (* There is no bound variable at [level] *)
                    | Some arg_number ->
                        assert (arg_number < nb);
                        Variable (bruijn_convert arg_number nb))
            term)


    let make_level_to_bound
        (nb: int)
        (stack: int list)
        : int * int option array * int list * int list
        =
        assert (nb > 0);
        let arg_type_levels, stack =
            pop_n_stack nb stack
        in
        let base_level = top_of_stack arg_type_levels
        in
        let level_to_bound =
            let rec make level arg_no arg_type_levels level_to_bound =
                match arg_type_levels with
                | [] ->
                    level_to_bound
                | hd :: tail ->
                    assert (arg_no < nb);
                    assert (level <= hd);
                    make
                        (hd + 2)
                        (arg_no + 1)
                        tail
                        Array.(
                            fill (hd + 1 - level) None level_to_bound
                            |> push (Some (arg_no)))
            in
            make base_level 0 arg_type_levels [||]
        in
        base_level, level_to_bound, arg_type_levels, stack




    let make_bound (level: int) (bc: t): Term.t * t =
        GSub.variable_of_bound level bc.gamma,
        bc



    let make_typed_term (bc: t): Term.t * t =
        (*  make the term [Typed (exp_inner, typ)]

            start: stack = exp_inner typ ...

            end:   stack = ...
        *)
        match bc.stack with
        | exp_ptr :: typ_ptr :: stack ->
            let open GSub in
            let exp = substitution_at_level_unsafe exp_ptr bc.gamma
            and typ = substitution_at_level_unsafe typ_ptr bc.gamma
            in
            Term.Typed (exp, typ),
            {bc with stack}
        | _  ->
            assert false (* cannot happen, there are at least 2 pointers on the
            stack. *)



    let make_function_type
        (args: Expression.formal_argument list)
        (bc: t)
        : Term.typ * t
        =
        (* make the term [all (x: A) (y: B) ... : RT]

           where stack = RT Z ... B A ...

           and   gamma = ..., A:Any1, x:A, ..., B:Any1, y:B, ..., RT:Any1, ...

           and remove the placeholders from the stack
        *)
        let nb = List.length args in
        let rt_level, stack = pop_stack bc.stack in
        let a_level, level_to_bound, arg_levels, stack =
            make_level_to_bound nb stack
        in
        let tp =
            let rec make arg_no arg_levels args =
                assert (arg_no <= nb);
                if arg_no = nb then
                    placeholder_into rt_level nb a_level level_to_bound bc
                else
                    match arg_levels, args with
                    | level :: arg_levels, (name, atp) :: args ->
                        let info =
                            let name = Located.value name in
                            match atp with
                            | None ->
                                Term.Pi_info.untyped name
                            | Some _ ->
                                if name = "_" then
                                    Term.Pi_info.arrow
                                else
                                    Term.Pi_info.typed name
                        in
                        let rt = make (arg_no + 1) arg_levels args
                        in
                        let arg_tp =
                            placeholder_into
                                level arg_no a_level level_to_bound bc
                        in
                        Term.Pi (arg_tp, rt, info)
                    | _, _ ->
                        assert false (* cannot happen: nb > 0 *)
            in
            make 0 arg_levels args
        in
        tp, {bc with stack}



    let end_compound
        (make: t -> Term.t * t)
        (explicits: Explicits.t)
        (bc: t)
        : t option
        =
        let tp, bc = make bc in
        build_candidate tp explicits bc
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
  | No_candidate  of range * int * (required_type * candidate_type) list
  | Unused_bound of range
  | Cannot_infer_bound of range
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
        [BuildC.(empty gsub |> push_type 2 |> push_term 0)];
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



let end_compound
    (range: range)
    (make: BuildC.t -> Term.t * BuildC.t)
    (explicits: Explicits.t)
    (builder: t)
    : (t,problem) result
    =
    let bcs =
        List.map_and_filter
            (BuildC.end_compound make explicits)
            builder.bcs
    in
    if bcs = [] then
        let lst =
            List.map
                (fun bc ->
                    let term, bc = make bc in
                    let typ = GSub.type_of_term term bc.gamma in
                    let gamma = GSub.base (BuildC.base bc) in
                    (BuildC.required_type bc, gamma),
                    (typ, gamma))
                builder.bcs
        in
        Error (No_candidate (range, Explicits.count explicits, lst))
    else
        Ok {builder with bcs}




let build_bound
    (range: range)
    (name: string)
    (level: int)
    (explicits: Explicits.t)
    (builder: t)
    : (t, problem) result
    =
    Result.(
        end_compound range (BuildC.make_bound level) explicits builder
        >>= fun builder ->
        Ok {builder with
            bounds = Bounds.use name builder.bounds}
    )



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
    (* Add a new placeholder for a new term to be constructed whose type is the
    last constructed expression. *)
  map BuildC.push_term_last


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



let build_term
    (exp: Expression.t)
    (buildf: build_function)
    (builder: t)
    : (t, problem) result
    =
    (* Build the term for [exp] whose type is the last built expression. *)
    push_term builder
    |> buildf exp Explicits.empty



let build_formal_argument
    (buildf: build_function)
    ((name,tp): string Located.t * Expression.t option)
    (builder: t)
    : (t, problem) result
    =
    Result.map
        (push_bound (Located.value name) (tp = None))
        (build_optional_type tp buildf builder)


let build_formal_arguments
  (args: (string Located.t * Expression.t option) list)
  (buildf: build_function)
  (builder: t)
  : (t, problem) result
  =
  List_fold.fold_left
    (build_formal_argument buildf)
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


let check_formal_argument_types
    (args: (string Located.t * Expression.t option) list)
    (builder: t)
    : (t, problem) result
    =
    let nargs = List.length args in
    let find_untyped =
        BuildC.find_untyped_argument nargs
    in
    let bcs =
        List.filter
            (fun bc ->
                match find_untyped bc with
                | None ->
                    true
                | Some _ ->
                    false)
            builder.bcs
    in
    if bcs = [] then
        match builder.bcs with
        | [] ->
            assert false (* cannot happen *)
        | bc :: _ ->
            match find_untyped bc with
            | None ->
                assert false (* cannot happen *)
            | Some i ->
                let str, _ = List.nth_strict i args in
                Error (Cannot_infer_bound (Located.range str))
    else
        Ok builder



let end_function_type (* Missing: Use [end_compound] *)
    (range: range)
    (args: Expression.formal_argument list)
    (explicits: Explicits.t)
    (builder: t)
    : (t, problem) result
    =
    end_compound range
        (BuildC.make_function_type args)
        explicits
        builder



let split_formal_arguments
    (args: Expression.formal_argument list)
    (explicits: Explicits.t)
    : Expression.formal_argument list * Expression.formal_argument list
    =
    let rec split n args1 args2 =
        if n = 0 then
            List.rev args1, args2
        else
            match args2 with
            | [] ->
                List.rev args1, args2
            | arg :: args2 ->
                split (n - 1) (arg :: args1) args2
    in
    split (Explicits.count explicits) [] args



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
        Result.(
            build_type tp build0 c
            >>= build_term inner build0
            >>= end_compound range BuildC.make_typed_term explicits)

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
          >>= check_formal_argument_types formal_args
          >>= end_function_type range formal_args explicits

    | Function (formal_args, result_tp, exp_inner) ->
        let fargs1, fargs2 = split_formal_arguments formal_args explicits
        in
        let open Result
        in
        build_formal_arguments fargs1 build0 c
        >>= fun _ -> assert false
        >>= build_optional_type result_tp build0
        >>= build_term exp_inner build0
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
        Pretty_printer.run 0 200 200
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
    match build_expression "all a b: a = b" with
    | Error (Cannot_infer_bound _) ->
        true
    | _ ->
        false



let%test _ =
    match build_expression "all a (b:Int): a = b" with
    | Ok ([term, typ]) ->
        string_of_term_type term typ
        = "(all a (b: Int): a = b): Proposition"
    | _ ->
        false



let%test _ =
    match build_expression "Int -> all (A:Any): A" with
    | Ok ([term, typ]) ->
        string_of_term_type term typ
        = "Int -> (all (A: Any): A): Any(1)"
    | _ ->
        false
