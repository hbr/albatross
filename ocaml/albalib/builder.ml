open Fmlib
open Common


module Parser = Parser_lang
module Expression = Parser.Expression

type pos = Character_parser.Position.t

module Position =
  Character_parser.Position

module Located =
  Character_parser.Located



type required =
  Gamma.t     (* Context with placeholders with required types *)

  * int list  (* Positions of the placeholders for not yet built arguments. *)


type actual =
  Gamma.t     (* Context with placeholders for the arguments (there might be
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
      | Overflow of pos * string
      | No_name of pos * string
      | Not_enough_args of pos * int * int * actual list
      | None_conforms of pos * int * required list * actual list
  end


module Result = Monad.Result (Problem)


module Print  (P:Pretty_printer.SIG) =
  struct
    let required ((c,lst):required): P.t
      (* Print the required type of the next argument (type of the topmost
         placeholder). *)
      =
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


let find_name (name:string) (pos:Position.t) (c:Context.t): int list Result.t =
  match Context.find_name name c with
  | [] ->
     Error (Problem.No_name (pos,name))
  | lst ->
     Ok lst



let extract_args
      (nargs:int)                      (* Name is applied to [nargs] arguments
                                          *)
      (mode: Term.appl)                (* Mode of the application *)
      (base:Context.t)
      (pos:Position.t)                 (* Position of the name *)
      (len:int)                        (* String length of the name *)
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
             gamma,
             (Interval.fold
                []
                (fun i lst -> cnt + nargs - 1 - i :: lst)
                0 nargs),
             Term.(
               application
                 (Variable Gamma.(index_of_level i gamma))
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
              (pos, len, nargs,
               List.map
                 (fun i ->
                   (Context.gamma base),
                   [],
                   Gamma.term_at_level i (Context.gamma base))
                 lst
       ))
  | lst ->
     Ok lst


let unify
      (pos:Position.t)
      (len:int)
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
       and cnt = Gamma.count gamma_req
       in
       assert (cnt0 <= cnt);
       assert (cnt0 <= Gamma.count gamma_act);
       let nargs = Gamma.count gamma_act - cnt0 in
       let gamma, t =
         Gamma.push_signature
           gamma_act nargs t
           gamma_req
       and req_lst =
         (List.map (fun i -> i + (cnt - cnt0)) act_args)
         @ req_lst
       in
       match
         Gamma.(unify
                  (Term.Variable (index_of_level i_req gamma))
                  t
                  gamma)
       with
       | None ->
          []
       | Some gamma1 ->
          assert Gamma.(count gamma = count gamma1);
          [gamma1, req_lst]
    )
  with
  | [] ->
     Error (Problem.None_conforms (pos, len, reqs, actuals))
  | lst ->
     Ok lst


let term_of_name
      (name: string)
      (pos: Position.t)
      (nargs: int)
      (mode: Term.appl)
      (base: Context.t)
      (reqs: required list)
    : (required list, Problem.t) result
  =
  let len = String.length name in
  Result.(
    find_name name pos base
    >>= extract_args nargs mode base pos len
    >>= unify pos len base reqs
  )


let term_of_number
      (number:string)
      (pos:Position.t)
      (base:Context.t)
      (reqs: required list)
    : (required list, Problem.t) result
  =
  let lst =
    Term.Value.number_values number
  in
  match lst with
  | [] ->
     Error (Problem.Overflow (pos,number))
  | _ ->
     unify
       pos (String.length number) base reqs
       (List.map
          (fun v ->
            match v with
            | Term.Value.Int _ ->
               (Context.gamma base),
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
  let pos = Located.start expr in
  let len =
    Position.column (Located.end_ expr) - Position.column pos
  in
  match
    Located.value expr
  with
  | Any ->
     unify
       pos (String.length "Any") base reqs
       [Context.gamma base, [], Term.any]

  | Identifier name | Operator (name,_) ->
     term_of_name name pos nargs mode base reqs

  | Number str ->
     assert (nargs = 0);
     term_of_number str pos base reqs

  | Char code ->
     assert (nargs = 0);
     unify pos len base reqs [Context.gamma base, [], (Term.char code)]

  | String str ->
     assert (nargs = 0);
     unify pos len base reqs [Context.gamma base, [], (Term.string str)]

  | Binary (e1, op, e2) ->
     let name, _ = Located.value op
     and pos  = Located.start op in
     Result.(
       term_of_name name pos 2 Term.Binary base reqs
       >>= fun reqs ->
       build0 base reqs 0 Term.Normal e1
       >>= fun reqs ->
       build0 base reqs 0 Term.Normal e2
     )

  | Function (args, exp) ->
     assert false

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
        (fun (gamma, req_lst) ->
          assert (req_lst = []);
          assert (cnt + 2 <= Gamma.count gamma);
          assert (Gamma.is_all_substituted gamma);
          Gamma.(substitution_at_level (cnt + 1) gamma,
                 substitution_at_level cnt gamma)
        )
        lst
    )
    (build0
       c
       [Gamma.(Context.gamma c
               |> push_substitutable (Term.Sort (Term.Sort.Any 2))
               |> push_substitutable (Term.Variable 0))
       , [cnt + 1]]
       0
       Term.Normal
       expr)
