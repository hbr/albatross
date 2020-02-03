open Fmlib
open Common


module Parser     = Parser_lang
module Expression = Ast.Expression
module Position   = Character_parser.Position


type pos = Position.t

type range = pos * pos

module Located =
  Character_parser.Located


type typ = Term.typ * Gamma.t

type required_type = typ
type candidate_type = typ


type problem_description =
  | Overflow
  | No_name
  | Not_enough_args of candidate_type list
  | None_conforms of required_type list * candidate_type list
  | No_candidate  of (required_type * candidate_type) list
  | Incomplete_type of candidate_type list
  | Unused_bound
  | Cannot_infer_bound
  | Not_yet_implemented of string


type problem = range * problem_description


module Name_map = Context.Name_map
module Result = Monad.Result (struct type t = problem end)
module List_fold = List.Monadic_fold (Result)
module Interval_monadic = Interval.Monadic (Result)


module Bounds:
sig
    type t
    val count: t -> int
    val empty: t
    val push: range -> bool -> t -> t
    val use:  int -> t -> t
    val status: int -> t -> range * bool
end
=
struct
    type t = (range * bool) array

    let count bnds =
        Array.length bnds

    let empty = [||]

    let push range typed bnds =
        Array.push (range, typed) bnds

    let use i bnds =
        let range, flag = bnds.(i) in
        if flag then
            bnds
        else
            (let bnds_new = Array.copy bnds in
             bnds_new.(i) <- range, true;
             bnds_new)

    let status i bnds =
        bnds.(i)
end













type t = {
    names:  Name_map.t;
    base:   Gamma.t;
    bcs :   Build_context.t list;
    bounds: Bounds.t;
  }


let count_base (builder: t): int =
    Gamma.count builder.base


let count_bounds (builder: t): int =
    Bounds.count builder.bounds


let make (c: Context.t): t =
    {
        names = Context.name_map c;
        base  = Context.gamma c;
        bounds = Bounds.empty;
        bcs = [Build_context.make (Context.gamma c)]
     }



let push_bound
    (name: string Located.t)
    (typed: bool)
    (builder: t)
    : t
    =
    let name_str  = Located.value name
    in
    {builder with
        names =
            Name_map.add_local name_str builder.names;
        bounds =
            Bounds.push (Located.range name) typed builder.bounds}



let required_types (builder: t): required_type list =
    List.map
        (fun bc -> Build_context.(required_type bc, base bc))
        builder.bcs



let built_types (builder: t): candidate_type list =
    List.map
        (fun bc -> Build_context.(built_type bc, base bc))
        builder.bcs



let base_candidates
    (range: range)
    (candidates: Term.t list) (* All valid in the base context. *)
    (builder: t)
    : (t, problem) result
    =
    let bcs =
        List.(
            builder.bcs >>= fun bc ->
            candidates >>= fun term ->
            Option.to_list (Build_context.base_candidate term bc)
        )
    in
    if bcs = [] then
        Error
            (range,
             None_conforms
                (required_types builder,
                 List.map
                    (fun term ->
                        Gamma.type_of_term term builder.base,
                        builder.base)
                    candidates))
    else
        Ok {builder with bcs}





let map_bcs
    (f: Build_context.t -> Build_context.t)
    (builder: t)
    : t
    =
    {builder with bcs = List.map f builder.bcs}



let map_bcs2
    (f: Build_context.t -> (Build_context.t, 'a) result)
    (g: 'a list -> problem)
    (builder: t)
    : (t, problem) result
    =
    let bcs, errors =
        List.fold_left
            (fun (bcs, errors)  bc ->
                match f bc with
                | Ok bc ->
                    bc :: bcs, errors
                | Error problem ->
                    bcs, problem :: errors)
            ([], [])
            builder.bcs
    in
    if bcs <> [] then
        Ok {builder with bcs}
    else
        Error (g errors)




let map_filter_bcs
    (f: Build_context.t -> Build_context.t option)
    (g: t -> problem)
    (builder: t)
    : (t, problem) result
    =
    let bcs =
        List.map_and_filter f builder.bcs
    in
    if bcs = [] then
        Error (g builder)
    else
        Ok {builder with bcs}




let terminate_term
    (range: range)
    (make: Build_context.t -> Term.t * Build_context.t)
    : t -> (t, problem) result
    =
    map_filter_bcs
        (fun bc ->
            let term, bc = make bc in
            Build_context.candidate term bc)
        (fun builder ->
            let lst =
                List.map
                    (fun bc ->
                        let term, bc = Build_context.make_typed bc in
                        let req      = Build_context.required_type bc in
                        let gamma    = Build_context.base bc in
                        (req, gamma),
                        (Gamma.type_of_term term gamma, gamma))
                    builder.bcs
            in
            range, No_candidate lst)





let rec build0
    (exp: Expression.t)
    (builder: t)
    : (t, problem) result
    =
    let build_type typ builder =
        build0
            typ
            (map_bcs Build_context.push_type builder)
    in
    let open Expression in
    let open Result in
    let range = Located.range exp
    in
    match
        Located.value exp
    with
    | Proposition ->
        base_candidates range [Term.proposition] builder

    | Any ->
        base_candidates range [Term.any] builder

    | Identifier name | Operator (name, _) ->
        let cnt_base = count_base builder in
        (
            match Name_map.find name builder.names with
            | [] ->
                Error (range, No_name)

            | [level] when cnt_base <= level ->
                terminate_term
                    range
                    (Build_context.make_bound level)
                    {builder with
                        bounds =
                            Bounds.use (level - cnt_base) builder.bounds}

            | lst ->
                base_candidates
                    range
                    (List.map
                        (fun level -> Gamma.term_at_level level builder.base)
                        lst)
                    builder
        )

    | Number str ->
        base_candidates range (Term.number_values str) builder

    | Char code ->
        base_candidates range [Term.char code] builder

    | String str ->
        base_candidates range [Term.string str] builder

    | Typed (exp, typ) ->
        build_type typ builder
        >>= fun builder ->
        build0
            exp
            (map_bcs Build_context.push_typed builder)
        >>= terminate_term range Build_context.make_typed

    | Application (f, args ) ->
        let pos1, pos2 = Located.range f
        in
        (* Build the function term. *)
        build0
            f
            (map_bcs Build_context.start_function_application builder)
        >>=
        (* Build all arguments and apply the function term incrementally to the
        arguments. *)
        fun builder ->
            (List_fold.fold_left
                (fun (arg,mode) (builder, pos2) ->
                    let builder =
                        map_bcs Build_context.push_implicits builder
                    in
                    map
                        (fun b ->
                            map_bcs (Build_context.apply_argument mode) b,
                            Located.end_ arg)
                        (map_filter_bcs
                            Build_context.push_argument
                            (fun builder ->
                                (pos1, pos2),
                                Not_enough_args (built_types builder))
                            builder
                         >>= build0 arg)
                )
                args
                (builder, pos2))
        >>=
        (* Complete the function application. Pop the term off the stack and
        unify its type with the required type. *)
        fun (builder, pos2) ->
        terminate_term
            (pos1,pos2)
            Build_context.pop
            builder

    | Function (fargs, res_tp, exp) ->
        List_fold.fold_left
            (fun (name, arg_tp) builder->
                match arg_tp with
                | None ->
                    Ok (map_bcs
                            Build_context.lambda_bound
                            (push_bound name false builder))
                | Some arg_tp ->
                    build_type arg_tp (push_bound name true builder)
                    >>=
                    map_bcs2
                        Build_context.lambda_bound_typed
                        (fun _ -> assert false)
            )
            fargs
            (map_bcs Build_context.start_binder builder)
        >>= fun builder ->
        (   match res_tp with
            | None ->
                Ok (map_bcs Build_context.lambda_inner builder)
            | Some res_tp ->
                build_type res_tp builder
                >>=
                map_bcs2
                    Build_context.lambda_inner_typed
                    (fun _ -> assert false)
        )
        >>=
        build0 exp
        >>= fun _ ->
        assert false

    | Product (fargs, res_tp) ->
        let nbounds0 = count_bounds builder in
        (* Build formal arguments. *)
        List_fold.fold_left
            (fun (name, arg_tp) builder ->
                let name_str = Located.value name in
                match arg_tp with
                | None ->
                    Ok (map_bcs
                            (Build_context.pi_bound name_str)
                            (push_bound name false builder))

                | Some arg_tp ->
                    map
                        (map_bcs (Build_context.pi_bound_typed name_str))
                        (build_type
                            arg_tp
                            (push_bound name true builder)))
            fargs
            (map_bcs Build_context.start_binder builder)
        >>=
        (* Build result type. *)
        build_type res_tp
        >>=
        (* Check usage of untyped formal arguments and complete type inference.*)
        fun builder ->
        let nbounds = count_bounds builder - nbounds0 in
        Interval_monadic.fold
            (fun i builder ->
                let range, used_or_typed =
                    Bounds.status i builder.bounds
                in
                (if used_or_typed then
                    Ok builder
                 else
                    Error (range, Unused_bound))
                >>=
                map_bcs2
                    (Build_context.check_bound i nbounds)
                    (fun _ -> range, Cannot_infer_bound)
            )
            0 nbounds builder
        >>=
        terminate_term range Build_context.pi_make








let build
      (exp: Ast.Expression.t)
      (c: Context.t)
    : ((Term.t * Term.typ) list, problem) result
    =
    let open Result
    in
    build0 exp (make c) >>= fun builder ->
    let lst =
        List.map_and_filter
            (fun bc ->
                let term, typ, gamma =
                    Build_context.final bc
                in
                if Gamma.(count builder.base = count gamma) then
                    Some (term, typ)
                else
                    None
                )
            builder.bcs
    in
    if lst = [] then
        Error (
            Located.range exp,
            Incomplete_type (
                List.map
                    (fun bc ->
                        let _, typ, gamma = Build_context.final bc in
                        typ, gamma)
                    builder.bcs))
    else
        Ok lst











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
let _ = string_of_term_type

let string_of_error ((_,p): problem): string =
    match p with
    | Overflow -> "overflow"
    | No_name -> "no name"
    | Not_enough_args _ -> "not enough args"
    | None_conforms _ -> "None conforms"
    | No_candidate _ -> "no candidate"
    | Incomplete_type _ -> "incomplete type"
    | Unused_bound -> "unused bound"
    | Cannot_infer_bound -> "cannot infer bound"
    | Not_yet_implemented _ -> "not yet implemented"
let _ = string_of_error

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
    match build_expression "abc" with
    | Error (_, No_name) ->
        true
    | _ ->
        false


let%test _ =
    match build_expression "Any" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "Any: Any(1)"
    | _ ->
        false



let%test _ =
    match build_expression "Proposition" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "Proposition: Any"
    | _ ->
        false



let%test _ =
    match build_expression "String" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "String: Any"
    | _ ->
        false



let%test _ =
    match build_expression "'a'" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "'a': Character"
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
    match build_expression "1:Int" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "(1: Int): Int"
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
    match build_expression "(+) 1 2 3" with
    | Error (_, Not_enough_args _) ->
        true
    | _ ->
        false




let%test _ =
    match build_expression "leibniz 'a'" with
    | Error (_, Incomplete_type _) ->
        true
    | _ ->
        false





let%test _ =
    match build_expression "all a b: 'x' = b" with
    | Error (_, Unused_bound) ->
        true
    | _ ->
        false



let%test _ =
    match build_expression "all a b: a = b" with
    | Error (_, Cannot_infer_bound) ->
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
    match build_expression "1 |> (+) 2" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "1 |> (+) 2: Int"
    | _ ->
        false




let%test _ =
    match build_expression "Int -> all (A:Any): A" with
    | Ok ([term, typ]) ->
        string_of_term_type term typ
        = "Int -> (all (A: Any): A): Any(1)"
    | _ ->
        false
