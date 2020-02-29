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
  | Incomplete_type of (Term.t list * Term.t * Term.typ * Gamma.t) list
  | Unused_bound
  | Cannot_infer_bound
  | Not_yet_implemented of string


type problem = range * problem_description


module Name_map = Context.Name_map
module Result = Monad.Result (struct type t = problem end)
module List_fold = List.Monadic_fold (Result)
module Interval_monadic = Interval.Monadic (Result)

module Build_context = Build_context2


type t = {
    names: Name_map.t;
    base:  Gamma.t;
    bcs:   Build_context.t list;
}



let count_base (builder: t): int =
    Gamma.count builder.base




let push_bound (name: string) (builder: t): t =
    {builder with
        names = Name_map.add_local name builder.names}



let make (c: Context.t): t =
    {
        names = Context.name_map c;
        base  = Context.gamma c;
        bcs   = [Build_context.make (Context.gamma c)]
    }



let base_candidates
    (_: range)
    (candidates: Term.t list)
    (nargs: int)
    (builder: t)
    : (t, problem) result
    =
    let bcs =
        List.(
            builder.bcs >>= fun bc ->
            candidates  >>= fun term ->
            Option.to_list (Build_context.base_candidate term nargs bc))
    in
    if bcs = [] then
        assert false
    else
        Ok {builder with bcs}



let map_bcs_list (f: Build_context.t -> Build_context.t) (builder: t): t =
    {builder with bcs = List.map f builder.bcs}



let map_bcs0
    (f: Build_context.t -> ('a, 'b) result)
    (g: 'b list -> problem)
    (builder: t)
    : ('a list, problem) result
    =
    let lst, errors =
        List.fold_left
            (fun (lst, errors)  bc ->
                match f bc with
                | Ok a ->
                    a :: lst, errors
                | Error problem ->
                    lst, problem :: errors)
            ([], [])
            builder.bcs
    in
    if lst <> [] then
        Ok lst
    else
        Error (g errors)





let map_bcs
    (f: Build_context.t -> (Build_context.t, 'a) result)
    (g: 'a list -> problem)
    (builder: t)
    : (t, problem) result
    =
    Result.map
        (fun bcs -> {builder with bcs})
        (map_bcs0 f g builder)






let rec build0
    (exp: Expression.t)
    (nargs: int)
    (builder: t)
    : (t, problem) result
    =
    let open Expression in
    let range = Located.range exp in
    match
        Located.value exp
    with
    | Number str ->
        base_candidates range (Term.number_values str) nargs builder

    | Char code ->
        base_candidates range [Term.char code] nargs builder

    | String str ->
        base_candidates range [Term.string str] nargs builder

    | Proposition ->
        base_candidates range [Term.proposition] nargs builder

    | Any ->
        base_candidates range [Term.any] nargs builder

    | Identifier name | Operator (name, _) ->
        let cnt_base = count_base builder in
        (
            match Name_map.find name builder.names with
            | [] ->
                Error (range, No_name)

            | [level] when cnt_base <= level ->
                map_bcs
                    (Build_context.bound (level - cnt_base) nargs)
                    (fun _ -> assert false)
                    builder

            | lst ->
                base_candidates
                    range
                    (List.map
                        (fun level -> Gamma.term_at_level level builder.base)
                        lst)
                    nargs
                    builder
        )

    | Typed (exp, tp) ->
        let open Result in
        (map_bcs_list Build_context.Typed.start builder
        |> build0 tp 0)
        >>= fun builder ->
        (map_bcs_list Build_context.Typed.expression builder
        |> build0 exp 0)
        >>=
        map_bcs
            (Build_context.Typed.end_ nargs)
            (fun _ -> assert false)

    | Product (fargs, res) ->
        let open Result in
        List_fold.fold_left
            (fun (name, arg_tp) builder ->
                let name_str = Located.value name in
                let next typed builder =
                    map_bcs_list
                        (Build_context.Product.next name_str typed)
                        builder
                    |> push_bound (Located.value name)
                in
                match arg_tp with
                | None ->
                    Ok (next false builder)
                | Some tp ->
                    map
                        (next true)
                        (build0 tp 0 builder))
            fargs
            (map_bcs_list Build_context.Product.start builder)
        >>= build0 res 0
        >>= map_bcs
                (Build_context.Product.end_ (List.length fargs))
                (fun _ -> assert false)


    | Application (_, _) ->
        assert false


    | _ ->
        assert false




let build
      (exp: Ast.Expression.t)
      (c: Context.t)
    : ((Term.t * Term.typ) list, problem) result
    =
    let open Result
    in
    build0 exp 0 (make c)
    >>=
    map_bcs0
        Build_context.final
        (fun lst -> Located.range exp, Incomplete_type lst)








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
    match build_expression "Proposition" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "Proposition: Any"
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
    match build_expression "Int" with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "Int: Any"
    | _ ->
        false



let%test _ =
    match build_expression "abc" with
    | Error (_, No_name) ->
        true
    | _ ->
        false



let%test _ =
    match build_expression "(|>)" with
    | Ok [term,typ] ->
        string_of_term_type term typ
        = "(|>): all (A: Any) (a: A) (B: Any) (f: A -> B): B"
    | _ ->
        false


let%test _ =
    match build_expression "Int -> all (B: Any): (Int -> B) -> B" with
    | Ok [term,typ] ->
        string_of_term_type term typ
        = "Int -> (all (B: Any): (Int -> B) -> B): Any(1)"
    | Error (problem) ->
        Printf.printf "%s\n" (string_of_error problem);
        false
    | _ ->
        false


let%test _ =
    match build_expression "'a' : Character : Any" with
    | Ok [term, typ] ->
        string_of_term_type term typ
        = "('a': Character: Any): Character: Any"
    | _ ->
        false


let%test _ =
    let tp_str = "Int -> (all (B: Any): (Int -> B) -> B)"
    in
    match build_expression ("(|>): " ^ tp_str)  with
    | Ok [term, typ] ->
        string_of_term_type term typ
        =
        "((|>): " ^ tp_str ^ "): "  ^ tp_str
    | _ ->
        false

(*
let%test _ =
    match build_expression "all a b: a = b" with
    | Error (_, Cannot_infer_bound) ->
        true
    | _ ->
        false
*)
