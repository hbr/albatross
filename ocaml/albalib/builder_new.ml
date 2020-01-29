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


type problem =
  | Overflow of range
  | No_name of range
  | Not_enough_args of range * candidate_type list
  | None_conforms of range * required_type list * candidate_type list
  | No_candidate  of range * (required_type * candidate_type) list
  | Unused_bound of range
  | Cannot_infer_bound of range
  | Not_yet_implemented of range * string



module Name_map = Context.Name_map
module Result = Monad.Result (struct type t = problem end)
module List_fold = List.Monadic_fold (Result)






module Bounds =
    (* This module keeps track of the usage status of bound variables. *)
struct
    type t = {
        map: bool list String_map.t; (* usage flag for each bound var *)
    }

    let empty: t =
        {map = String_map.empty}

    (*let push(name: string) (bnds: t): t =
        {map =
            match String_map.maybe_find name bnds.map with
            | None ->
                String_map.add name [false] bnds.map
            | Some lst ->
                String_map.add name (false :: lst) bnds.map}*)

    (*let use (name: string) (bnds: t): t =
        {map =
            match String_map.maybe_find name bnds.map with
            | None ->
                bnds.map
            | Some [] ->
                assert false (* Illegal call! *)
            | Some (_ :: rest) ->
                String_map.add name (true :: rest) bnds.map}*)

    (*let pop (name: string) (bnds: t): bool * t =
        match String_map.find name bnds.map with
        | [] ->
            assert false (* Illegal call! *)
        | [flag] ->
            flag,
            {map = String_map.remove name bnds.map}
        | flag :: flags ->
            flag,
            {map = String_map.add name flags bnds.map}*)
end (* Bounds *)













type t = {
    names:  Name_map.t;
    base:   Gamma.t;
    bcs :   Build_context.t list;
    bounds: Bounds.t;
  }


let make (c: Context.t): t =
    {
        names = Context.name_map c;
        base  = Context.gamma c;
        bounds = Bounds.empty;
        bcs = [Build_context.make (Context.gamma c)]
     }




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
            (None_conforms
                (range,
                 required_types builder,
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





let rec build0
    (exp: Expression.t)
    (builder: t)
    : (t, problem) result
    =
    let open Expression in
    let open Result in
    let range = Located.range exp
    in
    match Located.value exp with
    | Proposition ->
        base_candidates range [Term.proposition] builder

    | Any ->
        base_candidates range [Term.any] builder

    | Identifier name | Operator (name, _) ->
        (
            match Name_map.find name builder.names with
            | [] ->
                Error (No_name range)

            | [level] when Gamma.count builder.base <= level ->
                assert false (* nyi bound variables *)

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
        build0
            typ
            (map_bcs Build_context.push_type builder)
        >>= fun builder ->
        build0
            exp
            (map_bcs Build_context.push_typed builder)
        >>= fun builder ->
        map_filter_bcs
            (fun bc ->
                let term, bc = Build_context.make_typed bc in
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
                No_candidate (range, lst))
            builder

    | Application (f, args ) ->
        let pos1, pos2 = Located.range f
        in
        build0
            f
            (map_bcs Build_context.push_function builder)
        >>=
        fun builder ->
            map fst
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
                                    Not_enough_args (
                                        (pos1,pos2),
                                        built_types builder
                                    ))
                                builder
                             >>= build0 arg)
                    )
                    args
                    (builder, pos2))

    | Product (_, _) ->
        assert false (* nyi *)

    | Function (_, _, _) ->
        assert false (* nyi *)








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
        assert false (* nyi *)
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
    | Error (No_name _) ->
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



(*
let%test _ =
    match build_expression "'a'= 'b'  " with
    | Ok ([term,typ]) ->
        string_of_term_type term typ
        = "'a' = 'b': Proposition"
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
*)
