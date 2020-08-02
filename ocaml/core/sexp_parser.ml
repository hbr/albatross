open Fmlib
open Module_types
open Common


module Located = Character_parser.Located

type range = Located.range

module Info =
struct type t = Located.range end

module Builder = Welltyped.Builder (Info)


module Make (Final: ANY) =
struct
    module State =
        struct
            type t = Welltyped.context
        end

    module Semantic =
        struct
            type t = Located.range * Type_error.t
        end

    type 'a located = Located.range * 'a

    include Character_parser.Normal (State) (Final) (Semantic) (Unit)

    type p = parser

    type term_tag =
      | Application
      | Lambda
      | Pi


    let term_tags: term_tag String_map.t =
        String_map.(empty
                    |> add "app" Application
                    |> add "all" Pi
                    |> add "lambda" Lambda)


    type declaration_tag =
      | Builtin
      | Definition
      | Class


    let declaration_tags: declaration_tag String_map.t =
        String_map.(
            empty
            |> add "builtin" Builtin
            |> add "def"     Definition
            |> add "class"   Class
      )
    let _ = declaration_tags



    let located (p: 'a t): 'a located t =
        map
            (fun res ->
                 let v = Located.value res
                 and range = Located.range res
                 in
                 range, v)
            (located p)


    let whitespace_char: char t =
        expect
            (fun c -> c = ' ' || c = '\n' || c = '\t')
            "space, newline or tab"


    let whitespace: int t =
        skip_zero_or_more whitespace_char


    let raw_name: string t =
        word
            Char.is_letter
            (fun c -> Char.is_letter c || Char.is_digit c || c = '_')
            "identifier"


    let name: string located t =
        located raw_name


    let name_ws: string located t =
        name |. whitespace

    let char_ws (c: char): unit t =
        char c |. whitespace

    let left_paren_ws: unit t =
        char_ws '('


    let right_paren_ws: unit t =
        char_ws ')'


    let parenthesized_located (p: unit -> 'a t): 'a located t =
        (return
             (fun ((p1,_),_) v ((_,p2),_) ->
                  (p1,p2), v))
        |= located (char '(')
        |. whitespace
        |== p
        |= located (char ')')
    let _ = parenthesized_located


    let parenthesized (p: unit -> 'a t): 'a t =
        (return identity)
        |. left_paren_ws
        |== p
        |. right_paren_ws


    let operator_characters: string = "+-^*|/=~<>"


    let is_operator_character (c: char): bool =
        String.has (fun d -> c = d) 0 operator_characters


    let operator: string located t =
        located (word
                     is_operator_character
                     is_operator_character
                     "operator character")
        |. whitespace
    let _ = operator


    let number: string located t =
        located (word Char.is_digit Char.is_digit "digit")
        |. whitespace
    let _ = number





    let atom: Builder.tl t =
        map
            (fun (range,name) _ -> Builder.identifier range name)
            name_ws



    let some_tag (expecting: string) (map: 'a String_map.t): 'a located t =
        (backtrackable
            (name_ws >>= fun (range, tag) ->
             match String_map.maybe_find tag map with
             | None ->
                 unexpected expecting
             | Some tag ->
                 return (range,tag))
            expecting)
        |. whitespace


    let parenthesized_tagged
            (expecting: string)
            (map: 'a String_map.t)
            (p: 'a located -> 'b t)
        : 'b t
        =
        parenthesized
            (fun _ ->
                 some_tag expecting map
                 >>=
                 p)




    let rec expression _: Builder.tl t =
        atom
        <|>
        compound ()

    and compound _: Builder.tl t =
        parenthesized_tagged
            "<term tag>"
            term_tags
            (fun (range, tag) ->
                match tag with
                | Application ->
                    application range
                | Pi ->
                    pi range
                | Lambda ->
                    assert false)

    and application (_: Located.range): Builder.tl t =
        (return (fun _ _ -> assert false))
        |= expression ()
        |= one_or_more (expression ())

    and pi (range: Located.range): Builder.tl t =
        return
             (fun fargs res ->
                  List.fold_right
                      (fun (name,arg_typ) res_typ _ ->
                           Builder.pi
                               range name arg_typ res_typ)
                      fargs
                      res)
        |== formal_arguments
        |. char_ws ':'
        |= result_type ()

    and result_type _: Builder.tl t =
        expression ()

    and formal_arguments _: Builder.formal_argument list t =
        zero_or_more (parenthesized formal_argument)

    and formal_argument _: Builder.formal_argument t =
        (return (fun name typ -> name, typ))
        |= name_ws
        |. char_ws ':'
        |= expression ()

    and signature _: Builder.signature t =
        return (fun fargs res -> fargs, res)
        |== formal_arguments
        |. char_ws ':'
        |== expression



    let judgement: Welltyped.judgement t
        =
        expression () >>= fun expr ->
        get_state >>= fun context ->
        match
            (Builder.make_term context (expr ()))
        with
        | Ok jm ->
            return jm
        | Error error ->
            fail error


    let declaration _: unit t =
        parenthesized_tagged
            "<declaration tag>"
            declaration_tags
            (fun (_, tag) ->
                match tag with
                | Builtin ->
                    get_state >>= fun context ->
                    name_ws >>= fun name ->
                    signature () >>= fun sign ->
                    (
                        match Builder.make_builtin context name sign with
                        | Ok context ->
                            put_state context
                        | Error error ->
                            fail error
                    )
                | Definition ->
                    assert false
                | Class ->
                    assert false)


    let declarations _: unit t =
        map
            (fun n ->
                 Printf.printf "%d declarations parsed\n" n;
                 ())
            (skip_zero_or_more
                 (declaration ()))


    let run_string
            (p: Final.t t) (c: Welltyped.context) (src: string)
        : p
        =
        run (p |. expect_end) c src
end




(* --------------------------------------------------------------------- *)
(* Unit tests *)
(* --------------------------------------------------------------------- *)


module Expression_parser =
    Make (struct type t = Builder.tl end)


module Context_parser =
    Make (Unit)


let build_expression
        (src: string)
        (c: Welltyped.context)
    : (Welltyped.judgement, Builder.problem) result =
    let open Expression_parser in
    let p = run_string (expression ()) c src in
    assert (has_ended p);
    assert (has_succeeded p);
    Builder.make_term
        c
        (Option.value (result p) ())



let build_expression_empty
        (src: string)
    : (Welltyped.judgement, Builder.problem) result
    =
    build_expression src Welltyped.empty


let build_context
        (src: string) (c: Welltyped.context)
    : Welltyped.context
    =
    let open Context_parser in
    let p = run_string (declarations ()) c src in
    assert (has_ended p);
    assert (has_succeeded p);
    state p



let is_term_ok (src: string): bool =
    let module PP = Pretty_printer.Pretty (String_printer) in
    let to_string (pp: PP.t): string =
        String_printer.run (PP.run 0 70 70 pp)
    in
    match
        build_expression src Welltyped.empty
    with
    | Ok jm ->
        let module Print = Welltyped.Print (PP) in
        Printf.printf "%s\n" (to_string (Print.judgement jm));
        true
    | Error (range, error) ->
        let module Print = Type_error.Print (PP) in
        let module Source_print = Position.Print (PP) in
        Printf.printf "%s\n\n%s\n"
            (String_printer.run
                 (PP.run 0 70 70
                      (Source_print.print_source src range)))
            (String_printer.run
                 (PP.run 0 70 70 (Print.print error)));
        false


(* Some simple expressions *)
let%test _ =
    is_term_ok "Any"


let%test _ =
    is_term_ok "Proposition"



let%test _ =
    is_term_ok "(all (A:Any) (a:A): A)"



let%test _ =
    is_term_ok "(all (a:Proposition): Proposition)"


let%test _ =
    is_term_ok "(all (a:Proposition)(x:a): a)"


let%test _ =
    is_term_ok "(all (A:Any) (x:A) (a:Proposition): a)"




let%test _ =
    match
        build_expression_empty "(all (A:Any) (a:A): a)"
    with
    | Error (_, Type_error.Not_a_type) ->
        true
    | _ ->
        false


let%test _ =
    match
        build_expression_empty "(all (A:Any) (a:A) (x:a): A)"
    with
    | Error (_, Type_error.Not_a_type) ->
        true
    | _ ->
        false




(*
(* Filling the context *)
let%test _ =
    let _ = build_context
            "(builtin Int: Any)"
            Welltyped.empty in
    true*)
