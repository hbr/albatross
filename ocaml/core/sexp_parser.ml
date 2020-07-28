open Fmlib
open Module_types
open Common


module Located = Character_parser.Located

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

    type term_tag =
      | Application
      | Lambda
      | Pi


    let term_tags: term_tag String_map.t =
        String_map.(empty
                    |> add "app" Application
                    |> add "pi" Pi
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


    let left_paren_ws: unit t =
        char '('
        |. whitespace


    let right_paren_ws: unit t =
        char ')'
        |. whitespace


    let operator_characters: string = "+-^*|/=~<>"


    let is_operator_character (c: char): bool =
        String.has (fun d -> c = d) 0 operator_characters


    let operator: string located t =
        located (word
                     is_operator_character
                     is_operator_character
                     "operator character")
        |. whitespace


    let number: string located t =
        located (word Char.is_digit Char.is_digit "digit")
        |. whitespace





    let atom: Builder.t t =
        map
            (fun (range,name) -> Builder.Construct.identifier range name)
            name_ws



    let some_tag (expecting: string) (map: 'a String_map.t): 'a t =
        (backtrackable
            (raw_name >>= fun tag ->
             match String_map.maybe_find tag map with
             | None ->
                 unexpected expecting
             | Some tag ->
                 return tag)
            expecting)
        |. whitespace



    let term_tag: term_tag t =
        some_tag "<term tag>" term_tags



    let rec expression _: Builder.t t =
        atom
        <|>
        compound ()


    and compound _: Builder.t t =
        (return (fun _ -> assert false))
        |. left_paren_ws
        |= (term_tag >>=
            function
            | Application ->
                application ()
            | Pi ->
                assert false
            | Lambda ->
                assert false)
        |. right_paren_ws

    and application _: Builder.t t =
        (return (fun _ _ -> assert false))
        |= expression ()
        |= one_or_more (expression ())
end




(* --------------------------------------------------------------------- *)
(* Unit tests *)
(* --------------------------------------------------------------------- *)


module Expression =
struct
    type t = Builder.t
end

module Expression_parser  = Make (Expression)


let build_expression
    (src: string)
    (c: Welltyped.context)
    : (Welltyped.judgement, Builder.problem) result =
    let open Expression_parser in
    let p = run (expression ()) c src in
    assert (has_ended p);
    assert (has_succeeded p);
    Builder.make_term
        c
        (Option.value (result p))


let is_term_ok (src: string): bool =
    match
        build_expression src Welltyped.empty
    with
    | Ok _ ->
        true
    | Error _ ->
        false


(* Some simple expressions *)
let%test _ =
    is_term_ok "Any"


let%test _ =
    is_term_ok "Proposition"

(*
let%test _ =
    is_term_ok "(pi ((A Any) (a A)) A"
*)


(* Adding builtin types and functions *)
(*
let%test _ =
    match
        add_builtin "(builtin Int () Any)" Welltyped.empty
    with
    | Ok _ ->
        true
    | Error _ ->
        false
*)
