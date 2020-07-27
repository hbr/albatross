open Fmlib
open Module_types
open Common


module Located = Character_parser.Located

module Info =
struct type t = Located.range end

module Builder = Welltyped.Builder (Info)


module Make (State: ANY) (Final: ANY) =
struct
    include Character_parser.Normal (State) (Final) (Unit) (Unit)


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


    let name: string Located.t t =
        located raw_name


    let name_ws: string Located.t t =
        name |. whitespace


    let operator_characters: string = "+-^*|/=~<>"


    let is_operator_character (c: char): bool =
        String.has (fun d -> c = d) 0 operator_characters


    let operator: string Located.t t =
        located (word
                     is_operator_character
                     is_operator_character
                     "operator character")
        |. whitespace


    let number: string Located.t t =
        located (word Char.is_digit Char.is_digit "digit")
        |. whitespace





    let atom: Builder.term Builder.t t =
        map
            (fun name ->
                let name, range = Located.split name in
                Builder.Construct.identifier range name)
            name_ws




    let rec expression _: Builder.term Builder.t t =
        atom
        <|>
        compound ()

    and compound _: Builder.term Builder.t t =
        (return (fun _ -> assert false))
        |.  char '('
        |. whitespace
        |= (name_ws >>= fun name ->
            let name = Located.value name
            in
            if name = "app" then
                application ()
            else if name = "pi" then
                assert false
            else if name = "lam" then
                assert false
            else
                unexpected "wrong tag of expression"
        )
        |. char ')'
        |. whitespace

    and application _: Builder.term Builder.t t =
        (return (fun _ _ -> assert false))
        |= expression ()
        |= one_or_more (expression ())
end




(* --------------------------------------------------------------------- *)
(* Unit tests *)
(* --------------------------------------------------------------------- *)


module Expression =
struct
    type t = Builder.term Builder.t
end

module Expression_parser = Make (Unit) (Expression)

let build_expression
    (str: string)
    : (Welltyped.judgement, Builder.problem) result =
    let open Expression_parser in
    let p = run (expression ()) () str in
    assert (has_ended p);
    assert (has_succeeded p);
    Builder.make_term
        (Welltyped.empty)
        (Option.value (result p))


let%test _ =
    match build_expression "Any" with
    | Ok _ ->
        true
    | Error _ ->
        false


let%test _ =
    match build_expression "Proposition" with
    | Ok _ ->
        true
    | Error _ ->
        false
