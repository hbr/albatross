open Alba_core
open Ast


module Inductive_parser =
    Parser_lang.Make (
        struct
            type t = Source_entry.inductive array
        end)


module Expression_parser =
    Parser_lang.Make (Expression)


module Definition_parser =
    Parser_lang.Make (
        struct
            type t = Expression.definition
        end)




let add_definition (src: string) (c: Context.t): Context.t =
    Printf.printf "add definition \"%s\"\n" src;
    let open Definition_parser in
    let p = run (global_definition ()) src in
    assert (has_ended p);
    assert (has_succeeded p);
    match result p with
    | None ->
        assert false (* Cannot happen. *)
    | Some def ->
        match Builder.add_definition def c with
        | Error _ ->
            assert false
        | Ok c ->
            c





let add_inductive (src: string) (c: Context.t): Context.t =
    Printf.printf "add inductive \"%s\"\n" src;
    let open Inductive_parser in
    let p = run (inductive_family ()) src in
    assert (has_ended p);
    assert (has_succeeded p);
    match result p with
    | None ->
        assert false (* Cannot happen. *)
    | Some def ->
        match Builder.add_inductive def c with
        | Error _ ->
            assert false
        | Ok c ->
            c


let add_builtin
    (descr: string) (name: string) (src: string) (c: Context.t):
    Context.t
=
    Printf.printf "add builtin %s \"%s\"\n" descr src;
    let open Expression_parser in
    let p = run (expression ()) src in
    assert (has_ended p);
    assert (has_succeeded p);
    match result p with
    | None ->
        assert false (* Cannot happen. *)
    | Some exp ->
        match Build_expression.build exp c with
        | Error _ ->
            assert false
        | Ok (typ, _) ->
            Context.add_builtin_type descr name typ c






let add_logic (c: Context.t): Context.t =
    c
    |>
    add_definition
        "(=>) (a: Proposition) (b: Proposition): Proposition :=\
        \n  a -> b"
    |>
    add_inductive
        "class false: Proposition :="
    |>
    add_inductive
        "class true: Proposition := trueValid"
    |>
    add_inductive
        "class (=) (A: Any) (a: A): A -> Proposition := identical: a = a"




let add_basics (c: Context.t): Context.t =
    c
    |>
    add_definition
        "(|>) (A: Any) (a: A) (B: Any) (f: A -> B): B := f a"
    |>
    add_definition
        "(<|) (A: Any) (B: Any) (f: A -> B) (a: A): B := f a"




let add_builtins (c: Context.t): Context.t =
    c
    |>
    add_builtin "int_type" "Int" "Any"
    |>
    add_builtin "int_plus" "+" "Int -> Int -> Int"
    |>
    add_builtin "int_minus" "-" "Int -> Int -> Int"
    |>
    add_builtin "int_times" "*" "Int -> Int -> Int"
    |>
    add_builtin "string_type" "String" "Any"
    |>
    add_builtin "string_concat" "+" "String -> String -> String"
    |>
    add_builtin "character_type" "Character" "Any"





let make (): Context.t =
    Context.empty
    |>
    add_basics
    |>
    add_logic
    |>
    add_builtins



let _ = make ()
