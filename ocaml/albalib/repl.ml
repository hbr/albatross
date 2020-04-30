open Fmlib
open Alba_core

module Command_parser =
    Parser_lang.Make (Parser_lang.Command)


module Make (Io: Io.SIG) =
struct

    module Cli_state =
    struct
        type t = string option

        let init: t = Some ""

        let exit: t = None

        let prompt (state: t): t =
            Option.map
                (fun str ->
                    if str = "" then
                        "> "
                    else
                        "| ")
                state

        let add (line: string) (state: t): t =
            Option.map
                (fun str ->
                    if str = "" then
                        line
                    else
                        str ^ "\n"  ^ line)
                state

        let string (state: t): string =
            match state with
            | None ->
                assert false (* Illegal call! *)
            | Some str ->
                str
    end (* Cli_state *)




    module Pretty =
    struct
        module Out =
            Fmlib.Io.Output (Io)

        include
            Pretty_printer.Pretty (Out)

        let run (pr: t): unit Io.t =
            Out.run
                Io.File.stdout
                (run 0 80 80 pr)
    end (* Pretty *)




    let parse (input: string): Command_parser.parser =
        let len = String.length input
        in
        let module P = Command_parser in
        let rec parse i p =
            let more = P.needs_more p
            in
            if i < len && more then
                parse (i + 1) (P.put_char p input.[i])
            else if more then
                P.put_end p
            else
                p
        in
        parse 0 P.(make command)


    let build_and_compute
        (input: string)
        (expression: Ast.Expression.t)
        (compute: bool)
        : Pretty.t
        =
        let std_context = Context.standard () in
        match
            Builder.build expression std_context
        with
        | Error (range, descr) ->
            let module Print = Printer.Make (Pretty) in
            let module Builder_print = Builder.Print (Pretty) in
            let open Pretty in
            Print.print_error_header "TYPE"
            <+> Print.print_source input range []
            <+> cut
            <+> Builder_print.description descr
            <+> cut

        | Ok (term, typ) ->
            let term =
                if compute then
                    Context.compute term std_context
                else
                    term
            in
            let open Pretty in
            let module P = Context.Pretty (Pretty)
            in
            cut
            <+>
            P.print Term.(Typed (term, typ)) std_context
            <+>
            cut



    let process_input (input: string): Cli_state.t Io.t =
        let continue_after action =
            Io.(action >>= fun _ -> return Cli_state.init)
        in
        let p = parse input
        in
        assert (Command_parser.has_ended p);
        match Command_parser.result p with
        | Some cmd ->
            assert (Command_parser.has_succeeded p);
            (
                match cmd with
                | Parser_lang.Command.Do_nothing ->
                    Io.return Cli_state.init

                | Parser_lang.Command.Exit ->
                    Io.return Cli_state.exit

                | Parser_lang.Command.Evaluate expression ->
                    continue_after
                        (Pretty.run
                            (build_and_compute
                                input
                                expression
                                true))

                | Parser_lang.Command.Type_check expression ->
                    continue_after
                        (Pretty.run
                            (build_and_compute
                                input
                                expression
                                false))
            )
        | None ->
            let module Printer =
                Command_parser.Error_printer (Pretty)
            in
            continue_after
                (Pretty.run
                    (Printer.print_with_source input p))



    let next (state: Cli_state.t) (line: string): Cli_state.t Io.t =
        assert (Cli_state.prompt state <> None); (* guaranteed by [cli_loop]. *)
        let state = Cli_state.add line state
        in
        let is_last (line: string): bool =
            let len = String.length line in
            len = 0
            || line.[len - 1] <> ' '
        in
        if is_last line then
            process_input (Cli_state.string state)
        else
            Io.return state


    let stop (state: Cli_state.t): Cli_state.t Io.t =
        Io.return state


    let run_cli _: unit Io.t =
        Io.(
            cli_loop
                Cli_state.init
                Cli_state.prompt
                next
                stop
            >>= fun _ ->
            return ()
        )


    module Evaluate_stdin =
    struct
        module Expression_parser =
            Parser_lang.Make (Ast.Expression)


        module Writable =
        struct
            type t = {
                can_end: bool;
                input: string;
                parser: Expression_parser.parser;
            }

            let init (): t =
                {
                    can_end =
                        false;

                    input =
                        "";

                    parser =
                        Expression_parser.(make (expression ()));
                }

            let needs_more (w: t): bool =
                Expression_parser.needs_more w.parser
                ||
                not w.can_end


            let putc (w: t) (c: char): t =
                let open Expression_parser in
                {
                    can_end =
                        c = '\n';

                    input =
                        w.input ^ Common.String.one c;

                    parser =
                        if needs_more w.parser then
                            put_char w.parser c
                        else
                            w.parser;
                }

            let putend (w: t): t =
                Printf.printf "putend\n";
                let open Expression_parser in
                { w with
                    parser =
                        if needs_more w.parser then
                            put_end w.parser
                        else
                            w.parser;
                }

            let result (w: t): string * Expression_parser.parser =
                w.input,
                w.parser
        end (* Writable *)



        let run _: unit Io.t =
            let module R = Io.File.Read (Writable) in
            let module Error = Fmlib.Io.Error in
            Io.(
                R.read File.stdin (Writable.init ())
                >>= fun io_res ->
                match io_res with
                | Error (_, error) ->
                    Pretty.(run
                        (string (Error.message error) <+> cut)
                    )
                | Ok w ->
                    let input, p = Writable.result w in
                    let open Expression_parser
                    in
                    assert (has_ended p);
                    match result p with
                    | None ->
                        let module Printer =
                            Error_printer (Pretty)
                        in
                        Pretty.run
                            (Printer.print_with_source input p)

                    | Some expression ->
                        Pretty.run
                            (build_and_compute
                                input
                                expression
                                false)
            )
    end



    let run_eval _: unit Io.t =
        Evaluate_stdin.run ()
end
