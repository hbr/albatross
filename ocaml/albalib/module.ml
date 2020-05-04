open Fmlib


module Parser = Parser_lang.Make (Unit)



module Compiler =
struct
    type t = {
        parser: Parser.parser;
    }


    let needs_more (_: t): bool =
        assert false

    let put_character (_: t) (_: char): t =
        assert false

    let put_end (_: t): t =
        assert false


    let make _: t =
        { parser = Parser.(make (source_file ()))}
end





module Make (Io: Io.SIG) =
struct
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



    let run _: unit Io.t =
        let module Reader = Io.File.Read (Compiler) in
        Io.(
            Reader.read File.stdin (Compiler.make ())
            >>= fun io_result ->
            match io_result with
            | Error (_, error) ->
                let module Error = Fmlib.Io.Error in
                Pretty.(run (string (Error.message error) <+> cut))
            | Ok _ ->
                assert false
        )
end
