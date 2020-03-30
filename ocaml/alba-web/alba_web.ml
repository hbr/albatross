module Make (Io: Fmlib.Browser.IO) =
struct
    let model: unit = ()

    let view (): unit Fmlib.Html.t =
        let open Fmlib.Html in
        div
            []
            [text "Hello world";
             textarea [] [];
             pre [] [text "preformatted"]]

    let update () () = ()

    let run (): unit =
        Io.sandbox model view update
end


let _ =
    let module Web = Make (Fmlib_node.Web.Io) in
    Web.run ()
