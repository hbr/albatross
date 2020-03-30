module Make (Io: Fmlib.Browser.IO) =
struct
    let model: unit = ()

    let view (): unit Fmlib.Html.t =
        let open Fmlib.Html in
        text "Hello world"

    let update () () = ()

    let run (): unit =
        Io.sandbox model view update
end


let _ =
    let module Web = Make (Fmlib_node.Web.Io) in
    Web.run ()
