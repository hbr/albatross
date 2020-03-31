module Make (Io: Fmlib.Browser.IO) =
struct
    let model: unit = ()

    let view (): unit Fmlib.Html.t =
        let open Fmlib.Html in
        let open Attribute in
        div
            []
            [text "Hello world";
             textarea [] [];
             pre
                [   style "color" "red";
                    style "backgroundColor" "lightgray";
                    style "width" "50%"
                ]
                [text "preformatted"];
             button [style "color" "blue"] [text "evaluate"];
             button [] [text "typecheck"];
             button [attribute "class" "myclass"] [text "clear"];
             ]

    let update () () = ()

    let run (): unit =
        Io.sandbox model view update
end


let _ =
    let module Web = Make (Fmlib_node.Web.Io) in
    Web.run ()
