module Make (Io: Fmlib.Browser.IO) =
struct
    let model: unit = ()

    let view (): unit Fmlib.Html.t =
        let open Fmlib.Html in
        let open Attribute in
        div
            []
            [text "Hello world";
             textarea
                [attribute "placeholder" "Enter expression";
                 property  "value" "Sample";
                 attribute "cols" "10";
                 attribute "rows" "3"]
                [];
             pre
                [   style "color" "red";
                    style "background-color" "lightgray";
                    style "width" "50%"
                ]
                [text "preformatted"];
             button
                [style "color" "blue"]
                [text "evaluate"];
             button
                [on "click" (Handler.Normal ())]
                [text "typecheck"];
             button [attribute "class" "myclass"] [text "clear"];
            ]

    let update () () = ()

    let run (): unit =
        Io.sandbox model view update
end


let _ =
    let module Web = Make (Fmlib_node.Web.Io) in
    Web.run ()
