open Fmlib
open Common

module Alba_web (Browser: Html2.BROWSER) =
struct
    module Vdom = Html2.Vdom (Browser)


    let model: string =
        ""

    let view (model: string): string Vdom.t =
        let open Vdom in
        let open Attribute in
        div
            []
            [input
                [   attribute "placeholder" "Text to reverse"
                ;   property "value" model
                ;   on "input" Browser.Decoder.string
                ]
                []
            ;div [] [text (String.reverse model)]
            ]

    let update (message: string) (_: string): string =
        message


    let run (): unit =
        let module Browser = Browser.Make (Vdom) in
        Browser.sandbox model view update
end



let _ =
    let module Browser = Alba_web (Fmlib_js.Browser) in
    Browser.run ()
