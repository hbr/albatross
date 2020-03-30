open Fmlib
open Js_of_ocaml

module Io =
struct
    let sandbox
        (_: 'model)
        (_: 'model -> 'a Html.t)
        (_: 'a -> 'model -> 'model)
        : unit
        =
        let window = Dom_html.window in
        let document = window##.document in
        window##.onload :=
            Dom_html.handler
                (fun _ ->
                    Dom.appendChild
                        document##.body
                        (document##createTextNode
                            (Js.string "Test 3"));
                    Js._false
                )
end
