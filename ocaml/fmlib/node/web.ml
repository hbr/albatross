open Fmlib
open Js_of_ocaml

module Io =
struct
    type ('model,'msg) t = {
        window:   Dom_html.window Js.t;
        document: Dom_html.document Js.t;
        model:    'model;
        view:     'model -> 'msg Html.t;
    }

    let make (model: 'a) (view: 'model -> 'msg Html.t): ('model,'msg) t =
        let window = Dom_html.window in
        let document = window##.document in
        { window; document; model; view }


    let remove_children (node: Dom_html.element Js.t): unit =
        let rec remove () =
            match Js.Opt.to_option (node##.firstChild) with
            | None ->
                ()
            | Some child ->
                Dom.removeChild node child;
                remove ()
        in
        remove ()


    let make_html
        (html: 'msg Html.t)
        (doc: Dom_html.document Js.t)
        : Dom_html.element Js.t
        =
        let open Html in
        let rec make html =
            match html with
            | Text text ->
                (
                    Js.Unsafe.coerce (doc##createTextNode (Js.string text))
                    : Dom_html.element Js.t
                )
            | Node (tag, _ , children) ->
                List.fold_left
                    (fun node child ->
                        Dom.appendChild node (make child);
                        node
                    )
                    (doc##createElement (Js.string tag))
                    children
        in
        make html


    let sandbox
        (model: 'model)
        (view: 'model -> 'msg Html.t)
        (_: 'msg -> 'model -> 'model)
        : unit
        =
        Dom_html.window##.onload :=
            Dom_html.handler
                (fun _ ->
                    let state = make model view in
                    remove_children (state.document##.body);
                    Dom.appendChild
                        state.document##.body
                        (make_html (view model) state.document);
                    Js._false
                )
end
